/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2025 The Stockfish developers (see AUTHORS file)

  Stockfish is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Stockfish is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include "evaluate.h"

#include <algorithm>
#include <cstdio>
#include <cassert>
#include <cmath>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <memory>
#include <sstream>
#include <tuple>

#include "nnue/network.h"
#include "nnue/nnue_misc.h"
#include "position.h"
#include "types.h"
#include "uci.h"
#include <fstream>
#include "nnue/nnue_accumulator.h"

namespace Stockfish {

// Returns a static, purely materialistic evaluation of the position from
// the point of view of the given color. It can be divided by PawnValue to get
// an approximation of the material advantage on the board in terms of pawns.
int Eval::simple_eval(const Position& pos, Color c) {
    return PawnValue * (pos.count<PAWN>(c) - pos.count<PAWN>(~c))
         + (pos.non_pawn_material(c) - pos.non_pawn_material(~c));
}

bool Eval::use_smallnet(const Position& pos) {
    int simpleEval = simple_eval(pos, pos.side_to_move());
    return std::abs(simpleEval) > 962;
}

// On Windows, we use a helper struct to hold our bidirectional process information.
#ifdef _WIN32
struct BidirectionalProcess {
    PROCESS_INFORMATION pi;
    HANDLE              hChildStd_IN_Wr;
    HANDLE              hChildStd_OUT_Rd;
};

// Helper function to create a bidirectional process.
// Returns true on success.
static bool createBidirectionalProcess(const char* cmd, BidirectionalProcess& bp) {
    SECURITY_ATTRIBUTES saAttr;
    saAttr.nLength              = sizeof(SECURITY_ATTRIBUTES);
    saAttr.bInheritHandle       = TRUE;
    saAttr.lpSecurityDescriptor = NULL;

    // Create pipe for STDOUT.
    HANDLE hChildStd_OUT_Rd = NULL;
    HANDLE hChildStd_OUT_Wr = NULL;
    if (!CreatePipe(&hChildStd_OUT_Rd, &hChildStd_OUT_Wr, &saAttr, 0))
    {
        std::cerr << "Stdout pipe creation failed\n";
        return false;
    }
    if (!SetHandleInformation(hChildStd_OUT_Rd, HANDLE_FLAG_INHERIT, 0))
    {
        std::cerr << "Stdout SetHandleInformation failed\n";
        return false;
    }

    // Create pipe for STDIN.
    HANDLE hChildStd_IN_Rd = NULL;
    HANDLE hChildStd_IN_Wr = NULL;
    if (!CreatePipe(&hChildStd_IN_Rd, &hChildStd_IN_Wr, &saAttr, 0))
    {
        std::cerr << "Stdin pipe creation failed\n";
        return false;
    }
    if (!SetHandleInformation(hChildStd_IN_Wr, HANDLE_FLAG_INHERIT, 0))
    {
        std::cerr << "Stdin SetHandleInformation failed\n";
        return false;
    }

    // Set up STARTUPINFO structure.
    STARTUPINFOA siStartInfo;
    ZeroMemory(&siStartInfo, sizeof(STARTUPINFOA));
    siStartInfo.cb         = sizeof(STARTUPINFOA);
    siStartInfo.hStdError  = hChildStd_OUT_Wr;
    siStartInfo.hStdOutput = hChildStd_OUT_Wr;
    siStartInfo.hStdInput  = hChildStd_IN_Rd;
    siStartInfo.dwFlags |= STARTF_USESTDHANDLES;

    // Create the process.
    PROCESS_INFORMATION piProcInfo;
    ZeroMemory(&piProcInfo, sizeof(PROCESS_INFORMATION));
    BOOL success = CreateProcessA(NULL,
                                  const_cast<LPSTR>(cmd),  // command line
                                  NULL,                    // process security attributes
                                  NULL,                    // primary thread security attributes
                                  TRUE,                    // handles are inherited
                                  0,                       // creation flags
                                  NULL,                    // use parent's environment
                                  NULL,                    // use parent's current directory
                                  &siStartInfo,            // STARTUPINFO pointer
                                  &piProcInfo              // receives PROCESS_INFORMATION
    );

    // Close handles that are not needed by the parent.
    CloseHandle(hChildStd_OUT_Wr);
    CloseHandle(hChildStd_IN_Rd);

    if (!success)
    {
        std::cerr << "CreateProcess failed\n";
        return false;
    }

    bp.pi               = piProcInfo;
    bp.hChildStd_IN_Wr  = hChildStd_IN_Wr;
    bp.hChildStd_OUT_Rd = hChildStd_OUT_Rd;
    return true;
}
#endif  // _WIN32

// Modified evaluation function.
Value Eval::evaluate(const Eval::NNUE::Networks&    networks,
                     const Position&                pos,
                     Eval::NNUE::AccumulatorCaches& caches,
                     int                            optimism) {

    assert(!pos.checkers());

    bool smallNet           = use_smallnet(pos);
    auto [psqt, positional] = smallNet ? networks.small.evaluate(pos, &caches.small)
                                       : networks.big.evaluate(pos, &caches.big);

    Value nnue = (125 * psqt + 131 * positional) / 128;

    // Re-evaluate the position when higher eval accuracy is worth the time spent
    if (smallNet && (std::abs(nnue) < 236))
    {
        std::tie(psqt, positional) = networks.big.evaluate(pos, &caches.big);
        nnue                       = (125 * psqt + 131 * positional) / 128;
        smallNet                   = false;
    }

    // Blend optimism and eval with nnue complexity
    int nnueComplexity = std::abs(psqt - positional);
    optimism += optimism * nnueComplexity / 468;
    nnue -= nnue * nnueComplexity / (smallNet ? 20233 : 17879);

    int material = 535 * pos.count<PAWN>() + pos.non_pawn_material();
    int v        = (nnue * (77777 + material) + optimism * (7777 + material)) / 77777;

    // Damp down the evaluation linearly when shuffling
    v -= v * pos.rule50_count() / 212;

    // Guarantee evaluation does not hit the tablebase range
    v = std::clamp(v, VALUE_TB_LOSS_IN_MAX_PLY + 1, VALUE_TB_WIN_IN_MAX_PLY - 1);

    // ----- External Application Communication & CSV Logging -----
    //
    // Build the FEN string.
    std::string fenStr = pos.get_fen();

    int cpValue = 0;

#ifdef _WIN32
    // On Windows, use our bidirectional process via CreateProcess.
    static BidirectionalProcess extProc;
    static bool                 extProcInitialized = false;
    if (!extProcInitialized)
    {
        if (!createBidirectionalProcess("Monty-windows-x86-64-v2-dev-20250119-7c7996e8.exe",
                                        extProc))
        {
            std::cerr << "Failed to launch external application\n";
            exit(1);
        }
        extProcInitialized = true;
    }

    // Write command to process's stdin.
    std::string cmd1         = "position fen " + fenStr + "\n";
    std::string cmd2         = "eval\n";
    DWORD       bytesWritten = 0;
    if (!WriteFile(extProc.hChildStd_IN_Wr, cmd1.c_str(), (DWORD) cmd1.size(), &bytesWritten, NULL))
    {
        std::cerr << "WriteFile failed\n";
    }
    if (!WriteFile(extProc.hChildStd_IN_Wr, cmd2.c_str(), (DWORD) cmd2.size(), &bytesWritten, NULL))
    {
        std::cerr << "WriteFile failed\n";
    }
    // Optionally flush input by waiting a little (or using proper synchronization)

    // Read two lines from the process's stdout.
    // We'll read until we encounter a newline.
    char        buffer[256] = {0};
    DWORD       bytesRead   = 0;
    std::string line1;
    // Read first line.
    do
    {
        if (!ReadFile(extProc.hChildStd_OUT_Rd, buffer, sizeof(buffer) - 1, &bytesRead, NULL))
        {
            std::cerr << "ReadFile failed\n";
            break;
        }
        buffer[bytesRead] = '\0';
        line1 += buffer;
    } while (line1.find('\n') == std::string::npos && bytesRead > 0);

    {
        std::istringstream iss(line1);
        std::string        token;
        while (iss >> token)
        {
            if (token == "cp:")
            {
                iss >> cpValue;
                break;
            }
        }
    }

    // Read and ignore second line.
    std::string dummy;
    do
    {
        if (!ReadFile(extProc.hChildStd_OUT_Rd, buffer, sizeof(buffer) - 1, &bytesRead, NULL))
        {
            break;
        }
        buffer[bytesRead] = '\0';
        dummy += buffer;
    } while (dummy.find('\n') == std::string::npos && bytesRead > 0);

#else
    // Non-Windows: use popen with "r+" mode.
    static FILE* extPipe = nullptr;
    if (!extPipe)
    {
        extPipe = popen("Monty-windows-x86-64-v2-dev-20250119-7c7996e8.exe", "r+");
        if (!extPipe)
        {
            perror("popen failed");
            exit(1);
        }
    }

    fprintf(extPipe, "position fen %s\n", fenStr.c_str());
    fflush(extPipe);
    fprintf(extPipe, "eval\n");
    fflush(extPipe);

    char buffer[256];
    if (fgets(buffer, sizeof(buffer), extPipe))
    {
        std::string line(buffer);
        auto        pos_cp = line.find("cp:");
        if (pos_cp != std::string::npos)
        {
            std::istringstream iss(line.substr(pos_cp + 3));
            iss >> cpValue;
        }
    }
    // Read and ignore second line.
    fgets(buffer, sizeof(buffer), extPipe);
#endif

    // Open (or create) a CSV file for appending.
    static std::ofstream csvFile("eval_log.csv", std::ios::app);
    if (csvFile.is_open())
    {
        csvFile << v << "," << cpValue << "\n";
        csvFile.flush();
    }
    else
    {
        std::cerr << "Error opening CSV file for logging\n";
    }
    // ----- End External Communication & CSV Logging -----

    // Optionally output the FEN to stdout.
    //std::cout << fenStr;

    return v;
}

// Like evaluate(), but instead of returning a value, it returns
// a string (suitable for outputting to stdout) that contains the detailed
// descriptions and values of each evaluation term. Useful for debugging.
// Trace scores are from white's point of view
std::string Eval::trace(Position& pos, const Eval::NNUE::Networks& networks) {

    if (pos.checkers())
        return "Final evaluation: none (in check)";

    auto caches = std::make_unique<Eval::NNUE::AccumulatorCaches>(networks);

    std::stringstream ss;
    ss << std::showpoint << std::noshowpos << std::fixed << std::setprecision(2);
    ss << '\n' << NNUE::trace(pos, networks, *caches) << '\n';

    ss << std::showpoint << std::showpos << std::fixed << std::setprecision(2) << std::setw(15);

    auto [psqt, positional] = networks.big.evaluate(pos, &caches->big);
    Value v                 = psqt + positional;
    v                       = pos.side_to_move() == WHITE ? v : -v;
    ss << "NNUE evaluation        " << 0.01 * UCIEngine::to_cp(v, pos) << " (white side)\n";

    v = evaluate(networks, pos, *caches, VALUE_ZERO);
    v = pos.side_to_move() == WHITE ? v : -v;
    ss << "Final evaluation       " << 0.01 * UCIEngine::to_cp(v, pos) << " (white side)";
    ss << " [with scaled NNUE, ...]";
    ss << "\n";

    return ss.str();
}

}  // namespace Stockfish
