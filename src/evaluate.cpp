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
#include <thread>
#include <mutex>
#include <condition_variable>
#include <queue>
#include <chrono>
#include <fstream>

#ifdef __unix__
    #include <fcntl.h>  // For fcntl() on non-Windows systems (if needed)
#endif

#include "nnue/network.h"
#include "nnue/nnue_misc.h"
#include "position.h"
#include "types.h"
#include "uci.h"
#include "nnue/nnue_accumulator.h"

#ifdef _WIN32
    #include <windows.h>
#endif

namespace Stockfish {

// Timeout and retry constants (not used in the fully blocking version)
static const int TIMEOUT_MS  = 200;
static const int MAX_RETRIES = 3;

//
// ExternalComm
//
// This class encapsulates communication with the external process (monty.exe).
// It launches the process, then starts a dedicated I/O thread that continuously
// reads data from monty.exe’s standard output. The thread splits incoming data
// on newline characters and pushes each complete line into a thread‑safe queue.
// The method getLineSync() blocks until a full line is available.
//
class ExternalComm {
   public:
    ExternalComm();
    ~ExternalComm();

    // Initializes the external process and starts the I/O thread.
    bool initialize();

    // Sends a command string to the external process.
    bool sendCommand(const std::string& cmd);

    // Blocks until a complete output line is available (terminated by '\n')
    // and returns that line in 'line'.
    bool getLineSync(std::string& line);

   private:
    std::mutex              mtx;
    std::condition_variable cond;
    std::queue<std::string> lineQueue;
    bool                    stopThread;
    std::thread             ioThread;

#ifdef _WIN32
    // Windows-specific members.
    struct BidirectionalProcess {
        PROCESS_INFORMATION pi;
        HANDLE              hChildStd_IN_Wr;
        HANDLE              hChildStd_OUT_Rd;
    } extProc;

    // Helper to launch a bidirectional process.
    bool createBidirectionalProcess(const char* cmd, BidirectionalProcess& bp);
#else
    // Non-Windows: we use popen.
    FILE* extPipe;
#endif

    // The dedicated I/O thread function.
    void ioThreadFunc();
};

ExternalComm::ExternalComm() :
    stopThread(false) {
#ifdef _WIN32
    // Nothing additional needed.
#else
    extPipe = nullptr;
#endif
}

ExternalComm::~ExternalComm() {
    stopThread = true;
    if (ioThread.joinable())
        ioThread.join();
#ifdef _WIN32
        // Optionally close process handles here.
#else
    if (extPipe)
        pclose(extPipe);
#endif
}

#ifdef _WIN32
bool ExternalComm::createBidirectionalProcess(const char* cmd, BidirectionalProcess& bp) {
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
#endif

bool ExternalComm::initialize() {
#ifdef _WIN32
    // Launch monty.exe on Windows.
    if (!createBidirectionalProcess("monty.exe", extProc))
    {
        std::cerr << "Failed to launch monty.exe\n";
        return false;
    }
#else
    // On non-Windows systems, launch monty.exe using popen.
    extPipe = popen("./monty.exe", "r+");
    if (!extPipe)
    {
        perror("popen failed");
        return false;
    }
#endif
    // Clear any old output.
    {
        std::lock_guard<std::mutex> lock(mtx);
        while (!lineQueue.empty())
            lineQueue.pop();
    }
    stopThread = false;
    // Start the dedicated I/O thread.
    ioThread = std::thread(&ExternalComm::ioThreadFunc, this);
    return true;
}

bool ExternalComm::sendCommand(const std::string& cmd) {
#ifdef _WIN32
    DWORD bytesWritten = 0;
    if (!WriteFile(extProc.hChildStd_IN_Wr, cmd.c_str(), (DWORD) cmd.size(), &bytesWritten, NULL))
    {
        std::cerr << "WriteFile failed for command: " << cmd;
        return false;
    }
#else
    if (fprintf(extPipe, "%s", cmd.c_str()) < 0)
    {
        std::cerr << "fprintf failed for command: " << cmd;
        return false;
    }
    fflush(extPipe);
#endif
    return true;
}

bool ExternalComm::getLineSync(std::string& line) {
    std::unique_lock<std::mutex> lock(mtx);
    // Block indefinitely until a full line is available.
    cond.wait(lock, [this]() { return !lineQueue.empty(); });
    line = lineQueue.front();
    lineQueue.pop();
    return true;
}

//
// Modified I/O thread function that splits incoming data on newline characters.
//
void ExternalComm::ioThreadFunc() {
    std::string partial;  // accumulate any leftover partial data
    while (!stopThread)
    {
        std::string data;
#ifdef _WIN32
        char  buffer[256] = {0};
        DWORD bytesRead   = 0;
        if (!ReadFile(extProc.hChildStd_OUT_Rd, buffer, sizeof(buffer) - 1, &bytesRead, NULL))
        {
            std::cerr << "ReadFile failed in ioThreadFunc\n";
            std::this_thread::sleep_for(std::chrono::milliseconds(10));
            continue;
        }
        if (bytesRead > 0)
        {
            buffer[bytesRead] = '\0';
            data              = buffer;
        }
#else
        char buffer[256];
        if (fgets(buffer, sizeof(buffer), extPipe))
            data = buffer;
        else
        {
            std::this_thread::sleep_for(std::chrono::milliseconds(10));
            continue;
        }
#endif
        // Prepend any previously read partial data.
        data = partial + data;
        partial.clear();

        // Split the received data on newline characters.
        size_t start = 0;
        while (true)
        {
            size_t pos = data.find('\n', start);
            if (pos == std::string::npos)
            {
                // No complete line; save the rest as partial.
                partial = data.substr(start);
                break;
            }
            // Extract the complete line (including the newline).
            std::string line = data.substr(start, pos - start + 1);
            {
                std::lock_guard<std::mutex> lock(mtx);
                lineQueue.push(line);
            }
            cond.notify_one();
            start = pos + 1;
            if (start >= data.size())
                break;
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(1));
    }
}

// Global instance for external communication.
static ExternalComm externalComm;
static bool         externalCommInitialized = false;

//
// Stockfish Evaluation Functions
//

// Returns a material-only evaluation from the perspective of color c.
int Eval::simple_eval(const Position& pos, Color c) {
    return PawnValue * (pos.count<PAWN>(c) - pos.count<PAWN>(~c))
         + (pos.non_pawn_material(c) - pos.non_pawn_material(~c));
}

// Chooses between the small and big NNUE network based on a simple evaluation.
bool Eval::use_smallnet(const Position& pos) {
    int simpleEval = simple_eval(pos, pos.side_to_move());
    return std::abs(simpleEval) > 962;
}

// The modified evaluation function.
// It combines NNUE evaluation with external evaluation data from monty.exe,
// and logs both values to a CSV file. This version blocks deterministically
// until a valid external cp value (different from 40000) is obtained.
Value Eval::evaluate(const Eval::NNUE::Networks&    networks,
                     const Position&                pos,
                     Eval::NNUE::AccumulatorCaches& caches,
                     int                            optimism) {
    assert(!pos.checkers());

    bool smallNet           = use_smallnet(pos);
    auto [psqt, positional] = smallNet ? networks.small.evaluate(pos, &caches.small)
                                       : networks.big.evaluate(pos, &caches.big);
    Value nnue              = (125 * psqt + 131 * positional) / 128;

    // Re-evaluate for higher accuracy if needed.
    if (smallNet && (std::abs(nnue) < 236))
    {
        std::tie(psqt, positional) = networks.big.evaluate(pos, &caches.big);
        nnue                       = (125 * psqt + 131 * positional) / 128;
        smallNet                   = false;
    }

    // Blend optimism and evaluation using NNUE complexity.
    int nnueComplexity = std::abs(psqt - positional);
    optimism += optimism * nnueComplexity / 468;
    nnue -= nnue * nnueComplexity / (smallNet ? 20233 : 17879);

    int material = 535 * pos.count<PAWN>() + pos.non_pawn_material();
    int v        = (nnue * (77777 + material) + optimism * (7777 + material)) / 77777;
    v -= v * pos.rule50_count() / 212;
    v = std::clamp(v, VALUE_TB_LOSS_IN_MAX_PLY + 1, VALUE_TB_WIN_IN_MAX_PLY - 1);

    std::string fenStr = pos.get_fen();
    // For debugging, cpValue is initialized to 40000 (which should never be the valid output).
    int cpValue = 40000;

    if (!externalCommInitialized)
    {
        if (!externalComm.initialize())
        {
            std::cerr << "Failed to initialize external communication with monty.exe\n";
            exit(1);
        }
        externalCommInitialized = true;
    }

    // Loop until a valid cp value is obtained.
    while (cpValue == 40000)
    {
        externalComm.sendCommand("position fen " + fenStr + "\n");
        externalComm.sendCommand("eval\n");

        std::string line;
        externalComm.getLineSync(line);
        std::istringstream iss(line);
        std::string        token;
        while (iss >> token)
        {
            if (token == "cp:")
            {
                iss >> cpValue;
                break;
            }
        }
        if (cpValue == 40000)
        {
            std::cerr << "Invalid cp value received, waiting for correct result...\n";
            std::this_thread::sleep_for(std::chrono::milliseconds(50));
        }
    }

    // Read and ignore the second output line.
    {
        std::string dummy;
        externalComm.getLineSync(dummy);
    }

    // Append the evaluation and cp value to a CSV log file.
    //static std::ofstream csvFile("eval_log.csv", std::ios::app);
    //if (csvFile.is_open())
    //{
    //    csvFile << v << "," << cpValue << "\n";
    //    csvFile.flush();
    //}
    //else
    //{
    //    std::cerr << "Error opening CSV file for logging\n";
    //}

    return cpValue;
}

std::string Eval::trace(Position& pos, const Eval::NNUE::Networks& networks) {
    if (pos.checkers())
        return "Final evaluation: none (in check)";

    auto              caches = std::make_unique<Eval::NNUE::AccumulatorCaches>(networks);
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
