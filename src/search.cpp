/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2023 The Stockfish developers (see AUTHORS file)

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

#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstring>   // For std::memset
#include <iostream>
#include <sstream>

#include "evaluate.h"
#include "misc.h"
#include "movegen.h"
#include "movepick.h"
#include "position.h"
#include "search.h"
#include "thread.h"
#include "timeman.h"
#include "tt.h"
#include "uci.h"
#include "syzygy/tbprobe.h"
#include "nnue/evaluate_nnue.h"

namespace Stockfish {

namespace Search {

  LimitsType Limits;
}

namespace Tablebases {

  int Cardinality;
  bool RootInTB;
  bool UseRule50;
  Depth ProbeDepth;
}

namespace TB = Tablebases;

using std::string;
using Eval::evaluate;
using namespace Search;

namespace {

    //VLTC Tune 1 60k game values
    int lmrDepthScale = 978; int lmrDepthScaleTwo = 876; int ttMoveCutNodeScale = 3803;
    int depthReductionDecreaseThres = 4707; int LMRDepthReductionThres = -3754;

  // Different node types, used as a template parameter
  enum NodeType { NonPV, PV, Root };

  // Futility margin
  Value futility_margin(Depth d, bool noTtCutNode, bool improving) {
    return Value((140 - 40 * noTtCutNode) * (d - improving));
  }

  // Reductions lookup table initialized at startup
  int Reductions[MAX_MOVES]; // [depth or moveNumber]

  int reduction(bool i, Depth d, int mn, Value delta, Value rootDelta) {
      int r = Reductions[d] * Reductions[mn];
      return (r + 1372 - int(delta) * 1073 / int(rootDelta)) / 1024 + (!i && r > 936);
  }

  //Extension/Reduction NN Zero Initialise
  int inputScales[24][9][2] = {};

  int depthInput[24][5] = {};

  int singularInput[24][4] = {};

  int nodeTypeInput[24][3] = {};

  int ttValueInput[24][3] = {};

  int ttMoveInput[24][5] = {};

  int statScoreInput[24] = {};

  int biases[2][24] = { {},
                         {} };

  int slopes[2][2][24] = { {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
                            {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
                          {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
                            {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}} };

  int outputBias[2] = {};
  int outputSlopes[2][2] = { { 1024, 1024 }, {1024, 1024} };

  void SetValues() {
      inputScales[0][0][0] = 2;
      inputScales[0][0][1] = -4;
      inputScales[0][1][0] = 16;
      inputScales[0][1][1] = -3;
      inputScales[0][2][0] = -9;
      inputScales[0][2][1] = 11;
      inputScales[0][3][0] = 3;
      inputScales[0][3][1] = 5;
      inputScales[0][4][0] = -29;
      inputScales[0][4][1] = 6;
      inputScales[0][5][0] = 21;
      inputScales[0][5][1] = 10;
      inputScales[0][6][0] = 8;
      inputScales[0][6][1] = 30;
      inputScales[0][7][0] = -4;
      inputScales[0][7][1] = 2;
      inputScales[0][8][0] = 9;
      inputScales[0][8][1] = -29;
      inputScales[1][0][0] = 8;
      inputScales[1][0][1] = 4;
      inputScales[1][1][0] = -6;
      inputScales[1][1][1] = 4;
      inputScales[1][2][0] = 28;
      inputScales[1][2][1] = 18;
      inputScales[1][3][0] = 8;
      inputScales[1][3][1] = 10;
      inputScales[1][4][0] = -22;
      inputScales[1][4][1] = -15;
      inputScales[1][5][0] = 0;
      inputScales[1][5][1] = -1;
      inputScales[1][6][0] = -11;
      inputScales[1][6][1] = -3;
      inputScales[1][7][0] = 31;
      inputScales[1][7][1] = -24;
      inputScales[1][8][0] = -24;
      inputScales[1][8][1] = 15;
      inputScales[2][0][0] = -30;
      inputScales[2][0][1] = 5;
      inputScales[2][1][0] = -23;
      inputScales[2][1][1] = -12;
      inputScales[2][2][0] = -27;
      inputScales[2][2][1] = -25;
      inputScales[2][3][0] = 13;
      inputScales[2][3][1] = 32;
      inputScales[2][4][0] = 23;
      inputScales[2][4][1] = 17;
      inputScales[2][5][0] = 21;
      inputScales[2][5][1] = -34;
      inputScales[2][6][0] = 2;
      inputScales[2][6][1] = 5;
      inputScales[2][7][0] = -3;
      inputScales[2][7][1] = 2;
      inputScales[2][8][0] = -8;
      inputScales[2][8][1] = -5;
      inputScales[3][0][0] = 45;
      inputScales[3][0][1] = 25;
      inputScales[3][1][0] = -13;
      inputScales[3][1][1] = -4;
      inputScales[3][2][0] = 33;
      inputScales[3][2][1] = -36;
      inputScales[3][3][0] = 2;
      inputScales[3][3][1] = -24;
      inputScales[3][4][0] = 16;
      inputScales[3][4][1] = -3;
      inputScales[3][5][0] = -10;
      inputScales[3][5][1] = 12;
      inputScales[3][6][0] = 24;
      inputScales[3][6][1] = -20;
      inputScales[3][7][0] = 2;
      inputScales[3][7][1] = -8;
      inputScales[3][8][0] = -13;
      inputScales[3][8][1] = -30;
      inputScales[4][0][0] = 0;
      inputScales[4][0][1] = -30;
      inputScales[4][1][0] = 18;
      inputScales[4][1][1] = -22;
      inputScales[4][2][0] = -10;
      inputScales[4][2][1] = -8;
      inputScales[4][3][0] = 9;
      inputScales[4][3][1] = 25;
      inputScales[4][4][0] = -4;
      inputScales[4][4][1] = 5;
      inputScales[4][5][0] = -4;
      inputScales[4][5][1] = -9;
      inputScales[4][6][0] = 24;
      inputScales[4][6][1] = -23;
      inputScales[4][7][0] = 29;
      inputScales[4][7][1] = -4;
      inputScales[4][8][0] = -32;
      inputScales[4][8][1] = 15;
      inputScales[5][0][0] = -14;
      inputScales[5][0][1] = -17;
      inputScales[5][1][0] = 3;
      inputScales[5][1][1] = -11;
      inputScales[5][2][0] = 16;
      inputScales[5][2][1] = -19;
      inputScales[5][3][0] = 10;
      inputScales[5][3][1] = 15;
      inputScales[5][4][0] = 10;
      inputScales[5][4][1] = 11;
      inputScales[5][5][0] = -20;
      inputScales[5][5][1] = 6;
      inputScales[5][6][0] = -18;
      inputScales[5][6][1] = 14;
      inputScales[5][7][0] = -10;
      inputScales[5][7][1] = -34;
      inputScales[5][8][0] = 12;
      inputScales[5][8][1] = -3;
      inputScales[6][0][0] = 2;
      inputScales[6][0][1] = 25;
      inputScales[6][1][0] = -2;
      inputScales[6][1][1] = 12;
      inputScales[6][2][0] = -4;
      inputScales[6][2][1] = 16;
      inputScales[6][3][0] = -11;
      inputScales[6][3][1] = -24;
      inputScales[6][4][0] = -14;
      inputScales[6][4][1] = -2;
      inputScales[6][5][0] = -1;
      inputScales[6][5][1] = 5;
      inputScales[6][6][0] = -12;
      inputScales[6][6][1] = -1;
      inputScales[6][7][0] = -5;
      inputScales[6][7][1] = 16;
      inputScales[6][8][0] = 0;
      inputScales[6][8][1] = 22;
      inputScales[7][0][0] = 2;
      inputScales[7][0][1] = 0;
      inputScales[7][1][0] = -6;
      inputScales[7][1][1] = -9;
      inputScales[7][2][0] = -1;
      inputScales[7][2][1] = 20;
      inputScales[7][3][0] = 12;
      inputScales[7][3][1] = 17;
      inputScales[7][4][0] = 7;
      inputScales[7][4][1] = 7;
      inputScales[7][5][0] = 11;
      inputScales[7][5][1] = 3;
      inputScales[7][6][0] = -18;
      inputScales[7][6][1] = -14;
      inputScales[7][7][0] = 3;
      inputScales[7][7][1] = -9;
      inputScales[7][8][0] = -4;
      inputScales[7][8][1] = -12;
      inputScales[8][0][0] = -6;
      inputScales[8][0][1] = -30;
      inputScales[8][1][0] = 25;
      inputScales[8][1][1] = -38;
      inputScales[8][2][0] = 17;
      inputScales[8][2][1] = -5;
      inputScales[8][3][0] = -11;
      inputScales[8][3][1] = 1;
      inputScales[8][4][0] = -24;
      inputScales[8][4][1] = -29;
      inputScales[8][5][0] = 24;
      inputScales[8][5][1] = -38;
      inputScales[8][6][0] = 14;
      inputScales[8][6][1] = -13;
      inputScales[8][7][0] = -3;
      inputScales[8][7][1] = 28;
      inputScales[8][8][0] = -1;
      inputScales[8][8][1] = 24;
      inputScales[9][0][0] = 26;
      inputScales[9][0][1] = 11;
      inputScales[9][1][0] = -10;
      inputScales[9][1][1] = -8;
      inputScales[9][2][0] = -5;
      inputScales[9][2][1] = -9;
      inputScales[9][3][0] = -17;
      inputScales[9][3][1] = -15;
      inputScales[9][4][0] = 19;
      inputScales[9][4][1] = -2;
      inputScales[9][5][0] = -1;
      inputScales[9][5][1] = -29;
      inputScales[9][6][0] = 8;
      inputScales[9][6][1] = -6;
      inputScales[9][7][0] = 7;
      inputScales[9][7][1] = -5;
      inputScales[9][8][0] = 1;
      inputScales[9][8][1] = 12;
      inputScales[10][0][0] = 41;
      inputScales[10][0][1] = -55;
      inputScales[10][1][0] = -12;
      inputScales[10][1][1] = -9;
      inputScales[10][2][0] = 29;
      inputScales[10][2][1] = -29;
      inputScales[10][3][0] = 4;
      inputScales[10][3][1] = -25;
      inputScales[10][4][0] = -8;
      inputScales[10][4][1] = -7;
      inputScales[10][5][0] = -26;
      inputScales[10][5][1] = -2;
      inputScales[10][6][0] = -6;
      inputScales[10][6][1] = -3;
      inputScales[10][7][0] = 15;
      inputScales[10][7][1] = -6;
      inputScales[10][8][0] = 22;
      inputScales[10][8][1] = 6;
      inputScales[11][0][0] = 19;
      inputScales[11][0][1] = 0;
      inputScales[11][1][0] = -2;
      inputScales[11][1][1] = 0;
      inputScales[11][2][0] = 0;
      inputScales[11][2][1] = 2;
      inputScales[11][3][0] = -33;
      inputScales[11][3][1] = 17;
      inputScales[11][4][0] = 4;
      inputScales[11][4][1] = 0;
      inputScales[11][5][0] = -6;
      inputScales[11][5][1] = 14;
      inputScales[11][6][0] = -48;
      inputScales[11][6][1] = 16;
      inputScales[11][7][0] = 23;
      inputScales[11][7][1] = -4;
      inputScales[11][8][0] = 6;
      inputScales[11][8][1] = 9;
      inputScales[12][0][0] = 0;
      inputScales[12][0][1] = -2;
      inputScales[12][1][0] = 33;
      inputScales[12][1][1] = 17;
      inputScales[12][2][0] = -13;
      inputScales[12][2][1] = -26;
      inputScales[12][3][0] = 15;
      inputScales[12][3][1] = 36;
      inputScales[12][4][0] = 10;
      inputScales[12][4][1] = 15;
      inputScales[12][5][0] = 2;
      inputScales[12][5][1] = -1;
      inputScales[12][6][0] = 13;
      inputScales[12][6][1] = 18;
      inputScales[12][7][0] = -8;
      inputScales[12][7][1] = 7;
      inputScales[12][8][0] = -5;
      inputScales[12][8][1] = -1;
      inputScales[13][0][0] = -5;
      inputScales[13][0][1] = 10;
      inputScales[13][1][0] = -4;
      inputScales[13][1][1] = 23;
      inputScales[13][2][0] = -1;
      inputScales[13][2][1] = -5;
      inputScales[13][3][0] = 9;
      inputScales[13][3][1] = 24;
      inputScales[13][4][0] = -1;
      inputScales[13][4][1] = -7;
      inputScales[13][5][0] = -14;
      inputScales[13][5][1] = -7;
      inputScales[13][6][0] = 4;
      inputScales[13][6][1] = -23;
      inputScales[13][7][0] = 20;
      inputScales[13][7][1] = -9;
      inputScales[13][8][0] = 7;
      inputScales[13][8][1] = 10;
      inputScales[14][0][0] = -9;
      inputScales[14][0][1] = -24;
      inputScales[14][1][0] = 14;
      inputScales[14][1][1] = -10;
      inputScales[14][2][0] = -15;
      inputScales[14][2][1] = 12;
      inputScales[14][3][0] = 8;
      inputScales[14][3][1] = -16;
      inputScales[14][4][0] = -20;
      inputScales[14][4][1] = -16;
      inputScales[14][5][0] = -14;
      inputScales[14][5][1] = -20;
      inputScales[14][6][0] = 17;
      inputScales[14][6][1] = -6;
      inputScales[14][7][0] = -27;
      inputScales[14][7][1] = 3;
      inputScales[14][8][0] = -2;
      inputScales[14][8][1] = 11;
      inputScales[15][0][0] = 6;
      inputScales[15][0][1] = -7;
      inputScales[15][1][0] = -2;
      inputScales[15][1][1] = 0;
      inputScales[15][2][0] = -2;
      inputScales[15][2][1] = -7;
      inputScales[15][3][0] = -8;
      inputScales[15][3][1] = 1;
      inputScales[15][4][0] = 3;
      inputScales[15][4][1] = 15;
      inputScales[15][5][0] = -7;
      inputScales[15][5][1] = 15;
      inputScales[15][6][0] = -12;
      inputScales[15][6][1] = 5;
      inputScales[15][7][0] = 0;
      inputScales[15][7][1] = -3;
      inputScales[15][8][0] = 9;
      inputScales[15][8][1] = 15;
      inputScales[16][0][0] = 7;
      inputScales[16][0][1] = -38;
      inputScales[16][1][0] = -22;
      inputScales[16][1][1] = 16;
      inputScales[16][2][0] = -18;
      inputScales[16][2][1] = -29;
      inputScales[16][3][0] = -33;
      inputScales[16][3][1] = 27;
      inputScales[16][4][0] = 1;
      inputScales[16][4][1] = -9;
      inputScales[16][5][0] = 1;
      inputScales[16][5][1] = 24;
      inputScales[16][6][0] = 21;
      inputScales[16][6][1] = 12;
      inputScales[16][7][0] = -1;
      inputScales[16][7][1] = -14;
      inputScales[16][8][0] = -30;
      inputScales[16][8][1] = 22;
      inputScales[17][0][0] = 21;
      inputScales[17][0][1] = 0;
      inputScales[17][1][0] = 11;
      inputScales[17][1][1] = 3;
      inputScales[17][2][0] = 10;
      inputScales[17][2][1] = -4;
      inputScales[17][3][0] = 15;
      inputScales[17][3][1] = 0;
      inputScales[17][4][0] = 13;
      inputScales[17][4][1] = -1;
      inputScales[17][5][0] = 18;
      inputScales[17][5][1] = -11;
      inputScales[17][6][0] = -9;
      inputScales[17][6][1] = 4;
      inputScales[17][7][0] = -6;
      inputScales[17][7][1] = -38;
      inputScales[17][8][0] = 7;
      inputScales[17][8][1] = 22;
      inputScales[18][0][0] = 18;
      inputScales[18][0][1] = 9;
      inputScales[18][1][0] = -16;
      inputScales[18][1][1] = 33;
      inputScales[18][2][0] = 4;
      inputScales[18][2][1] = -20;
      inputScales[18][3][0] = -51;
      inputScales[18][3][1] = -19;
      inputScales[18][4][0] = -5;
      inputScales[18][4][1] = 6;
      inputScales[18][5][0] = 5;
      inputScales[18][5][1] = 8;
      inputScales[18][6][0] = 15;
      inputScales[18][6][1] = -7;
      inputScales[18][7][0] = 5;
      inputScales[18][7][1] = -4;
      inputScales[18][8][0] = -23;
      inputScales[18][8][1] = 14;
      inputScales[19][0][0] = -10;
      inputScales[19][0][1] = -34;
      inputScales[19][1][0] = 3;
      inputScales[19][1][1] = -20;
      inputScales[19][2][0] = 2;
      inputScales[19][2][1] = -6;
      inputScales[19][3][0] = -7;
      inputScales[19][3][1] = -16;
      inputScales[19][4][0] = 15;
      inputScales[19][4][1] = -16;
      inputScales[19][5][0] = 6;
      inputScales[19][5][1] = -4;
      inputScales[19][6][0] = -9;
      inputScales[19][6][1] = 7;
      inputScales[19][7][0] = -3;
      inputScales[19][7][1] = -39;
      inputScales[19][8][0] = 7;
      inputScales[19][8][1] = 8;
      inputScales[20][0][0] = 28;
      inputScales[20][0][1] = -29;
      inputScales[20][1][0] = -18;
      inputScales[20][1][1] = -18;
      inputScales[20][2][0] = -16;
      inputScales[20][2][1] = 0;
      inputScales[20][3][0] = 4;
      inputScales[20][3][1] = -30;
      inputScales[20][4][0] = 13;
      inputScales[20][4][1] = 2;
      inputScales[20][5][0] = 0;
      inputScales[20][5][1] = -11;
      inputScales[20][6][0] = -5;
      inputScales[20][6][1] = -8;
      inputScales[20][7][0] = -32;
      inputScales[20][7][1] = 3;
      inputScales[20][8][0] = -9;
      inputScales[20][8][1] = -14;
      inputScales[21][0][0] = -20;
      inputScales[21][0][1] = 13;
      inputScales[21][1][0] = 9;
      inputScales[21][1][1] = -8;
      inputScales[21][2][0] = 1;
      inputScales[21][2][1] = 1;
      inputScales[21][3][0] = 25;
      inputScales[21][3][1] = 20;
      inputScales[21][4][0] = 26;
      inputScales[21][4][1] = 36;
      inputScales[21][5][0] = 18;
      inputScales[21][5][1] = 2;
      inputScales[21][6][0] = -16;
      inputScales[21][6][1] = 20;
      inputScales[21][7][0] = 3;
      inputScales[21][7][1] = 25;
      inputScales[21][8][0] = 10;
      inputScales[21][8][1] = -8;
      inputScales[22][0][0] = -5;
      inputScales[22][0][1] = -38;
      inputScales[22][1][0] = 25;
      inputScales[22][1][1] = -5;
      inputScales[22][2][0] = 15;
      inputScales[22][2][1] = 31;
      inputScales[22][3][0] = -2;
      inputScales[22][3][1] = -34;
      inputScales[22][4][0] = -7;
      inputScales[22][4][1] = 2;
      inputScales[22][5][0] = 5;
      inputScales[22][5][1] = -17;
      inputScales[22][6][0] = 0;
      inputScales[22][6][1] = -14;
      inputScales[22][7][0] = -20;
      inputScales[22][7][1] = -3;
      inputScales[22][8][0] = -6;
      inputScales[22][8][1] = 45;
      inputScales[23][0][0] = 10;
      inputScales[23][0][1] = -16;
      inputScales[23][1][0] = 23;
      inputScales[23][1][1] = 1;
      inputScales[23][2][0] = 16;
      inputScales[23][2][1] = -28;
      inputScales[23][3][0] = -14;
      inputScales[23][3][1] = -17;
      inputScales[23][4][0] = 7;
      inputScales[23][4][1] = 10;
      inputScales[23][5][0] = 29;
      inputScales[23][5][1] = 23;
      inputScales[23][6][0] = -12;
      inputScales[23][6][1] = 30;
      inputScales[23][7][0] = -12;
      inputScales[23][7][1] = -22;
      inputScales[23][8][0] = 11;
      inputScales[23][8][1] = -2;
      depthInput[0][0] = 15;
      depthInput[0][1] = 5;
      depthInput[0][2] = 13;
      depthInput[0][3] = -30;
      depthInput[0][4] = 1;
      depthInput[1][0] = -18;
      depthInput[1][1] = 0;
      depthInput[1][2] = 0;
      depthInput[1][3] = 0;
      depthInput[1][4] = 36;
      depthInput[2][0] = -27;
      depthInput[2][1] = -26;
      depthInput[2][2] = 10;
      depthInput[2][3] = -21;
      depthInput[2][4] = -5;
      depthInput[3][0] = -3;
      depthInput[3][1] = -8;
      depthInput[3][2] = -30;
      depthInput[3][3] = 23;
      depthInput[3][4] = 8;
      depthInput[4][0] = 1;
      depthInput[4][1] = -6;
      depthInput[4][2] = 9;
      depthInput[4][3] = 31;
      depthInput[4][4] = -17;
      depthInput[5][0] = -28;
      depthInput[5][1] = 24;
      depthInput[5][2] = 18;
      depthInput[5][3] = -13;
      depthInput[5][4] = -7;
      depthInput[6][0] = -41;
      depthInput[6][1] = -11;
      depthInput[6][2] = 20;
      depthInput[6][3] = 8;
      depthInput[6][4] = 7;
      depthInput[7][0] = -2;
      depthInput[7][1] = -3;
      depthInput[7][2] = -19;
      depthInput[7][3] = 14;
      depthInput[7][4] = 10;
      depthInput[8][0] = -11;
      depthInput[8][1] = -5;
      depthInput[8][2] = 3;
      depthInput[8][3] = -12;
      depthInput[8][4] = -21;
      depthInput[9][0] = 21;
      depthInput[9][1] = -10;
      depthInput[9][2] = -15;
      depthInput[9][3] = 16;
      depthInput[9][4] = 25;
      depthInput[10][0] = -3;
      depthInput[10][1] = 11;
      depthInput[10][2] = 11;
      depthInput[10][3] = 1;
      depthInput[10][4] = -26;
      depthInput[11][0] = -9;
      depthInput[11][1] = -24;
      depthInput[11][2] = 15;
      depthInput[11][3] = 4;
      depthInput[11][4] = 12;
      depthInput[12][0] = 3;
      depthInput[12][1] = 14;
      depthInput[12][2] = -15;
      depthInput[12][3] = -44;
      depthInput[12][4] = -14;
      depthInput[13][0] = 46;
      depthInput[13][1] = -22;
      depthInput[13][2] = 3;
      depthInput[13][3] = 1;
      depthInput[13][4] = 1;
      depthInput[14][0] = 1;
      depthInput[14][1] = 1;
      depthInput[14][2] = 8;
      depthInput[14][3] = 11;
      depthInput[14][4] = 7;
      depthInput[15][0] = 16;
      depthInput[15][1] = 25;
      depthInput[15][2] = 3;
      depthInput[15][3] = -12;
      depthInput[15][4] = 7;
      depthInput[16][0] = -14;
      depthInput[16][1] = 37;
      depthInput[16][2] = -10;
      depthInput[16][3] = 21;
      depthInput[16][4] = -8;
      depthInput[17][0] = 28;
      depthInput[17][1] = -6;
      depthInput[17][2] = 34;
      depthInput[17][3] = 35;
      depthInput[17][4] = -8;
      depthInput[18][0] = -8;
      depthInput[18][1] = 3;
      depthInput[18][2] = -13;
      depthInput[18][3] = 15;
      depthInput[18][4] = 19;
      depthInput[19][0] = -32;
      depthInput[19][1] = -4;
      depthInput[19][2] = -12;
      depthInput[19][3] = 2;
      depthInput[19][4] = 8;
      depthInput[20][0] = 15;
      depthInput[20][1] = -2;
      depthInput[20][2] = -4;
      depthInput[20][3] = -15;
      depthInput[20][4] = -13;
      depthInput[21][0] = -4;
      depthInput[21][1] = -24;
      depthInput[21][2] = 1;
      depthInput[21][3] = -6;
      depthInput[21][4] = -30;
      depthInput[22][0] = -6;
      depthInput[22][1] = -7;
      depthInput[22][2] = 11;
      depthInput[22][3] = -7;
      depthInput[22][4] = -37;
      depthInput[23][0] = -28;
      depthInput[23][1] = 16;
      depthInput[23][2] = 8;
      depthInput[23][3] = 1;
      depthInput[23][4] = -2;
      singularInput[0][0] = 17;
      singularInput[0][1] = 27;
      singularInput[0][2] = -2;
      singularInput[0][3] = 11;
      singularInput[1][0] = 9;
      singularInput[1][1] = -4;
      singularInput[1][2] = -5;
      singularInput[1][3] = 18;
      singularInput[2][0] = 21;
      singularInput[2][1] = 16;
      singularInput[2][2] = 20;
      singularInput[2][3] = 27;
      singularInput[3][0] = -11;
      singularInput[3][1] = -33;
      singularInput[3][2] = -1;
      singularInput[3][3] = -2;
      singularInput[4][0] = 8;
      singularInput[4][1] = -22;
      singularInput[4][2] = -16;
      singularInput[4][3] = 13;
      singularInput[5][0] = -23;
      singularInput[5][1] = -3;
      singularInput[5][2] = 7;
      singularInput[5][3] = -6;
      singularInput[6][0] = -12;
      singularInput[6][1] = 3;
      singularInput[6][2] = 29;
      singularInput[6][3] = 50;
      singularInput[7][0] = 1;
      singularInput[7][1] = 14;
      singularInput[7][2] = 25;
      singularInput[7][3] = -6;
      singularInput[8][0] = -20;
      singularInput[8][1] = 5;
      singularInput[8][2] = -27;
      singularInput[8][3] = 27;
      singularInput[9][0] = -12;
      singularInput[9][1] = 12;
      singularInput[9][2] = 34;
      singularInput[9][3] = -10;
      singularInput[10][0] = 19;
      singularInput[10][1] = -10;
      singularInput[10][2] = -9;
      singularInput[10][3] = -12;
      singularInput[11][0] = -30;
      singularInput[11][1] = 4;
      singularInput[11][2] = -5;
      singularInput[11][3] = -23;
      singularInput[12][0] = -42;
      singularInput[12][1] = -3;
      singularInput[12][2] = 3;
      singularInput[12][3] = -10;
      singularInput[13][0] = -11;
      singularInput[13][1] = -13;
      singularInput[13][2] = -1;
      singularInput[13][3] = 23;
      singularInput[14][0] = 47;
      singularInput[14][1] = 2;
      singularInput[14][2] = 11;
      singularInput[14][3] = -8;
      singularInput[15][0] = 8;
      singularInput[15][1] = -1;
      singularInput[15][2] = -6;
      singularInput[15][3] = -17;
      singularInput[16][0] = 13;
      singularInput[16][1] = 7;
      singularInput[16][2] = 0;
      singularInput[16][3] = 41;
      singularInput[17][0] = -2;
      singularInput[17][1] = 32;
      singularInput[17][2] = -7;
      singularInput[17][3] = 26;
      singularInput[18][0] = 16;
      singularInput[18][1] = 14;
      singularInput[18][2] = 11;
      singularInput[18][3] = -21;
      singularInput[19][0] = -25;
      singularInput[19][1] = 31;
      singularInput[19][2] = -3;
      singularInput[19][3] = -5;
      singularInput[20][0] = -23;
      singularInput[20][1] = 0;
      singularInput[20][2] = -8;
      singularInput[20][3] = 10;
      singularInput[21][0] = 39;
      singularInput[21][1] = -12;
      singularInput[21][2] = 21;
      singularInput[21][3] = 30;
      singularInput[22][0] = 8;
      singularInput[22][1] = 4;
      singularInput[22][2] = -4;
      singularInput[22][3] = -9;
      singularInput[23][0] = -12;
      singularInput[23][1] = -16;
      singularInput[23][2] = 5;
      singularInput[23][3] = 9;
      nodeTypeInput[0][0] = 10;
      nodeTypeInput[0][1] = -5;
      nodeTypeInput[0][2] = 9;
      nodeTypeInput[1][0] = 5;
      nodeTypeInput[1][1] = 9;
      nodeTypeInput[1][2] = -11;
      nodeTypeInput[2][0] = 10;
      nodeTypeInput[2][1] = -4;
      nodeTypeInput[2][2] = -11;
      nodeTypeInput[3][0] = 34;
      nodeTypeInput[3][1] = -25;
      nodeTypeInput[3][2] = 7;
      nodeTypeInput[4][0] = -9;
      nodeTypeInput[4][1] = 11;
      nodeTypeInput[4][2] = 2;
      nodeTypeInput[5][0] = 15;
      nodeTypeInput[5][1] = -25;
      nodeTypeInput[5][2] = 2;
      nodeTypeInput[6][0] = -16;
      nodeTypeInput[6][1] = -15;
      nodeTypeInput[6][2] = -14;
      nodeTypeInput[7][0] = 3;
      nodeTypeInput[7][1] = -6;
      nodeTypeInput[7][2] = 18;
      nodeTypeInput[8][0] = -8;
      nodeTypeInput[8][1] = -16;
      nodeTypeInput[8][2] = 7;
      nodeTypeInput[9][0] = -5;
      nodeTypeInput[9][1] = 7;
      nodeTypeInput[9][2] = -12;
      nodeTypeInput[10][0] = -20;
      nodeTypeInput[10][1] = 4;
      nodeTypeInput[10][2] = -21;
      nodeTypeInput[11][0] = 14;
      nodeTypeInput[11][1] = -19;
      nodeTypeInput[11][2] = -6;
      nodeTypeInput[12][0] = 7;
      nodeTypeInput[12][1] = -11;
      nodeTypeInput[12][2] = -15;
      nodeTypeInput[13][0] = -23;
      nodeTypeInput[13][1] = 10;
      nodeTypeInput[13][2] = -3;
      nodeTypeInput[14][0] = 16;
      nodeTypeInput[14][1] = 9;
      nodeTypeInput[14][2] = -7;
      nodeTypeInput[15][0] = -22;
      nodeTypeInput[15][1] = 10;
      nodeTypeInput[15][2] = -22;
      nodeTypeInput[16][0] = -29;
      nodeTypeInput[16][1] = -11;
      nodeTypeInput[16][2] = 15;
      nodeTypeInput[17][0] = 33;
      nodeTypeInput[17][1] = 29;
      nodeTypeInput[17][2] = 0;
      nodeTypeInput[18][0] = 8;
      nodeTypeInput[18][1] = 27;
      nodeTypeInput[18][2] = 2;
      nodeTypeInput[19][0] = -1;
      nodeTypeInput[19][1] = 12;
      nodeTypeInput[19][2] = 0;
      nodeTypeInput[20][0] = 7;
      nodeTypeInput[20][1] = 36;
      nodeTypeInput[20][2] = 0;
      nodeTypeInput[21][0] = 14;
      nodeTypeInput[21][1] = -24;
      nodeTypeInput[21][2] = -2;
      nodeTypeInput[22][0] = 13;
      nodeTypeInput[22][1] = -5;
      nodeTypeInput[22][2] = -1;
      nodeTypeInput[23][0] = 7;
      nodeTypeInput[23][1] = -12;
      nodeTypeInput[23][2] = 8;
      ttValueInput[0][0] = 9;
      ttValueInput[0][1] = 3;
      ttValueInput[0][2] = 2;
      ttValueInput[1][0] = 2;
      ttValueInput[1][1] = 5;
      ttValueInput[1][2] = 15;
      ttValueInput[2][0] = -33;
      ttValueInput[2][1] = -10;
      ttValueInput[2][2] = -12;
      ttValueInput[3][0] = 37;
      ttValueInput[3][1] = -27;
      ttValueInput[3][2] = -18;
      ttValueInput[4][0] = 3;
      ttValueInput[4][1] = 9;
      ttValueInput[4][2] = -3;
      ttValueInput[5][0] = -7;
      ttValueInput[5][1] = -15;
      ttValueInput[5][2] = 8;
      ttValueInput[6][0] = 7;
      ttValueInput[6][1] = 7;
      ttValueInput[6][2] = -9;
      ttValueInput[7][0] = -41;
      ttValueInput[7][1] = 13;
      ttValueInput[7][2] = -3;
      ttValueInput[8][0] = -18;
      ttValueInput[8][1] = 7;
      ttValueInput[8][2] = 5;
      ttValueInput[9][0] = -18;
      ttValueInput[9][1] = -4;
      ttValueInput[9][2] = 15;
      ttValueInput[10][0] = 5;
      ttValueInput[10][1] = 1;
      ttValueInput[10][2] = -19;
      ttValueInput[11][0] = 22;
      ttValueInput[11][1] = -16;
      ttValueInput[11][2] = -12;
      ttValueInput[12][0] = -20;
      ttValueInput[12][1] = 11;
      ttValueInput[12][2] = -13;
      ttValueInput[13][0] = 15;
      ttValueInput[13][1] = -30;
      ttValueInput[13][2] = 25;
      ttValueInput[14][0] = 44;
      ttValueInput[14][1] = -15;
      ttValueInput[14][2] = 24;
      ttValueInput[15][0] = 4;
      ttValueInput[15][1] = 13;
      ttValueInput[15][2] = 16;
      ttValueInput[16][0] = -17;
      ttValueInput[16][1] = -16;
      ttValueInput[16][2] = -3;
      ttValueInput[17][0] = -16;
      ttValueInput[17][1] = 1;
      ttValueInput[17][2] = -16;
      ttValueInput[18][0] = -2;
      ttValueInput[18][1] = -21;
      ttValueInput[18][2] = -32;
      ttValueInput[19][0] = 27;
      ttValueInput[19][1] = 3;
      ttValueInput[19][2] = 12;
      ttValueInput[20][0] = 21;
      ttValueInput[20][1] = 15;
      ttValueInput[20][2] = 12;
      ttValueInput[21][0] = -29;
      ttValueInput[21][1] = 22;
      ttValueInput[21][2] = -19;
      ttValueInput[22][0] = -9;
      ttValueInput[22][1] = -33;
      ttValueInput[22][2] = -15;
      ttValueInput[23][0] = 12;
      ttValueInput[23][1] = -2;
      ttValueInput[23][2] = 27;
      ttMoveInput[0][0] = -10;
      ttMoveInput[0][1] = 1;
      ttMoveInput[0][2] = 16;
      ttMoveInput[0][3] = -10;
      ttMoveInput[0][4] = -30;
      ttMoveInput[1][0] = -4;
      ttMoveInput[1][1] = -1;
      ttMoveInput[1][2] = -8;
      ttMoveInput[1][3] = -35;
      ttMoveInput[1][4] = -12;
      ttMoveInput[2][0] = -25;
      ttMoveInput[2][1] = -10;
      ttMoveInput[2][2] = -4;
      ttMoveInput[2][3] = -2;
      ttMoveInput[2][4] = -27;
      ttMoveInput[3][0] = -1;
      ttMoveInput[3][1] = 1;
      ttMoveInput[3][2] = -2;
      ttMoveInput[3][3] = 7;
      ttMoveInput[3][4] = -12;
      ttMoveInput[4][0] = 31;
      ttMoveInput[4][1] = 7;
      ttMoveInput[4][2] = 11;
      ttMoveInput[4][3] = -19;
      ttMoveInput[4][4] = 37;
      ttMoveInput[5][0] = -30;
      ttMoveInput[5][1] = -6;
      ttMoveInput[5][2] = -17;
      ttMoveInput[5][3] = -7;
      ttMoveInput[5][4] = 9;
      ttMoveInput[6][0] = -5;
      ttMoveInput[6][1] = -13;
      ttMoveInput[6][2] = -15;
      ttMoveInput[6][3] = 12;
      ttMoveInput[6][4] = -20;
      ttMoveInput[7][0] = 11;
      ttMoveInput[7][1] = 31;
      ttMoveInput[7][2] = -9;
      ttMoveInput[7][3] = -5;
      ttMoveInput[7][4] = -14;
      ttMoveInput[8][0] = -9;
      ttMoveInput[8][1] = 7;
      ttMoveInput[8][2] = -28;
      ttMoveInput[8][3] = 28;
      ttMoveInput[8][4] = 14;
      ttMoveInput[9][0] = 5;
      ttMoveInput[9][1] = -7;
      ttMoveInput[9][2] = -25;
      ttMoveInput[9][3] = 22;
      ttMoveInput[9][4] = 16;
      ttMoveInput[10][0] = -9;
      ttMoveInput[10][1] = 37;
      ttMoveInput[10][2] = 30;
      ttMoveInput[10][3] = 22;
      ttMoveInput[10][4] = 18;
      ttMoveInput[11][0] = 42;
      ttMoveInput[11][1] = -12;
      ttMoveInput[11][2] = -15;
      ttMoveInput[11][3] = 18;
      ttMoveInput[11][4] = 2;
      ttMoveInput[12][0] = -8;
      ttMoveInput[12][1] = -17;
      ttMoveInput[12][2] = -19;
      ttMoveInput[12][3] = -15;
      ttMoveInput[12][4] = -26;
      ttMoveInput[13][0] = 12;
      ttMoveInput[13][1] = -3;
      ttMoveInput[13][2] = -6;
      ttMoveInput[13][3] = -1;
      ttMoveInput[13][4] = -2;
      ttMoveInput[14][0] = -4;
      ttMoveInput[14][1] = 19;
      ttMoveInput[14][2] = -24;
      ttMoveInput[14][3] = 10;
      ttMoveInput[14][4] = -25;
      ttMoveInput[15][0] = -10;
      ttMoveInput[15][1] = -14;
      ttMoveInput[15][2] = 12;
      ttMoveInput[15][3] = -2;
      ttMoveInput[15][4] = -16;
      ttMoveInput[16][0] = -21;
      ttMoveInput[16][1] = -16;
      ttMoveInput[16][2] = -1;
      ttMoveInput[16][3] = 4;
      ttMoveInput[16][4] = 12;
      ttMoveInput[17][0] = -28;
      ttMoveInput[17][1] = -6;
      ttMoveInput[17][2] = -9;
      ttMoveInput[17][3] = 1;
      ttMoveInput[17][4] = -33;
      ttMoveInput[18][0] = -2;
      ttMoveInput[18][1] = 9;
      ttMoveInput[18][2] = -2;
      ttMoveInput[18][3] = -9;
      ttMoveInput[18][4] = 37;
      ttMoveInput[19][0] = 19;
      ttMoveInput[19][1] = -4;
      ttMoveInput[19][2] = 22;
      ttMoveInput[19][3] = 4;
      ttMoveInput[19][4] = -4;
      ttMoveInput[20][0] = -9;
      ttMoveInput[20][1] = -11;
      ttMoveInput[20][2] = -5;
      ttMoveInput[20][3] = 1;
      ttMoveInput[20][4] = -7;
      ttMoveInput[21][0] = -5;
      ttMoveInput[21][1] = -27;
      ttMoveInput[21][2] = 6;
      ttMoveInput[21][3] = 4;
      ttMoveInput[21][4] = -21;
      ttMoveInput[22][0] = 37;
      ttMoveInput[22][1] = -8;
      ttMoveInput[22][2] = -6;
      ttMoveInput[22][3] = -5;
      ttMoveInput[22][4] = 38;
      ttMoveInput[23][0] = 3;
      ttMoveInput[23][1] = -1;
      ttMoveInput[23][2] = 11;
      ttMoveInput[23][3] = -16;
      ttMoveInput[23][4] = -5;
      statScoreInput[0] = 15;
      statScoreInput[1] = -8;
      statScoreInput[2] = -2;
      statScoreInput[3] = 19;
      statScoreInput[4] = 8;
      statScoreInput[5] = 32;
      statScoreInput[6] = -8;
      statScoreInput[7] = 21;
      statScoreInput[8] = 11;
      statScoreInput[9] = -10;
      statScoreInput[10] = -4;
      statScoreInput[11] = 19;
      statScoreInput[12] = 7;
      statScoreInput[13] = 23;
      statScoreInput[14] = -14;
      statScoreInput[15] = 17;
      statScoreInput[16] = -25;
      statScoreInput[17] = -23;
      statScoreInput[18] = 23;
      statScoreInput[19] = 20;
      statScoreInput[20] = -9;
      statScoreInput[21] = 4;
      statScoreInput[22] = 4;
      statScoreInput[23] = 15;
      biases[0][0] = 5;
      biases[0][1] = -26;
      biases[0][2] = 3;
      biases[0][3] = -2;
      biases[0][4] = -13;
      biases[0][5] = 11;
      biases[0][6] = 16;
      biases[0][7] = -1;
      biases[0][8] = -21;
      biases[0][9] = -11;
      biases[0][10] = 2;
      biases[0][11] = 17;
      biases[0][12] = 17;
      biases[0][13] = -20;
      biases[0][14] = -26;
      biases[0][15] = 19;
      biases[0][16] = 30;
      biases[0][17] = 9;
      biases[0][18] = 6;
      biases[0][19] = -3;
      biases[0][20] = -13;
      biases[0][21] = 8;
      biases[0][22] = -6;
      biases[0][23] = 14;
      biases[1][0] = 14;
      biases[1][1] = -26;
      biases[1][2] = 4;
      biases[1][3] = 5;
      biases[1][4] = -3;
      biases[1][5] = 9;
      biases[1][6] = -19;
      biases[1][7] = -6;
      biases[1][8] = 34;
      biases[1][9] = 1;
      biases[1][10] = 20;
      biases[1][11] = 10;
      biases[1][12] = 4;
      biases[1][13] = 3;
      biases[1][14] = -19;
      biases[1][15] = -22;
      biases[1][16] = -2;
      biases[1][17] = 1;
      biases[1][18] = 6;
      biases[1][19] = 8;
      biases[1][20] = 3;
      biases[1][21] = -28;
      biases[1][22] = 15;
      biases[1][23] = -23;
      outputBias[0] = 59;
      outputBias[1] = 45;
      slopes[0][0][0] = 9;
      slopes[0][0][1] = 5;
      slopes[0][0][2] = 0;
      slopes[0][0][3] = 22;
      slopes[0][0][4] = 3;
      slopes[0][0][5] = 13;
      slopes[0][0][6] = 12;
      slopes[0][0][7] = 3;
      slopes[0][0][8] = 26;
      slopes[0][0][9] = 5;
      slopes[0][0][10] = 4;
      slopes[0][0][11] = 42;
      slopes[0][0][12] = 18;
      slopes[0][0][13] = 4;
      slopes[0][0][14] = 2;
      slopes[0][0][15] = 6;
      slopes[0][0][16] = 6;
      slopes[0][0][17] = 11;
      slopes[0][0][18] = 13;
      slopes[0][0][19] = 0;
      slopes[0][0][20] = 18;
      slopes[0][0][21] = 4;
      slopes[0][0][22] = 12;
      slopes[0][0][23] = 3;
      slopes[0][1][0] = 20;
      slopes[0][1][1] = 17;
      slopes[0][1][2] = 10;
      slopes[0][1][3] = 19;
      slopes[0][1][4] = 27;
      slopes[0][1][5] = 5;
      slopes[0][1][6] = 35;
      slopes[0][1][7] = 31;
      slopes[0][1][8] = 10;
      slopes[0][1][9] = 16;
      slopes[0][1][10] = 31;
      slopes[0][1][11] = 6;
      slopes[0][1][12] = 1;
      slopes[0][1][13] = 1;
      slopes[0][1][14] = 0;
      slopes[0][1][15] = 25;
      slopes[0][1][16] = 6;
      slopes[0][1][17] = 11;
      slopes[0][1][18] = 21;
      slopes[0][1][19] = 33;
      slopes[0][1][20] = 4;
      slopes[0][1][21] = 1;
      slopes[0][1][22] = 7;
      slopes[0][1][23] = 7;
      slopes[1][0][0] = 3;
      slopes[1][0][1] = 5;
      slopes[1][0][2] = 16;
      slopes[1][0][3] = 7;
      slopes[1][0][4] = 1;
      slopes[1][0][5] = 5;
      slopes[1][0][6] = 23;
      slopes[1][0][7] = 13;
      slopes[1][0][8] = 2;
      slopes[1][0][9] = 14;
      slopes[1][0][10] = 3;
      slopes[1][0][11] = 11;
      slopes[1][0][12] = 0;
      slopes[1][0][13] = 7;
      slopes[1][0][14] = 18;
      slopes[1][0][15] = 23;
      slopes[1][0][16] = 22;
      slopes[1][0][17] = 3;
      slopes[1][0][18] = 17;
      slopes[1][0][19] = 14;
      slopes[1][0][20] = 0;
      slopes[1][0][21] = 18;
      slopes[1][0][22] = 15;
      slopes[1][0][23] = 15;
      slopes[1][1][0] = 8;
      slopes[1][1][1] = 9;
      slopes[1][1][2] = 8;
      slopes[1][1][3] = 1;
      slopes[1][1][4] = 12;
      slopes[1][1][5] = 19;
      slopes[1][1][6] = 10;
      slopes[1][1][7] = 15;
      slopes[1][1][8] = 7;
      slopes[1][1][9] = 11;
      slopes[1][1][10] = 32;
      slopes[1][1][11] = 5;
      slopes[1][1][12] = 40;
      slopes[1][1][13] = 5;
      slopes[1][1][14] = 9;
      slopes[1][1][15] = 4;
      slopes[1][1][16] = 22;
      slopes[1][1][17] = 9;
      slopes[1][1][18] = 0;
      slopes[1][1][19] = 17;
      slopes[1][1][20] = 30;
      slopes[1][1][21] = 9;
      slopes[1][1][22] = 18;
      slopes[1][1][23] = 18;
      outputSlopes[0][0] = 1038;
      outputSlopes[0][1] = 1035;
      outputSlopes[1][0] = 1018;
      outputSlopes[1][1] = 1033;
      lmrDepthScale = 1021;
      lmrDepthScaleTwo = 931;
      ttMoveCutNodeScale = 3827;
      depthReductionDecreaseThres = 4667;
      LMRDepthReductionThres = -3770;
  }

  int PReLU(int input, int negativeSlope, int positiveSlope) {
      int output = 0;
      if (input >= 0)
          output = input * positiveSlope / 1024;
      else
          output = input * negativeSlope / 1024;
      return output;
  }

  int calculateFinalLayers(bool W_IN[9], int depth, int singular, int statScore, int nodeType, int ttValue, int ttMove, int n) {
      int outputSum = 0;
      for (int i = 0; i < 24; i++) {
          int sum = 0;
          for (int j = 0; j < 9; j++) {
              sum += inputScales[i][j][W_IN[j]];
          }
          sum += depthInput[i][depth] + singularInput[i][singular] + nodeTypeInput[i][nodeType]
              + ttValueInput[i][ttValue] + ttMoveInput[i][ttMove]
              + statScoreInput[i] * statScore;
          outputSum += PReLU(sum + biases[n][i], slopes[n][0][i], slopes[n][1][i]);
      }
      return PReLU(outputSum + outputBias[n], outputSlopes[n][0], outputSlopes[n][1]);
  }

  int Store[2][2][2][2][2][2][2][2][2][2][5][3][3][5][4][15];

  int Lookup(bool W_IN[9], int depth, int singular, int statScore, int nodeType, int ttValue, int ttMove, int n) {
      if (Store[n][W_IN[0]][W_IN[1]][W_IN[2]][W_IN[3]][W_IN[4]][W_IN[5]][W_IN[6]][W_IN[7]][W_IN[8]][ttMove]
          [ttValue][nodeType][depth][singular][statScore] == 0) {
          Store[n][W_IN[0]][W_IN[1]][W_IN[2]][W_IN[3]][W_IN[4]][W_IN[5]][W_IN[6]][W_IN[7]][W_IN[8]][ttMove]
              [ttValue][nodeType][depth][singular][statScore] = calculateFinalLayers(W_IN, depth, singular, statScore, nodeType, ttValue, ttMove, n);
      }
      return Store[n][W_IN[0]][W_IN[1]][W_IN[2]][W_IN[3]][W_IN[4]][W_IN[5]][W_IN[6]][W_IN[7]][W_IN[8]][ttMove]
          [ttValue][nodeType][depth][singular][statScore];
  }

  constexpr int futility_move_count(bool improving, Depth depth) {
    return improving ? (3 + depth * depth)
                     : (3 + depth * depth) / 2;
  }

  // History and stats update bonus, based on depth
  int stat_bonus(Depth d) {
    return std::min(336 * d - 547, 1561);
  }

  // Add a small random component to draw evaluations to avoid 3-fold blindness
  Value value_draw(const Thread* thisThread) {
    return VALUE_DRAW - 1 + Value(thisThread->nodes & 0x2);
  }

  // Skill structure is used to implement strength limit. If we have an uci_elo then
  // we convert it to a suitable fractional skill level using anchoring to CCRL Elo
  // (goldfish 1.13 = 2000) and a fit through Ordo derived Elo for a match (TC 60+0.6)
  // results spanning a wide range of k values.
  struct Skill {
    Skill(int skill_level, int uci_elo) {
        if (uci_elo)
        {
            double e = double(uci_elo - 1320) / (3190 - 1320);
            level = std::clamp((((37.2473 * e - 40.8525) * e + 22.2943) * e - 0.311438), 0.0, 19.0);
        }
        else
            level = double(skill_level);
    }
    bool enabled() const { return level < 20.0; }
    bool time_to_pick(Depth depth) const { return depth == 1 + int(level); }
    Move pick_best(size_t multiPV);

    double level;
    Move best = MOVE_NONE;
  };

  template <NodeType nodeType>
  Value search(Position& pos, Stack* ss, Value alpha, Value beta, Depth depth, bool cutNode);

  template <NodeType nodeType>
  Value qsearch(Position& pos, Stack* ss, Value alpha, Value beta, Depth depth = 0);

  Value value_to_tt(Value v, int ply);
  Value value_from_tt(Value v, int ply, int r50c);
  void update_pv(Move* pv, Move move, const Move* childPv);
  void update_continuation_histories(Stack* ss, Piece pc, Square to, int bonus);
  void update_quiet_stats(const Position& pos, Stack* ss, Move move, int bonus);
  void update_all_stats(const Position& pos, Stack* ss, Move bestMove, Value bestValue, Value beta, Square prevSq,
                        Move* quietsSearched, int quietCount, Move* capturesSearched, int captureCount, Depth depth);

  // perft() is our utility to verify move generation. All the leaf nodes up
  // to the given depth are generated and counted, and the sum is returned.
  template<bool Root>
  uint64_t perft(Position& pos, Depth depth) {

    StateInfo st;
    ASSERT_ALIGNED(&st, Eval::NNUE::CacheLineSize);

    uint64_t cnt, nodes = 0;
    const bool leaf = (depth == 2);

    for (const auto& m : MoveList<LEGAL>(pos))
    {
        if (Root && depth <= 1)
            cnt = 1, nodes++;
        else
        {
            pos.do_move(m, st);
            cnt = leaf ? MoveList<LEGAL>(pos).size() : perft<false>(pos, depth - 1);
            nodes += cnt;
            pos.undo_move(m);
        }
        if (Root)
            sync_cout << UCI::move(m, pos.is_chess960()) << ": " << cnt << sync_endl;
    }
    return nodes;
  }

} // namespace


/// Search::init() is called at startup to initialize various lookup tables

void Search::init() {

  for (int i = 1; i < MAX_MOVES; ++i)
      Reductions[i] = int((20.57 + std::log(Threads.size()) / 2) * std::log(i));
  SetValues();
}


/// Search::clear() resets search state to its initial value

void Search::clear() {

  Threads.main()->wait_for_search_finished();

  Time.availableNodes = 0;
  TT.clear();
  Threads.clear();
  Tablebases::init(Options["SyzygyPath"]); // Free mapped files
}


/// MainThread::search() is started when the program receives the UCI 'go'
/// command. It searches from the root position and outputs the "bestmove".

void MainThread::search() {

  if (Limits.perft)
  {
      nodes = perft<true>(rootPos, Limits.perft);
      sync_cout << "\nNodes searched: " << nodes << "\n" << sync_endl;
      return;
  }

  Color us = rootPos.side_to_move();
  Time.init(Limits, us, rootPos.game_ply());
  TT.new_search();

  Eval::NNUE::verify();

  if (rootMoves.empty())
  {
      rootMoves.emplace_back(MOVE_NONE);
      sync_cout << "info depth 0 score "
                << UCI::value(rootPos.checkers() ? -VALUE_MATE : VALUE_DRAW)
                << sync_endl;
  }
  else
  {
      Threads.start_searching(); // start non-main threads
      Thread::search();          // main thread start searching
  }

  // When we reach the maximum depth, we can arrive here without a raise of
  // Threads.stop. However, if we are pondering or in an infinite search,
  // the UCI protocol states that we shouldn't print the best move before the
  // GUI sends a "stop" or "ponderhit" command. We therefore simply wait here
  // until the GUI sends one of those commands.

  while (!Threads.stop && (ponder || Limits.infinite))
  {} // Busy wait for a stop or a ponder reset

  // Stop the threads if not already stopped (also raise the stop if
  // "ponderhit" just reset Threads.ponder).
  Threads.stop = true;

  // Wait until all threads have finished
  Threads.wait_for_search_finished();

  // When playing in 'nodes as time' mode, subtract the searched nodes from
  // the available ones before exiting.
  if (Limits.npmsec)
      Time.availableNodes += Limits.inc[us] - Threads.nodes_searched();

  Thread* bestThread = this;
  Skill skill = Skill(Options["Skill Level"], Options["UCI_LimitStrength"] ? int(Options["UCI_Elo"]) : 0);

  if (   int(Options["MultiPV"]) == 1
      && !Limits.depth
      && !skill.enabled()
      && rootMoves[0].pv[0] != MOVE_NONE)
      bestThread = Threads.get_best_thread();

  bestPreviousScore = bestThread->rootMoves[0].score;
  bestPreviousAverageScore = bestThread->rootMoves[0].averageScore;

  // Send again PV info if we have a new best thread
  if (bestThread != this)
      sync_cout << UCI::pv(bestThread->rootPos, bestThread->completedDepth) << sync_endl;

  sync_cout << "bestmove " << UCI::move(bestThread->rootMoves[0].pv[0], rootPos.is_chess960());

  if (bestThread->rootMoves[0].pv.size() > 1 || bestThread->rootMoves[0].extract_ponder_from_tt(rootPos))
      std::cout << " ponder " << UCI::move(bestThread->rootMoves[0].pv[1], rootPos.is_chess960());

  std::cout << sync_endl;
}


/// Thread::search() is the main iterative deepening loop. It calls search()
/// repeatedly with increasing depth until the allocated thinking time has been
/// consumed, the user stops the search, or the maximum search depth is reached.

void Thread::search() {

  // To allow access to (ss-7) up to (ss+2), the stack must be oversized.
  // The former is needed to allow update_continuation_histories(ss-1, ...),
  // which accesses its argument at ss-6, also near the root.
  // The latter is needed for statScore and killer initialization.
  Stack stack[MAX_PLY+10], *ss = stack+7;
  Move  pv[MAX_PLY+1];
  Value alpha, beta, delta;
  Move  lastBestMove = MOVE_NONE;
  Depth lastBestMoveDepth = 0;
  MainThread* mainThread = (this == Threads.main() ? Threads.main() : nullptr);
  double timeReduction = 1, totBestMoveChanges = 0;
  Color us = rootPos.side_to_move();
  int iterIdx = 0;

  std::memset(ss-7, 0, 10 * sizeof(Stack));
  for (int i = 7; i > 0; --i)
  {
      (ss-i)->continuationHistory = &this->continuationHistory[0][0][NO_PIECE][0]; // Use as a sentinel
      (ss-i)->staticEval = VALUE_NONE;
  }

  for (int i = 0; i <= MAX_PLY + 2; ++i)
      (ss+i)->ply = i;

  ss->pv = pv;

  bestValue = -VALUE_INFINITE;

  if (mainThread)
  {
      if (mainThread->bestPreviousScore == VALUE_INFINITE)
          for (int i = 0; i < 4; ++i)
              mainThread->iterValue[i] = VALUE_ZERO;
      else
          for (int i = 0; i < 4; ++i)
              mainThread->iterValue[i] = mainThread->bestPreviousScore;
  }

  size_t multiPV = size_t(Options["MultiPV"]);
  Skill skill(Options["Skill Level"], Options["UCI_LimitStrength"] ? int(Options["UCI_Elo"]) : 0);

  // When playing with strength handicap enable MultiPV search that we will
  // use behind-the-scenes to retrieve a set of possible moves.
  if (skill.enabled())
      multiPV = std::max(multiPV, (size_t)4);

  multiPV = std::min(multiPV, rootMoves.size());

  int searchAgainCounter = 0;

  // Iterative deepening loop until requested to stop or the target depth is reached
  while (   ++rootDepth < MAX_PLY
         && !Threads.stop
         && !(Limits.depth && mainThread && rootDepth > Limits.depth))
  {
      // Age out PV variability metric
      if (mainThread)
          totBestMoveChanges /= 2;

      // Save the last iteration's scores before the first PV line is searched and
      // all the move scores except the (new) PV are set to -VALUE_INFINITE.
      for (RootMove& rm : rootMoves)
          rm.previousScore = rm.score;

      size_t pvFirst = 0;
      pvLast = 0;

      if (!Threads.increaseDepth)
          searchAgainCounter++;

      // MultiPV loop. We perform a full root search for each PV line
      for (pvIdx = 0; pvIdx < multiPV && !Threads.stop; ++pvIdx)
      {
          if (pvIdx == pvLast)
          {
              pvFirst = pvLast;
              for (pvLast++; pvLast < rootMoves.size(); pvLast++)
                  if (rootMoves[pvLast].tbRank != rootMoves[pvFirst].tbRank)
                      break;
          }

          // Reset UCI info selDepth for each depth and each PV line
          selDepth = 0;

          // Reset aspiration window starting size
          Value prev = rootMoves[pvIdx].averageScore;
          delta = Value(10) + int(prev) * prev / 15799;
          alpha = std::max(prev - delta,-VALUE_INFINITE);
          beta  = std::min(prev + delta, VALUE_INFINITE);

          // Adjust optimism based on root move's previousScore
          int opt = 109 * prev / (std::abs(prev) + 141);
          optimism[ us] = Value(opt);
          optimism[~us] = -optimism[us];

          // Start with a small aspiration window and, in the case of a fail
          // high/low, re-search with a bigger window until we don't fail
          // high/low anymore.
          int failedHighCnt = 0;
          while (true)
          {
              // Adjust the effective depth searched, but ensure at least one effective increment for every
              // four searchAgain steps (see issue #2717).
              Depth adjustedDepth = std::max(1, rootDepth - failedHighCnt - 3 * (searchAgainCounter + 1) / 4);
              bestValue = Stockfish::search<Root>(rootPos, ss, alpha, beta, adjustedDepth, false);

              // Bring the best move to the front. It is critical that sorting
              // is done with a stable algorithm because all the values but the
              // first and eventually the new best one is set to -VALUE_INFINITE
              // and we want to keep the same order for all the moves except the
              // new PV that goes to the front. Note that in the case of MultiPV
              // search the already searched PV lines are preserved.
              std::stable_sort(rootMoves.begin() + pvIdx, rootMoves.begin() + pvLast);

              // If search has been stopped, we break immediately. Sorting is
              // safe because RootMoves is still valid, although it refers to
              // the previous iteration.
              if (Threads.stop)
                  break;

              // When failing high/low give some update (without cluttering
              // the UI) before a re-search.
              if (   mainThread
                  && multiPV == 1
                  && (bestValue <= alpha || bestValue >= beta)
                  && Time.elapsed() > 3000)
                  sync_cout << UCI::pv(rootPos, rootDepth) << sync_endl;

              // In case of failing low/high increase aspiration window and
              // re-search, otherwise exit the loop.
              if (bestValue <= alpha)
              {
                  beta = (alpha + beta) / 2;
                  alpha = std::max(bestValue - delta, -VALUE_INFINITE);

                  failedHighCnt = 0;
                  if (mainThread)
                      mainThread->stopOnPonderhit = false;
              }
              else if (bestValue >= beta)
              {
                  beta = std::min(bestValue + delta, VALUE_INFINITE);
                  ++failedHighCnt;
              }
              else
                  break;

              delta += delta / 3;

              assert(alpha >= -VALUE_INFINITE && beta <= VALUE_INFINITE);
          }

          // Sort the PV lines searched so far and update the GUI
          std::stable_sort(rootMoves.begin() + pvFirst, rootMoves.begin() + pvIdx + 1);

          if (    mainThread
              && (Threads.stop || pvIdx + 1 == multiPV || Time.elapsed() > 3000))
              sync_cout << UCI::pv(rootPos, rootDepth) << sync_endl;
      }

      if (!Threads.stop)
          completedDepth = rootDepth;

      if (rootMoves[0].pv[0] != lastBestMove)
      {
          lastBestMove = rootMoves[0].pv[0];
          lastBestMoveDepth = rootDepth;
      }

      // Have we found a "mate in x"?
      if (   Limits.mate
          && bestValue >= VALUE_MATE_IN_MAX_PLY
          && VALUE_MATE - bestValue <= 2 * Limits.mate)
          Threads.stop = true;

      if (!mainThread)
          continue;

      // If the skill level is enabled and time is up, pick a sub-optimal best move
      if (skill.enabled() && skill.time_to_pick(rootDepth))
          skill.pick_best(multiPV);

      // Use part of the gained time from a previous stable move for the current move
      for (Thread* th : Threads)
      {
          totBestMoveChanges += th->bestMoveChanges;
          th->bestMoveChanges = 0;
      }

      // Do we have time for the next iteration? Can we stop searching now?
      if (    Limits.use_time_management()
          && !Threads.stop
          && !mainThread->stopOnPonderhit)
      {
          double fallingEval = (69 + 13 * (mainThread->bestPreviousAverageScore - bestValue)
                                    +  6 * (mainThread->iterValue[iterIdx] - bestValue)) / 619.6;
          fallingEval = std::clamp(fallingEval, 0.5, 1.5);

          // If the bestMove is stable over several iterations, reduce time accordingly
          timeReduction = lastBestMoveDepth + 8 < completedDepth ? 1.57 : 0.65;
          double reduction = (1.4 + mainThread->previousTimeReduction) / (2.08 * timeReduction);
          double bestMoveInstability = 1 + 1.8 * totBestMoveChanges / Threads.size();

          double totalTime = Time.optimum() * fallingEval * reduction * bestMoveInstability;

          // Cap used time in case of a single legal move for a better viewer experience in tournaments
          // yielding correct scores and sufficiently fast moves.
          if (rootMoves.size() == 1)
              totalTime = std::min(500.0, totalTime);

          // Stop the search if we have exceeded the totalTime
          if (Time.elapsed() > totalTime)
          {
              // If we are allowed to ponder do not stop the search now but
              // keep pondering until the GUI sends "ponderhit" or "stop".
              if (mainThread->ponder)
                  mainThread->stopOnPonderhit = true;
              else
                  Threads.stop = true;
          }
          else if (   !mainThread->ponder
                   && Time.elapsed() > totalTime * 0.50)
              Threads.increaseDepth = false;
          else
              Threads.increaseDepth = true;
      }

      mainThread->iterValue[iterIdx] = bestValue;
      iterIdx = (iterIdx + 1) & 3;
  }

  if (!mainThread)
      return;

  mainThread->previousTimeReduction = timeReduction;

  // If the skill level is enabled, swap the best PV line with the sub-optimal one
  if (skill.enabled())
      std::swap(rootMoves[0], *std::find(rootMoves.begin(), rootMoves.end(),
                skill.best ? skill.best : skill.pick_best(multiPV)));
}


namespace {

  // search<>() is the main search function for both PV and non-PV nodes

  template <NodeType nodeType>
  Value search(Position& pos, Stack* ss, Value alpha, Value beta, Depth depth, bool cutNode) {

    constexpr bool PvNode = nodeType != NonPV;
    constexpr bool rootNode = nodeType == Root;

    // Check if we have an upcoming move that draws by repetition, or
    // if the opponent had an alternative move earlier to this position.
    if (   !rootNode
        && pos.rule50_count() >= 3
        && alpha < VALUE_DRAW
        && pos.has_game_cycle(ss->ply))
    {
        alpha = value_draw(pos.this_thread());
        if (alpha >= beta)
            return alpha;
    }

    // Dive into quiescence search when the depth reaches zero
    if (depth <= 0)
        return qsearch<PvNode ? PV : NonPV>(pos, ss, alpha, beta);

    assert(-VALUE_INFINITE <= alpha && alpha < beta && beta <= VALUE_INFINITE);
    assert(PvNode || (alpha == beta - 1));
    assert(0 < depth && depth < MAX_PLY);
    assert(!(PvNode && cutNode));

    Move pv[MAX_PLY+1], capturesSearched[32], quietsSearched[64];
    StateInfo st;
    ASSERT_ALIGNED(&st, Eval::NNUE::CacheLineSize);

    TTEntry* tte;
    Key posKey;
    Move ttMove, move, excludedMove, bestMove;
    Depth extension, initialDepth, newDepth;
    Value bestValue, value, ttValue, eval, maxValue, probCutBeta;
    bool givesCheck, improving, priorCapture, singularQuietLMR;
    bool capture, moveCountPruning, ttCapture;
    Piece movedPiece;
    int moveCount, captureCount, quietCount;

    // Step 1. Initialize node
    Thread* thisThread = pos.this_thread();
    ss->inCheck        = pos.checkers();
    priorCapture       = pos.captured_piece();
    Color us           = pos.side_to_move();
    moveCount          = captureCount = quietCount = ss->moveCount = 0;
    bestValue          = -VALUE_INFINITE;
    maxValue           = VALUE_INFINITE;

    // Check for the available remaining time
    if (thisThread == Threads.main())
        static_cast<MainThread*>(thisThread)->check_time();

    // Used to send selDepth info to GUI (selDepth counts from 1, ply from 0)
    if (PvNode && thisThread->selDepth < ss->ply + 1)
        thisThread->selDepth = ss->ply + 1;

    if (!rootNode)
    {
        // Step 2. Check for aborted search and immediate draw
        if (   Threads.stop.load(std::memory_order_relaxed)
            || pos.is_draw(ss->ply)
            || ss->ply >= MAX_PLY)
            return (ss->ply >= MAX_PLY && !ss->inCheck) ? evaluate(pos)
                                                        : value_draw(pos.this_thread());

        // Step 3. Mate distance pruning. Even if we mate at the next move our score
        // would be at best mate_in(ss->ply+1), but if alpha is already bigger because
        // a shorter mate was found upward in the tree then there is no need to search
        // because we will never beat the current alpha. Same logic but with reversed
        // signs apply also in the opposite condition of being mated instead of giving
        // mate. In this case, return a fail-high score.
        alpha = std::max(mated_in(ss->ply), alpha);
        beta = std::min(mate_in(ss->ply+1), beta);
        if (alpha >= beta)
            return alpha;
    }
    else
        thisThread->rootDelta = beta - alpha;

    assert(0 <= ss->ply && ss->ply < MAX_PLY);

    (ss+1)->excludedMove = bestMove = MOVE_NONE;
    (ss+2)->killers[0]   = (ss+2)->killers[1] = MOVE_NONE;
    (ss+2)->cutoffCnt    = 0;
    ss->doubleExtensions = (ss-1)->doubleExtensions;
    Square prevSq        = is_ok((ss-1)->currentMove) ? to_sq((ss-1)->currentMove) : SQ_NONE;
    ss->statScore        = 0;

    // Step 4. Transposition table lookup.
    excludedMove = ss->excludedMove;
    posKey = pos.key();
    tte = TT.probe(posKey, ss->ttHit);
    ttValue = ss->ttHit ? value_from_tt(tte->value(), ss->ply, pos.rule50_count()) : VALUE_NONE;
    ttMove =  rootNode ? thisThread->rootMoves[thisThread->pvIdx].pv[0]
            : ss->ttHit    ? tte->move() : MOVE_NONE;
    ttCapture = ttMove && pos.capture_stage(ttMove);

    // At this point, if excluded, skip straight to step 6, static eval. However,
    // to save indentation, we list the condition in all code between here and there.
    if (!excludedMove)
        ss->ttPv = PvNode || (ss->ttHit && tte->is_pv());

    // At non-PV nodes we check for an early TT cutoff
    if (  !PvNode
        && !excludedMove
        && tte->depth() > depth
        && ttValue != VALUE_NONE // Possible in case of TT access race or if !ttHit
        && (tte->bound() & (ttValue >= beta ? BOUND_LOWER : BOUND_UPPER)))
    {
        // If ttMove is quiet, update move sorting heuristics on TT hit (~2 Elo)
        if (ttMove)
        {
            if (ttValue >= beta)
            {
                // Bonus for a quiet ttMove that fails high (~2 Elo)
                if (!ttCapture)
                    update_quiet_stats(pos, ss, ttMove, stat_bonus(depth));

                // Extra penalty for early quiet moves of the previous ply (~0 Elo on STC, ~2 Elo on LTC)
                if (prevSq != SQ_NONE && (ss-1)->moveCount <= 2 && !priorCapture)
                    update_continuation_histories(ss-1, pos.piece_on(prevSq), prevSq, -stat_bonus(depth + 1));
            }
            // Penalty for a quiet ttMove that fails low (~1 Elo)
            else if (!ttCapture)
            {
                int penalty = -stat_bonus(depth);
                thisThread->mainHistory[us][from_to(ttMove)] << penalty;
                update_continuation_histories(ss, pos.moved_piece(ttMove), to_sq(ttMove), penalty);
            }
        }

        // Partial workaround for the graph history interaction problem
        // For high rule50 counts don't produce transposition table cutoffs.
        if (pos.rule50_count() < 90)
            return ttValue;
    }

    // Step 5. Tablebases probe
    if (!rootNode && !excludedMove && TB::Cardinality)
    {
        int piecesCount = pos.count<ALL_PIECES>();

        if (    piecesCount <= TB::Cardinality
            && (piecesCount <  TB::Cardinality || depth >= TB::ProbeDepth)
            &&  pos.rule50_count() == 0
            && !pos.can_castle(ANY_CASTLING))
        {
            TB::ProbeState err;
            TB::WDLScore wdl = Tablebases::probe_wdl(pos, &err);

            // Force check of time on the next occasion
            if (thisThread == Threads.main())
                static_cast<MainThread*>(thisThread)->callsCnt = 0;

            if (err != TB::ProbeState::FAIL)
            {
                thisThread->tbHits.fetch_add(1, std::memory_order_relaxed);

                int drawScore = TB::UseRule50 ? 1 : 0;

                // use the range VALUE_MATE_IN_MAX_PLY to VALUE_TB_WIN_IN_MAX_PLY to score
                value =  wdl < -drawScore ? VALUE_MATED_IN_MAX_PLY + ss->ply + 1
                       : wdl >  drawScore ? VALUE_MATE_IN_MAX_PLY - ss->ply - 1
                                          : VALUE_DRAW + 2 * wdl * drawScore;

                Bound b =  wdl < -drawScore ? BOUND_UPPER
                         : wdl >  drawScore ? BOUND_LOWER : BOUND_EXACT;

                if (    b == BOUND_EXACT
                    || (b == BOUND_LOWER ? value >= beta : value <= alpha))
                {
                    tte->save(posKey, value_to_tt(value, ss->ply), ss->ttPv, b,
                              std::min(MAX_PLY - 1, depth + 6),
                              MOVE_NONE, VALUE_NONE);

                    return value;
                }

                if (PvNode)
                {
                    if (b == BOUND_LOWER)
                        bestValue = value, alpha = std::max(alpha, bestValue);
                    else
                        maxValue = value;
                }
            }
        }
    }

    CapturePieceToHistory& captureHistory = thisThread->captureHistory;

    // Step 6. Static evaluation of the position
    if (ss->inCheck)
    {
        // Skip early pruning when in check
        ss->staticEval = eval = VALUE_NONE;
        improving = false;
        goto moves_loop;
    }
    else if (excludedMove)
    {
        // Providing the hint that this node's accumulator will be used often brings significant Elo gain (13 Elo)
        Eval::NNUE::hint_common_parent_position(pos);
        eval = ss->staticEval;
    }
    else if (ss->ttHit)
    {
        // Never assume anything about values stored in TT
        ss->staticEval = eval = tte->eval();
        if (eval == VALUE_NONE)
            ss->staticEval = eval = evaluate(pos);
        else if (PvNode)
            Eval::NNUE::hint_common_parent_position(pos);

        // ttValue can be used as a better position evaluation (~7 Elo)
        if (    ttValue != VALUE_NONE
            && (tte->bound() & (ttValue > eval ? BOUND_LOWER : BOUND_UPPER)))
            eval = ttValue;
    }
    else
    {
        ss->staticEval = eval = evaluate(pos);
        // Save static evaluation into the transposition table
        tte->save(posKey, VALUE_NONE, ss->ttPv, BOUND_NONE, DEPTH_NONE, MOVE_NONE, eval);
    }

    // Use static evaluation difference to improve quiet move ordering (~4 Elo)
    if (is_ok((ss-1)->currentMove) && !(ss-1)->inCheck && !priorCapture)
    {
        int bonus = std::clamp(-18 * int((ss-1)->staticEval + ss->staticEval), -1817, 1817);
        thisThread->mainHistory[~us][from_to((ss-1)->currentMove)] << bonus;
    }

    // Set up the improving flag, which is true if current static evaluation is
    // bigger than the previous static evaluation at our turn (if we were in
    // check at our previous move we look at static evaluation at move prior to it
    // and if we were in check at move prior to it flag is set to true) and is
    // false otherwise. The improving flag is used in various pruning heuristics.
    improving =   (ss-2)->staticEval != VALUE_NONE ? ss->staticEval > (ss-2)->staticEval
                : (ss-4)->staticEval != VALUE_NONE ? ss->staticEval > (ss-4)->staticEval
                : true;

    // Step 7. Razoring (~1 Elo).
    // If eval is really low check with qsearch if it can exceed alpha, if it can't,
    // return a fail low.
    if (eval < alpha - 456 - 252 * depth * depth)
    {
        value = qsearch<NonPV>(pos, ss, alpha - 1, alpha);
        if (value < alpha)
            return value;
    }

    // Step 8. Futility pruning: child node (~40 Elo).
    // The depth condition is important for mate finding.
    if (   !ss->ttPv
        &&  depth < 9
        &&  eval - futility_margin(depth, cutNode && !ss->ttHit, improving) - (ss-1)->statScore / 306 >= beta
        &&  eval >= beta
        &&  eval < 24923) // larger than VALUE_KNOWN_WIN, but smaller than TB wins
        return eval;

    // Step 9. Null move search with verification search (~35 Elo)
    if (   !PvNode
        && (ss-1)->currentMove != MOVE_NULL
        && (ss-1)->statScore < 17329
        &&  eval >= beta
        &&  eval >= ss->staticEval
        &&  ss->staticEval >= beta - 21 * depth + 258
        && !excludedMove
        &&  pos.non_pawn_material(us)
        &&  ss->ply >= thisThread->nmpMinPly
        &&  beta > VALUE_TB_LOSS_IN_MAX_PLY)
    {
        assert(eval - beta >= 0);

        // Null move dynamic reduction based on depth and eval
        Depth R = std::min(int(eval - beta) / 173, 6) + depth / 3 + 4;

        ss->currentMove = MOVE_NULL;
        ss->continuationHistory = &thisThread->continuationHistory[0][0][NO_PIECE][0];

        pos.do_null_move(st);

        Value nullValue = -search<NonPV>(pos, ss+1, -beta, -beta+1, depth-R, !cutNode);

        pos.undo_null_move();

        if (nullValue >= beta)
        {
            // Do not return unproven mate or TB scores
            nullValue = std::min(nullValue, VALUE_TB_WIN_IN_MAX_PLY-1);

            if (thisThread->nmpMinPly || depth < 14)
                return nullValue;

            assert(!thisThread->nmpMinPly); // Recursive verification is not allowed

            // Do verification search at high depths, with null move pruning disabled
            // until ply exceeds nmpMinPly.
            thisThread->nmpMinPly = ss->ply + 3 * (depth-R) / 4;

            Value v = search<NonPV>(pos, ss, beta-1, beta, depth-R, false);

            thisThread->nmpMinPly = 0;

            if (v >= beta)
                return nullValue;
        }
    }

    // Step 10. If the position doesn't have a ttMove, decrease depth by 2
    // (or by 4 if the TT entry for the current position was hit and the stored depth is greater than or equal to the current depth).
    // Use qsearch if depth is equal or below zero (~9 Elo)
    if (    PvNode
        && !ttMove)
        depth -= 2 + 2 * (ss->ttHit && tte->depth() >= depth);

    if (depth <= 0)
        return qsearch<PV>(pos, ss, alpha, beta);

    if (    cutNode
        &&  depth >= 8
        && !ttMove)
        depth -= 2;

    probCutBeta = beta + 168 - 61 * improving;

    // Step 11. ProbCut (~10 Elo)
    // If we have a good enough capture (or queen promotion) and a reduced search returns a value
    // much above beta, we can (almost) safely prune the previous move.
    if (   !PvNode
        &&  depth > 3
        &&  abs(beta) < VALUE_TB_WIN_IN_MAX_PLY
        // If value from transposition table is lower than probCutBeta, don't attempt probCut
        // there and in further interactions with transposition table cutoff depth is set to depth - 3
        // because probCut search has depth set to depth - 4 but we also do a move before it
        // So effective depth is equal to depth - 3
        && !(   tte->depth() >= depth - 3
             && ttValue != VALUE_NONE
             && ttValue < probCutBeta))
    {
        assert(probCutBeta < VALUE_INFINITE);

        MovePicker mp(pos, ttMove, probCutBeta - ss->staticEval, &captureHistory);

        while ((move = mp.next_move()) != MOVE_NONE)
            if (move != excludedMove && pos.legal(move))
            {
                assert(pos.capture_stage(move));

                ss->currentMove = move;
                ss->continuationHistory = &thisThread->continuationHistory[ss->inCheck]
                                                                          [true]
                                                                          [pos.moved_piece(move)]
                                                                          [to_sq(move)];

                pos.do_move(move, st);

                // Perform a preliminary qsearch to verify that the move holds
                value = -qsearch<NonPV>(pos, ss+1, -probCutBeta, -probCutBeta+1);

                // If the qsearch held, perform the regular search
                if (value >= probCutBeta)
                    value = -search<NonPV>(pos, ss+1, -probCutBeta, -probCutBeta+1, depth - 4, !cutNode);

                pos.undo_move(move);

                if (value >= probCutBeta)
                {
                    // Save ProbCut data into transposition table
                    tte->save(posKey, value_to_tt(value, ss->ply), ss->ttPv, BOUND_LOWER, depth - 3, move, ss->staticEval);
                    return value;
                }
            }

        Eval::NNUE::hint_common_parent_position(pos);
    }

moves_loop: // When in check, search starts here

    // Step 12. A small Probcut idea, when we are in check (~4 Elo)
    probCutBeta = beta + 413;
    if (   ss->inCheck
        && !PvNode
        && ttCapture
        && (tte->bound() & BOUND_LOWER)
        && tte->depth() >= depth - 4
        && ttValue >= probCutBeta
        && abs(ttValue) <= VALUE_KNOWN_WIN
        && abs(beta) <= VALUE_KNOWN_WIN)
        return probCutBeta;

    const PieceToHistory* contHist[] = { (ss-1)->continuationHistory, (ss-2)->continuationHistory,
                                          nullptr                   , (ss-4)->continuationHistory,
                                          nullptr                   , (ss-6)->continuationHistory };

    Move countermove = prevSq != SQ_NONE ? thisThread->counterMoves[pos.piece_on(prevSq)][prevSq] : MOVE_NONE;

    MovePicker mp(pos, ttMove, depth, &thisThread->mainHistory,
                                      &captureHistory,
                                      contHist,
                                      countermove,
                                      ss->killers);

    value = bestValue;
    moveCountPruning = singularQuietLMR = false;

    // Indicate PvNodes that will probably fail low if the node was searched
    // at a depth equal to or greater than the current depth, and the result of this search was a fail low.
    bool likelyFailLow =    PvNode
                         && ttMove
                         && (tte->bound() & BOUND_UPPER)
                         && tte->depth() >= depth;

    // Step 13. Loop through all pseudo-legal moves until no moves remain
    // or a beta cutoff occurs.
    while ((move = mp.next_move(moveCountPruning)) != MOVE_NONE)
    {
      assert(is_ok(move));

      if (move == excludedMove)
          continue;

      // At root obey the "searchmoves" option and skip moves not listed in Root
      // Move List. As a consequence, any illegal move is also skipped. In MultiPV
      // mode we also skip PV moves that have been already searched and those
      // of lower "TB rank" if we are in a TB root position.
      if (rootNode && !std::count(thisThread->rootMoves.begin() + thisThread->pvIdx,
                                  thisThread->rootMoves.begin() + thisThread->pvLast, move))
          continue;

      // Check for legality
      if (!rootNode && !pos.legal(move))
          continue;

      ss->moveCount = ++moveCount;

      if (rootNode && thisThread == Threads.main() && Time.elapsed() > 3000)
          sync_cout << "info depth " << depth
                    << " currmove " << UCI::move(move, pos.is_chess960())
                    << " currmovenumber " << moveCount + thisThread->pvIdx << sync_endl;
      if (PvNode)
          (ss+1)->pv = nullptr;

      extension = 0;
      capture = pos.capture_stage(move);
      movedPiece = pos.moved_piece(move);
      givesCheck = pos.gives_check(move);

      // Calculate new depth for this move
      newDepth = depth - 1;
      initialDepth = depth - 1;

      Value delta = beta - alpha;

      int r = reduction(improving, depth, moveCount, delta, thisThread->rootDelta) * lmrDepthScale;

      // Step 14. Pruning at shallow depth (~120 Elo). Depth conditions are important for mate finding.
      if (  !rootNode
          && pos.non_pawn_material(us)
          && bestValue > VALUE_TB_LOSS_IN_MAX_PLY)
      {
          // Skip quiet moves if movecount exceeds our FutilityMoveCount threshold (~8 Elo)
          moveCountPruning = moveCount >= futility_move_count(improving, depth);

          // Reduced depth of the next LMR search
          int lmrDepth = newDepth - (r / 1024);

          if (   capture
              || givesCheck)
          {
              // Futility pruning for captures (~2 Elo)
              if (   !givesCheck
                  && lmrDepth < 7
                  && !ss->inCheck
                  && ss->staticEval + 197 + 248 * lmrDepth + PieceValue[EG][pos.piece_on(to_sq(move))]
                   + captureHistory[movedPiece][to_sq(move)][type_of(pos.piece_on(to_sq(move)))] / 7 < alpha)
                  continue;

              Bitboard occupied;
              // SEE based pruning (~11 Elo)
              if (!pos.see_ge(move, occupied, Value(-205) * depth))
              {
                 if (depth < 2 - capture)
                    continue;
                 // Don't prune the move if opponent Queen/Rook is under discovered attack after the exchanges
                 // Don't prune the move if opponent King is under discovered attack after or during the exchanges
                 Bitboard leftEnemies = (pos.pieces(~us, KING, QUEEN, ROOK)) & occupied;
                 Bitboard attacks = 0;
                 occupied |= to_sq(move);
                 while (leftEnemies && !attacks)
                 {
                      Square sq = pop_lsb(leftEnemies);
                      attacks |= pos.attackers_to(sq, occupied) & pos.pieces(us) & occupied;
                      // Don't consider pieces that were already threatened/hanging before SEE exchanges
                      if (attacks && (sq != pos.square<KING>(~us) && (pos.attackers_to(sq, pos.pieces()) & pos.pieces(us))))
                         attacks = 0;
                 }
                 if (!attacks)
                    continue;
              }
          }
          else
          {
              int history =   (*contHist[0])[movedPiece][to_sq(move)]
                            + (*contHist[1])[movedPiece][to_sq(move)]
                            + (*contHist[3])[movedPiece][to_sq(move)];

              // Continuation history based pruning (~2 Elo)
              if (   lmrDepth < 6
                  && history < -3832 * depth)
                  continue;

              history += 2 * thisThread->mainHistory[us][from_to(move)];

              lmrDepth += history / 7011;
              lmrDepth = std::max(lmrDepth, -2);

              // Futility pruning: parent node (~13 Elo)
              if (   !ss->inCheck
                  && lmrDepth < 12
                  && ss->staticEval + 112 + 138 * lmrDepth <= alpha)
                  continue;

              lmrDepth = std::max(lmrDepth, 0);

              // Prune moves with negative SEE (~4 Elo)
              if (!pos.see_ge(move, Value(-27 * lmrDepth * lmrDepth - 16 * lmrDepth)))
                  continue;
          }
      }

      // Step 15. Extensions/Reductions (~200 Elo)
      bool W_IN[9] = {};
      int customSingular = 0;

      if (ss->ply < thisThread->rootDepth * 2)
          W_IN[0] = true;

      if (!rootNode
          && depth >= 4 - (thisThread->completedDepth > 22) + 2 * (PvNode && tte->is_pv())
          && move == ttMove
          && !excludedMove
          && abs(ttValue) < VALUE_KNOWN_WIN
          && (tte->bound() & BOUND_LOWER)
          && tte->depth() >= depth - 3)
      {
          W_IN[1] = true; 
      }

      if (W_IN[1] == true && W_IN[0] == true) 
      {
          Value singularBeta = ttValue - (82 + 65 * (ss->ttPv && !PvNode)) * depth / 64;
          Depth singularDepth = (depth - 1) / 2;

          ss->excludedMove = move;
          value = search<NonPV>(pos, ss, singularBeta - 1, singularBeta, singularDepth, cutNode);
          ss->excludedMove = MOVE_NONE;

          customSingular = std::clamp((int(value - singularBeta) + 80) / 20, 1, 3);

          if (value < singularBeta - 21)
              depth += depth < 13;

          if (singularBeta >= beta && value >= singularBeta)
              return singularBeta;
      } 

      int customNodeType = 0;
      
      if (PvNode)
         customNodeType = 1;

      if (cutNode)
          customNodeType = 2;

      int customTTValue = 0;

      if (ttValue >= beta)
          customTTValue = 1;

      if (ttValue <= value)
          customTTValue = 2;

      if (givesCheck)
          W_IN[2] = true;

      if (move == ss->killers[0]
          && (*contHist[0])[movedPiece][to_sq(move)] >= 5168)
          W_IN[3] = true;

      int customTTMove = 0;

      if (ttMove)
          customTTMove = 1;

      if (ttCapture)
          customTTMove = 2;

      if (move == ttMove)
          customTTMove = 3;

      if (move == ttMove && ttCapture)
          customTTMove = 4;

      if ((ss+1)->cutoffCnt >= 4)
          W_IN[4] = true;

      if ((ss-1)->moveCount >= 9)
          W_IN[5] = true;

      if (ss->ttPv && !likelyFailLow)
          W_IN[6] = true;

      if (tte->depth() >= depth + 3)
          W_IN[7] = true;

      if (improving)
          W_IN[8] = true;

      int customDepth = std::clamp(depth / 5, 0, 4);

      ss->statScore = 2 * thisThread->mainHistory[us][from_to(move)]
          + (*contHist[0])[movedPiece][to_sq(move)]
          + (*contHist[1])[movedPiece][to_sq(move)]
          + (*contHist[3])[movedPiece][to_sq(move)]
          - 4006;

      int customStatScore = std::clamp(ss->statScore / 10000, -7, 7) + 7;

      extension = Lookup(W_IN, customDepth, customSingular, customStatScore, customNodeType, customTTValue, customTTMove, 0);
      r = r * lmrDepthScaleTwo / 1024;
      r += Lookup(W_IN, customDepth, customSingular, customStatScore, customNodeType, customTTValue, customTTMove, 1);

      dbg_stdev_of(Lookup(W_IN, customDepth, customSingular, customStatScore, customNodeType, customTTValue, customTTMove, 1), 0);
      dbg_stdev_of(Lookup(W_IN, customDepth, customSingular, customStatScore, customNodeType, customTTValue, customTTMove, 0), 1);

      // Add extension to new depth
      newDepth += extension / 1024;

      // Speculative prefetch as early as possible
      prefetch(TT.first_entry(pos.key_after(move)));

      // Update the current move (this must be done after singular extension search)
      ss->currentMove = move;
      ss->continuationHistory = &thisThread->continuationHistory[ss->inCheck]
                                                                [capture]
                                                                [movedPiece]
                                                                [to_sq(move)];

      // Step 16. Make the move
      pos.do_move(move, st, givesCheck);

      // Step 17. Late moves reduction / extension (LMR, ~117 Elo)
      // We use various heuristics for the sons of a node after the first son has
      // been searched. In general, we would like to reduce them, but there are many
      // cases where we extend a son if it has good chances to be "interesting".
      if (    depth >= 2
          &&  moveCount > 1 + (PvNode && ss->ply <= 1)
          && (   !ss->ttPv
              || !capture
              || (cutNode && (ss-1)->moveCount > 1)))
      {
          // In general we want to cap the LMR depth search at newDepth, but when
          // reduction is negative, we allow this move a limited search extension
          // beyond the first move depth. This may lead to hidden double extensions.
          int totalAdjustment = r - extension;
          Depth d = std::clamp(initialDepth - (totalAdjustment / 1024), 1, newDepth + 1 + (r <= LMRDepthReductionThres));
          value = -search<NonPV>(pos, ss+1, -(alpha+1), -alpha, d, true);

          // Do a full-depth search when reduced LMR search fails high
          if (value > alpha && d < newDepth)
          {
              // Adjust full-depth search based on LMR results - if the result
              // was good enough search deeper, if it was bad enough search shallower
              const bool doDeeperSearch = value > (bestValue + 64 + 11 * (newDepth - d));
              const bool doEvenDeeperSearch = value > alpha + 711 && ss->doubleExtensions <= 6;
              const bool doShallowerSearch = value < bestValue + newDepth;

              ss->doubleExtensions = ss->doubleExtensions + doEvenDeeperSearch;

              newDepth += doDeeperSearch - doShallowerSearch + doEvenDeeperSearch;

              if (newDepth > d)
                  value = -search<NonPV>(pos, ss+1, -(alpha+1), -alpha, newDepth, !cutNode);

              int bonus = value <= alpha ? -stat_bonus(newDepth)
                        : value >= beta  ?  stat_bonus(newDepth)
                                         :  0;

              update_continuation_histories(ss, movedPiece, to_sq(move), bonus);
          }
      }

      // Step 18. Full-depth search when LMR is skipped. If expected reduction is high, reduce its depth by 1.
      else if (!PvNode || moveCount > 1)
      {
          // Increase reduction for cut nodes and not ttMove (~1 Elo)
          if (!ttMove && cutNode)
              r += ttMoveCutNodeScale;

          value = -search<NonPV>(pos, ss+1, -(alpha+1), -alpha, newDepth - (r >= depthReductionDecreaseThres), !cutNode);
      }

      // For PV nodes only, do a full PV search on the first move or after a fail
      // high (in the latter case search only if value < beta), otherwise let the
      // parent node fail low with value <= alpha and try another move.
      if (PvNode && (moveCount == 1 || (value > alpha && (rootNode || value < beta))))
      {
          (ss+1)->pv = pv;
          (ss+1)->pv[0] = MOVE_NONE;

          value = -search<PV>(pos, ss+1, -beta, -alpha, newDepth, false);
      }

      // Step 19. Undo move
      pos.undo_move(move);

      assert(value > -VALUE_INFINITE && value < VALUE_INFINITE);

      // Step 20. Check for a new best move
      // Finished searching the move. If a stop occurred, the return value of
      // the search cannot be trusted, and we return immediately without
      // updating best move, PV and TT.
      if (Threads.stop.load(std::memory_order_relaxed))
          return VALUE_ZERO;

      if (rootNode)
      {
          RootMove& rm = *std::find(thisThread->rootMoves.begin(),
                                    thisThread->rootMoves.end(), move);

          rm.averageScore = rm.averageScore != -VALUE_INFINITE ? (2 * value + rm.averageScore) / 3 : value;

          // PV move or new best move?
          if (moveCount == 1 || value > alpha)
          {
              rm.score =  rm.uciScore = value;
              rm.selDepth = thisThread->selDepth;
              rm.scoreLowerbound = rm.scoreUpperbound = false;

              if (value >= beta)
              {
                  rm.scoreLowerbound = true;
                  rm.uciScore = beta;
              }
              else if (value <= alpha)
              {
                  rm.scoreUpperbound = true;
                  rm.uciScore = alpha;
              }

              rm.pv.resize(1);

              assert((ss+1)->pv);

              for (Move* m = (ss+1)->pv; *m != MOVE_NONE; ++m)
                  rm.pv.push_back(*m);

              // We record how often the best move has been changed in each iteration.
              // This information is used for time management. In MultiPV mode,
              // we must take care to only do this for the first PV line.
              if (   moveCount > 1
                  && !thisThread->pvIdx)
                  ++thisThread->bestMoveChanges;
          }
          else
              // All other moves but the PV, are set to the lowest value: this
              // is not a problem when sorting because the sort is stable and the
              // move position in the list is preserved - just the PV is pushed up.
              rm.score = -VALUE_INFINITE;
      }

      if (value > bestValue)
      {
          bestValue = value;

          if (value > alpha)
          {
              bestMove = move;

              if (PvNode && !rootNode) // Update pv even in fail-high case
                  update_pv(ss->pv, move, (ss+1)->pv);

              if (value >= beta)
              {
                  ss->cutoffCnt += 1 + !ttMove;
                  assert(value >= beta); // Fail high
                  break;
              }
              else
              {
                  // Reduce other moves if we have found at least one score improvement (~2 Elo)
                  if (   depth > 2
                      && depth < 12
                      && beta  <  14362
                      && value > -12393)
                      depth -= 2;

                  assert(depth > 0);
                  alpha = value; // Update alpha! Always alpha < beta
              }
          }
      }


      // If the move is worse than some previously searched move, remember it, to update its stats later
      if (move != bestMove)
      {
          if (capture && captureCount < 32)
              capturesSearched[captureCount++] = move;

          else if (!capture && quietCount < 64)
              quietsSearched[quietCount++] = move;
      }
    }

    // The following condition would detect a stop only after move loop has been
    // completed. But in this case, bestValue is valid because we have fully
    // searched our subtree, and we can anyhow save the result in TT.
    /*
       if (Threads.stop)
        return VALUE_DRAW;
    */

    // Step 21. Check for mate and stalemate
    // All legal moves have been searched and if there are no legal moves, it
    // must be a mate or a stalemate. If we are in a singular extension search then
    // return a fail low score.

    assert(moveCount || !ss->inCheck || excludedMove || !MoveList<LEGAL>(pos).size());

    if (!moveCount)
        bestValue = excludedMove ? alpha :
                    ss->inCheck  ? mated_in(ss->ply)
                                 : VALUE_DRAW;

    // If there is a move that produces search value greater than alpha we update the stats of searched moves
    else if (bestMove)
        update_all_stats(pos, ss, bestMove, bestValue, beta, prevSq,
                         quietsSearched, quietCount, capturesSearched, captureCount, depth);

    // Bonus for prior countermove that caused the fail low
    else if (!priorCapture && prevSq != SQ_NONE)
    {
        int bonus = (depth > 5) + (PvNode || cutNode) + (bestValue < alpha - 113 * depth) + ((ss-1)->moveCount > 12);
        update_continuation_histories(ss-1, pos.piece_on(prevSq), prevSq, stat_bonus(depth) * bonus);
    }

    if (PvNode)
        bestValue = std::min(bestValue, maxValue);

    // If no good move is found and the previous position was ttPv, then the previous
    // opponent move is probably good and the new position is added to the search tree. (~7 Elo)
    if (bestValue <= alpha)
        ss->ttPv = ss->ttPv || ((ss-1)->ttPv && depth > 3);

    // Write gathered information in transposition table
    if (!excludedMove && !(rootNode && thisThread->pvIdx))
        tte->save(posKey, value_to_tt(bestValue, ss->ply), ss->ttPv,
                  bestValue >= beta ? BOUND_LOWER :
                  PvNode && bestMove ? BOUND_EXACT : BOUND_UPPER,
                  depth, bestMove, ss->staticEval);

    assert(bestValue > -VALUE_INFINITE && bestValue < VALUE_INFINITE);

    return bestValue;
  }


  // qsearch() is the quiescence search function, which is called by the main search
  // function with zero depth, or recursively with further decreasing depth per call.
  // (~155 Elo)
  template <NodeType nodeType>
  Value qsearch(Position& pos, Stack* ss, Value alpha, Value beta, Depth depth) {

    static_assert(nodeType != Root);
    constexpr bool PvNode = nodeType == PV;

    assert(alpha >= -VALUE_INFINITE && alpha < beta && beta <= VALUE_INFINITE);
    assert(PvNode || (alpha == beta - 1));
    assert(depth <= 0);

    Move pv[MAX_PLY+1];
    StateInfo st;
    ASSERT_ALIGNED(&st, Eval::NNUE::CacheLineSize);

    TTEntry* tte;
    Key posKey;
    Move ttMove, move, bestMove;
    Depth ttDepth;
    Value bestValue, value, ttValue, futilityValue, futilityBase;
    bool pvHit, givesCheck, capture;
    int moveCount;

    // Step 1. Initialize node
    if (PvNode)
    {
        (ss+1)->pv = pv;
        ss->pv[0] = MOVE_NONE;
    }

    Thread* thisThread = pos.this_thread();
    bestMove = MOVE_NONE;
    ss->inCheck = pos.checkers();
    moveCount = 0;

    // Step 2. Check for an immediate draw or maximum ply reached
    if (   pos.is_draw(ss->ply)
        || ss->ply >= MAX_PLY)
        return (ss->ply >= MAX_PLY && !ss->inCheck) ? evaluate(pos) : VALUE_DRAW;

    assert(0 <= ss->ply && ss->ply < MAX_PLY);

    // Decide whether or not to include checks: this fixes also the type of
    // TT entry depth that we are going to use. Note that in qsearch we use
    // only two types of depth in TT: DEPTH_QS_CHECKS or DEPTH_QS_NO_CHECKS.
    ttDepth = ss->inCheck || depth >= DEPTH_QS_CHECKS ? DEPTH_QS_CHECKS
                                                      : DEPTH_QS_NO_CHECKS;

    // Step 3. Transposition table lookup
    posKey = pos.key();
    tte = TT.probe(posKey, ss->ttHit);
    ttValue = ss->ttHit ? value_from_tt(tte->value(), ss->ply, pos.rule50_count()) : VALUE_NONE;
    ttMove = ss->ttHit ? tte->move() : MOVE_NONE;
    pvHit = ss->ttHit && tte->is_pv();

    // At non-PV nodes we check for an early TT cutoff
    if (  !PvNode
        && tte->depth() >= ttDepth
        && ttValue != VALUE_NONE // Only in case of TT access race or if !ttHit
        && (tte->bound() & (ttValue >= beta ? BOUND_LOWER : BOUND_UPPER)))
        return ttValue;

    // Step 4. Static evaluation of the position
    if (ss->inCheck)
        bestValue = futilityBase = -VALUE_INFINITE;
    else
    {
        if (ss->ttHit)
        {
            // Never assume anything about values stored in TT
            if ((ss->staticEval = bestValue = tte->eval()) == VALUE_NONE)
                ss->staticEval = bestValue = evaluate(pos);

            // ttValue can be used as a better position evaluation (~13 Elo)
            if (    ttValue != VALUE_NONE
                && (tte->bound() & (ttValue > bestValue ? BOUND_LOWER : BOUND_UPPER)))
                bestValue = ttValue;
        }
        else
            // In case of null move search use previous static eval with a different sign
            ss->staticEval = bestValue = (ss-1)->currentMove != MOVE_NULL ? evaluate(pos)
                                                                          : -(ss-1)->staticEval;

        // Stand pat. Return immediately if static value is at least beta
        if (bestValue >= beta)
        {
            // Save gathered info in transposition table
            if (!ss->ttHit)
                tte->save(posKey, value_to_tt(bestValue, ss->ply), false, BOUND_LOWER,
                          DEPTH_NONE, MOVE_NONE, ss->staticEval);

            return bestValue;
        }

        if (bestValue > alpha)
            alpha = bestValue;

        futilityBase = bestValue + 200;
    }

    const PieceToHistory* contHist[] = { (ss-1)->continuationHistory, (ss-2)->continuationHistory,
                                          nullptr                   , (ss-4)->continuationHistory,
                                          nullptr                   , (ss-6)->continuationHistory };

    // Initialize a MovePicker object for the current position, and prepare
    // to search the moves. Because the depth is <= 0 here, only captures,
    // queen promotions, and other checks (only if depth >= DEPTH_QS_CHECKS)
    // will be generated.
    Square prevSq = is_ok((ss-1)->currentMove) ? to_sq((ss-1)->currentMove) : SQ_NONE;
    MovePicker mp(pos, ttMove, depth, &thisThread->mainHistory,
                                      &thisThread->captureHistory,
                                      contHist,
                                      prevSq);

    int quietCheckEvasions = 0;

    // Step 5. Loop through all pseudo-legal moves until no moves remain
    // or a beta cutoff occurs.
    while ((move = mp.next_move()) != MOVE_NONE)
    {
        assert(is_ok(move));

        // Check for legality
        if (!pos.legal(move))
            continue;

        givesCheck = pos.gives_check(move);
        capture = pos.capture_stage(move);

        moveCount++;

        // Step 6. Pruning.
        if (bestValue > VALUE_TB_LOSS_IN_MAX_PLY)
        {
            // Futility pruning and moveCount pruning (~10 Elo)
            if (   !givesCheck
                &&  to_sq(move) != prevSq
                &&  futilityBase > -VALUE_KNOWN_WIN
                &&  type_of(move) != PROMOTION)
            {
                if (moveCount > 2)
                    continue;

                futilityValue = futilityBase + PieceValue[EG][pos.piece_on(to_sq(move))];

                if (futilityValue <= alpha)
                {
                    bestValue = std::max(bestValue, futilityValue);
                    continue;
                }

                if (futilityBase <= alpha && !pos.see_ge(move, VALUE_ZERO + 1))
                {
                    bestValue = std::max(bestValue, futilityBase);
                    continue;
                }
            }

            // We prune after the second quiet check evasion move, where being 'in check' is
            // implicitly checked through the counter, and being a 'quiet move' apart from
            // being a tt move is assumed after an increment because captures are pushed ahead.
            if (quietCheckEvasions > 1)
                break;

            // Continuation history based pruning (~3 Elo)
            if (   !capture
                && (*contHist[0])[pos.moved_piece(move)][to_sq(move)] < 0
                && (*contHist[1])[pos.moved_piece(move)][to_sq(move)] < 0)
                continue;

            // Do not search moves with bad enough SEE values (~5 Elo)
            if (!pos.see_ge(move, Value(-95)))
                continue;
        }

        // Speculative prefetch as early as possible
        prefetch(TT.first_entry(pos.key_after(move)));

        // Update the current move
        ss->currentMove = move;
        ss->continuationHistory = &thisThread->continuationHistory[ss->inCheck]
                                                                  [capture]
                                                                  [pos.moved_piece(move)]
                                                                  [to_sq(move)];

        quietCheckEvasions += !capture && ss->inCheck;

        // Step 7. Make and search the move
        pos.do_move(move, st, givesCheck);
        value = -qsearch<nodeType>(pos, ss+1, -beta, -alpha, depth - 1);
        pos.undo_move(move);

        assert(value > -VALUE_INFINITE && value < VALUE_INFINITE);

        // Step 8. Check for a new best move
        if (value > bestValue)
        {
            bestValue = value;

            if (value > alpha)
            {
                bestMove = move;

                if (PvNode) // Update pv even in fail-high case
                    update_pv(ss->pv, move, (ss+1)->pv);

                if (value < beta) // Update alpha here!
                    alpha = value;
                else
                    break; // Fail high
            }
        }
    }

    // Step 9. Check for mate
    // All legal moves have been searched. A special case: if we're in check
    // and no legal moves were found, it is checkmate.
    if (ss->inCheck && bestValue == -VALUE_INFINITE)
    {
        assert(!MoveList<LEGAL>(pos).size());

        return mated_in(ss->ply); // Plies to mate from the root
    }

    // Save gathered info in transposition table
    tte->save(posKey, value_to_tt(bestValue, ss->ply), pvHit,
              bestValue >= beta ? BOUND_LOWER : BOUND_UPPER,
              ttDepth, bestMove, ss->staticEval);

    assert(bestValue > -VALUE_INFINITE && bestValue < VALUE_INFINITE);

    return bestValue;
  }


  // value_to_tt() adjusts a mate or TB score from "plies to mate from the root" to
  // "plies to mate from the current position". Standard scores are unchanged.
  // The function is called before storing a value in the transposition table.

  Value value_to_tt(Value v, int ply) {

    assert(v != VALUE_NONE);

    return  v >= VALUE_TB_WIN_IN_MAX_PLY  ? v + ply
          : v <= VALUE_TB_LOSS_IN_MAX_PLY ? v - ply : v;
  }


  // value_from_tt() is the inverse of value_to_tt(): it adjusts a mate or TB score
  // from the transposition table (which refers to the plies to mate/be mated from
  // current position) to "plies to mate/be mated (TB win/loss) from the root". However,
  // for mate scores, to avoid potentially false mate scores related to the 50 moves rule
  // and the graph history interaction, we return an optimal TB score instead.

  Value value_from_tt(Value v, int ply, int r50c) {

    if (v == VALUE_NONE)
        return VALUE_NONE;

    if (v >= VALUE_TB_WIN_IN_MAX_PLY)  // TB win or better
    {
        if (v >= VALUE_MATE_IN_MAX_PLY && VALUE_MATE - v > 99 - r50c)
            return VALUE_MATE_IN_MAX_PLY - 1; // do not return a potentially false mate score

        return v - ply;
    }

    if (v <= VALUE_TB_LOSS_IN_MAX_PLY) // TB loss or worse
    {
        if (v <= VALUE_MATED_IN_MAX_PLY && VALUE_MATE + v > 99 - r50c)
            return VALUE_MATED_IN_MAX_PLY + 1; // do not return a potentially false mate score

        return v + ply;
    }

    return v;
  }


  // update_pv() adds current move and appends child pv[]

  void update_pv(Move* pv, Move move, const Move* childPv) {

    for (*pv++ = move; childPv && *childPv != MOVE_NONE; )
        *pv++ = *childPv++;
    *pv = MOVE_NONE;
  }


  // update_all_stats() updates stats at the end of search() when a bestMove is found

  void update_all_stats(const Position& pos, Stack* ss, Move bestMove, Value bestValue, Value beta, Square prevSq,
                        Move* quietsSearched, int quietCount, Move* capturesSearched, int captureCount, Depth depth) {

    Color us = pos.side_to_move();
    Thread* thisThread = pos.this_thread();
    CapturePieceToHistory& captureHistory = thisThread->captureHistory;
    Piece moved_piece = pos.moved_piece(bestMove);
    PieceType captured;

    int quietMoveBonus = stat_bonus(depth + 1);

    if (!pos.capture_stage(bestMove))
    {
        int bestMoveBonus = bestValue > beta + 145 ? quietMoveBonus  // larger bonus
                                            : stat_bonus(depth);     // smaller bonus

        // Increase stats for the best move in case it was a quiet move
        update_quiet_stats(pos, ss, bestMove, bestMoveBonus);

        // Decrease stats for all non-best quiet moves
        for (int i = 0; i < quietCount; ++i)
        {
            thisThread->mainHistory[us][from_to(quietsSearched[i])] << -bestMoveBonus;
            update_continuation_histories(ss, pos.moved_piece(quietsSearched[i]), to_sq(quietsSearched[i]), -bestMoveBonus);
        }
    }
    else
    {
        // Increase stats for the best move in case it was a capture move
        captured = type_of(pos.piece_on(to_sq(bestMove)));
        captureHistory[moved_piece][to_sq(bestMove)][captured] << quietMoveBonus;
    }

    // Extra penalty for a quiet early move that was not a TT move or
    // main killer move in previous ply when it gets refuted.
    if (   prevSq != SQ_NONE
        && ((ss-1)->moveCount == 1 + (ss-1)->ttHit || ((ss-1)->currentMove == (ss-1)->killers[0]))
        && !pos.captured_piece())
            update_continuation_histories(ss-1, pos.piece_on(prevSq), prevSq, -quietMoveBonus);

    // Decrease stats for all non-best capture moves
    for (int i = 0; i < captureCount; ++i)
    {
        moved_piece = pos.moved_piece(capturesSearched[i]);
        captured = type_of(pos.piece_on(to_sq(capturesSearched[i])));
        captureHistory[moved_piece][to_sq(capturesSearched[i])][captured] << -quietMoveBonus;
    }
  }


  // update_continuation_histories() updates histories of the move pairs formed
  // by moves at ply -1, -2, -4, and -6 with current move.

  void update_continuation_histories(Stack* ss, Piece pc, Square to, int bonus) {

    for (int i : {1, 2, 4, 6})
    {
        // Only update the first 2 continuation histories if we are in check
        if (ss->inCheck && i > 2)
            break;
        if (is_ok((ss-i)->currentMove))
            (*(ss-i)->continuationHistory)[pc][to] << bonus;
    }
  }


  // update_quiet_stats() updates move sorting heuristics

  void update_quiet_stats(const Position& pos, Stack* ss, Move move, int bonus) {

    // Update killers
    if (ss->killers[0] != move)
    {
        ss->killers[1] = ss->killers[0];
        ss->killers[0] = move;
    }

    Color us = pos.side_to_move();
    Thread* thisThread = pos.this_thread();
    thisThread->mainHistory[us][from_to(move)] << bonus;
    update_continuation_histories(ss, pos.moved_piece(move), to_sq(move), bonus);

    // Update countermove history
    if (is_ok((ss-1)->currentMove))
    {
        Square prevSq = to_sq((ss-1)->currentMove);
        thisThread->counterMoves[pos.piece_on(prevSq)][prevSq] = move;
    }
  }

  // When playing with strength handicap, choose the best move among a set of RootMoves
  // using a statistical rule dependent on 'level'. Idea by Heinz van Saanen.

  Move Skill::pick_best(size_t multiPV) {

    const RootMoves& rootMoves = Threads.main()->rootMoves;
    static PRNG rng(now()); // PRNG sequence should be non-deterministic

    // RootMoves are already sorted by score in descending order
    Value topScore = rootMoves[0].score;
    int delta = std::min(topScore - rootMoves[multiPV - 1].score, PawnValueMg);
    int maxScore = -VALUE_INFINITE;
    double weakness = 120 - 2 * level;

    // Choose best move. For each move score we add two terms, both dependent on
    // weakness. One is deterministic and bigger for weaker levels, and one is
    // random. Then we choose the move with the resulting highest score.
    for (size_t i = 0; i < multiPV; ++i)
    {
        // This is our magic formula
        int push = int((  weakness * int(topScore - rootMoves[i].score)
                        + delta * (rng.rand<unsigned>() % int(weakness))) / 128);

        if (rootMoves[i].score + push >= maxScore)
        {
            maxScore = rootMoves[i].score + push;
            best = rootMoves[i].pv[0];
        }
    }

    return best;
  }

} // namespace


/// MainThread::check_time() is used to print debug info and, more importantly,
/// to detect when we are out of available time and thus stop the search.

void MainThread::check_time() {

  if (--callsCnt > 0)
      return;

  // When using nodes, ensure checking rate is not lower than 0.1% of nodes
  callsCnt = Limits.nodes ? std::min(512, int(Limits.nodes / 1024)) : 512;

  static TimePoint lastInfoTime = now();

  TimePoint elapsed = Time.elapsed();
  TimePoint tick = Limits.startTime + elapsed;

  if (tick - lastInfoTime >= 1000)
  {
      lastInfoTime = tick;
      dbg_print();
  }

  // We should not stop pondering until told so by the GUI
  if (ponder)
      return;

  if (   (Limits.use_time_management() && (elapsed > Time.maximum() || stopOnPonderhit))
      || (Limits.movetime && elapsed >= Limits.movetime)
      || (Limits.nodes && Threads.nodes_searched() >= (uint64_t)Limits.nodes))
      Threads.stop = true;
}


/// UCI::pv() formats PV information according to the UCI protocol. UCI requires
/// that all (if any) unsearched PV lines are sent using a previous search score.

string UCI::pv(const Position& pos, Depth depth) {

  std::stringstream ss;
  TimePoint elapsed = Time.elapsed() + 1;
  const RootMoves& rootMoves = pos.this_thread()->rootMoves;
  size_t pvIdx = pos.this_thread()->pvIdx;
  size_t multiPV = std::min((size_t)Options["MultiPV"], rootMoves.size());
  uint64_t nodesSearched = Threads.nodes_searched();
  uint64_t tbHits = Threads.tb_hits() + (TB::RootInTB ? rootMoves.size() : 0);

  for (size_t i = 0; i < multiPV; ++i)
  {
      bool updated = rootMoves[i].score != -VALUE_INFINITE;

      if (depth == 1 && !updated && i > 0)
          continue;

      Depth d = updated ? depth : std::max(1, depth - 1);
      Value v = updated ? rootMoves[i].uciScore : rootMoves[i].previousScore;

      if (v == -VALUE_INFINITE)
          v = VALUE_ZERO;

      bool tb = TB::RootInTB && abs(v) < VALUE_MATE_IN_MAX_PLY;
      v = tb ? rootMoves[i].tbScore : v;

      if (ss.rdbuf()->in_avail()) // Not at first line
          ss << "\n";

      ss << "info"
         << " depth "    << d
         << " seldepth " << rootMoves[i].selDepth
         << " multipv "  << i + 1
         << " score "    << UCI::value(v);

      if (Options["UCI_ShowWDL"])
          ss << UCI::wdl(v, pos.game_ply());

      if (i == pvIdx && !tb && updated) // tablebase- and previous-scores are exact
         ss << (rootMoves[i].scoreLowerbound ? " lowerbound" : (rootMoves[i].scoreUpperbound ? " upperbound" : ""));

      ss << " nodes "    << nodesSearched
         << " nps "      << nodesSearched * 1000 / elapsed
         << " hashfull " << TT.hashfull()
         << " tbhits "   << tbHits
         << " time "     << elapsed
         << " pv";

      for (Move m : rootMoves[i].pv)
          ss << " " << UCI::move(m, pos.is_chess960());
  }

  return ss.str();
}


/// RootMove::extract_ponder_from_tt() is called in case we have no ponder move
/// before exiting the search, for instance, in case we stop the search during a
/// fail high at root. We try hard to have a ponder move to return to the GUI,
/// otherwise in case of 'ponder on' we have nothing to think about.

bool RootMove::extract_ponder_from_tt(Position& pos) {

    StateInfo st;
    ASSERT_ALIGNED(&st, Eval::NNUE::CacheLineSize);

    bool ttHit;

    assert(pv.size() == 1);

    if (pv[0] == MOVE_NONE)
        return false;

    pos.do_move(pv[0], st);
    TTEntry* tte = TT.probe(pos.key(), ttHit);

    if (ttHit)
    {
        Move m = tte->move(); // Local copy to be SMP safe
        if (MoveList<LEGAL>(pos).contains(m))
            pv.push_back(m);
    }

    pos.undo_move(pv[0]);
    return pv.size() > 1;
}

void Tablebases::rank_root_moves(Position& pos, Search::RootMoves& rootMoves) {

    RootInTB = false;
    UseRule50 = bool(Options["Syzygy50MoveRule"]);
    ProbeDepth = int(Options["SyzygyProbeDepth"]);
    Cardinality = int(Options["SyzygyProbeLimit"]);
    bool dtz_available = true;

    // Tables with fewer pieces than SyzygyProbeLimit are searched with
    // ProbeDepth == DEPTH_ZERO
    if (Cardinality > MaxCardinality)
    {
        Cardinality = MaxCardinality;
        ProbeDepth = 0;
    }

    if (Cardinality >= popcount(pos.pieces()) && !pos.can_castle(ANY_CASTLING))
    {
        // Rank moves using DTZ tables
        RootInTB = root_probe(pos, rootMoves);

        if (!RootInTB)
        {
            // DTZ tables are missing; try to rank moves using WDL tables
            dtz_available = false;
            RootInTB = root_probe_wdl(pos, rootMoves);
        }
    }

    if (RootInTB)
    {
        // Sort moves according to TB rank
        std::stable_sort(rootMoves.begin(), rootMoves.end(),
                  [](const RootMove &a, const RootMove &b) { return a.tbRank > b.tbRank; } );

        // Probe during search only if DTZ is not available and we are winning
        if (dtz_available || rootMoves[0].tbScore <= VALUE_DRAW)
            Cardinality = 0;
    }
    else
    {
        // Clean up if root_probe() and root_probe_wdl() have failed
        for (auto& m : rootMoves)
            m.tbRank = 0;
    }
}

} // namespace Stockfish
