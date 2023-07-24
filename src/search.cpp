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
    const int baseImprovingReductionAdjustment = -24012; const int baseReductionScale = 966;
    const int baseImprovingReductionScale = 920; const int lmrDepthScale = 978; const int lmrDepthScaleTwo = 876; const int ttMoveCutNodeScale = 3803;
    const int depthReductionDecreaseThres = 4707; const int improvingReductionMax = 1916344;
    const int baseReductionAdjustment = 928808; const int baseReductionDeltaScale = 880029; const int reductionTableScale = 1304;
    const int reductionTableAdjustment = 91; const int improvementAdjustment = 494; const int improvementScale = 123; const int improvementUpper = 991;
    const int statScoreScale = 11871; const int statScoreDepthScale = 5401; const int statScoreDepthLower = 7; const int statScoreDepthUpper = 22; 
    const int statScoreAdjustment = -3896348; const int statScoreMainHistoryScale = 2351; const int statScoreContHistoryZero = 1186; 
    const int statScoreContHistoryOne = 1013;  const int statScoreContHistoryThree = 895; const int improvementLower = 4; 
    const int nullMoveStatScoreThreshold = 17141852; const int futilityPruningStatScoreDivisor = 359047; const int LMRDepthReductionThres = -3754;

    //Residuals
    int residualScale; int residualAdjustment; int residualBaseline;


  // Different node types, used as a template parameter
  enum NodeType { NonPV, PV, Root };

  // Futility margin
  Value futility_margin(Depth d, bool noTtCutNode, bool improving) {
    return Value((140 - 40 * noTtCutNode) * (d - improving));
  }

  // Reductions lookup table initialized at startup
  int Reductions[MAX_MOVES]; // [depth or moveNumber]

  int reduction(int improvement, Depth d, int mn, Value delta, Value rootDelta) {
    int r = (Reductions[d] * Reductions[mn]) / 64 / 64;
    int reduction = baseReductionScale * r + baseReductionAdjustment - int(delta) * baseReductionDeltaScale / int(rootDelta);
    if(improvement <= improvementLower)
        reduction += std::min(r * baseImprovingReductionScale + baseImprovingReductionAdjustment, improvingReductionMax) *
        std::min(improvementAdjustment - improvement * improvementScale / 1024, improvementUpper) / 1024;
    return reduction / 1024;
  }

  //Tune 1 116k game values
  int inputScales[23][23][2];

  int biases[2][23];
  int slopes[2][2][23];

  int outputBias[2];
  int outputSlopes[2][2];

  void SetValues() {
      inputScales[0][0][0] = 39;
      inputScales[0][0][1] = 1284;
      inputScales[0][1][0] = 278;
      inputScales[0][1][1] = 1015;
      inputScales[0][2][0] = -699;
      inputScales[0][2][1] = 804;
      inputScales[0][3][0] = 35;
      inputScales[0][3][1] = 284;
      inputScales[0][4][0] = -385;
      inputScales[0][4][1] = 209;
      inputScales[0][5][0] = -139;
      inputScales[0][5][1] = -26;
      inputScales[0][6][0] = -301;
      inputScales[0][6][1] = 184;
      inputScales[0][7][0] = 121;
      inputScales[0][7][1] = 129;
      inputScales[0][8][0] = 51;
      inputScales[0][8][1] = 235;
      inputScales[0][9][0] = -371;
      inputScales[0][9][1] = 171;
      inputScales[0][10][0] = 293;
      inputScales[0][10][1] = 32;
      inputScales[0][11][0] = 159;
      inputScales[0][11][1] = 299;
      inputScales[0][12][0] = 24;
      inputScales[0][12][1] = 162;
      inputScales[0][13][0] = -28;
      inputScales[0][13][1] = -102;
      inputScales[0][14][0] = 76;
      inputScales[0][14][1] = -46;
      inputScales[0][15][0] = -29;
      inputScales[0][15][1] = 128;
      inputScales[0][16][0] = -95;
      inputScales[0][16][1] = 1;
      inputScales[0][17][0] = -127;
      inputScales[0][17][1] = -72;
      inputScales[0][18][0] = 16;
      inputScales[0][18][1] = 160;
      inputScales[0][19][0] = -117;
      inputScales[0][19][1] = 121;
      inputScales[0][20][0] = 15;
      inputScales[0][20][1] = -77;
      inputScales[0][21][0] = -2;
      inputScales[0][21][1] = 90;
      inputScales[0][22][0] = -93;
      inputScales[0][22][1] = -102;
      inputScales[1][0][0] = 90;
      inputScales[1][0][1] = 1226;
      inputScales[1][1][0] = -546;
      inputScales[1][1][1] = 685;
      inputScales[1][2][0] = -316;
      inputScales[1][2][1] = 582;
      inputScales[1][3][0] = -235;
      inputScales[1][3][1] = 1021;
      inputScales[1][4][0] = 187;
      inputScales[1][4][1] = -239;
      inputScales[1][5][0] = 4;
      inputScales[1][5][1] = -271;
      inputScales[1][6][0] = -121;
      inputScales[1][6][1] = 299;
      inputScales[1][7][0] = -111;
      inputScales[1][7][1] = -125;
      inputScales[1][8][0] = 167;
      inputScales[1][8][1] = -132;
      inputScales[1][9][0] = -77;
      inputScales[1][9][1] = -29;
      inputScales[1][10][0] = -92;
      inputScales[1][10][1] = 41;
      inputScales[1][11][0] = 265;
      inputScales[1][11][1] = 123;
      inputScales[1][12][0] = -37;
      inputScales[1][12][1] = 52;
      inputScales[1][13][0] = -101;
      inputScales[1][13][1] = 65;
      inputScales[1][14][0] = -120;
      inputScales[1][14][1] = 160;
      inputScales[1][15][0] = -94;
      inputScales[1][15][1] = 136;
      inputScales[1][16][0] = -121;
      inputScales[1][16][1] = 43;
      inputScales[1][17][0] = -157;
      inputScales[1][17][1] = 71;
      inputScales[1][18][0] = 46;
      inputScales[1][18][1] = -122;
      inputScales[1][19][0] = -80;
      inputScales[1][19][1] = -20;
      inputScales[1][20][0] = -35;
      inputScales[1][20][1] = 1;
      inputScales[1][21][0] = -2;
      inputScales[1][21][1] = -62;
      inputScales[1][22][0] = -76;
      inputScales[1][22][1] = 77;
      inputScales[2][0][0] = -387;
      inputScales[2][0][1] = -1086;
      inputScales[2][1][0] = 183;
      inputScales[2][1][1] = -988;
      inputScales[2][2][0] = -1013;
      inputScales[2][2][1] = -138;
      inputScales[2][3][0] = -643;
      inputScales[2][3][1] = 493;
      inputScales[2][4][0] = 436;
      inputScales[2][4][1] = -1153;
      inputScales[2][5][0] = -230;
      inputScales[2][5][1] = -136;
      inputScales[2][6][0] = 360;
      inputScales[2][6][1] = -426;
      inputScales[2][7][0] = 206;
      inputScales[2][7][1] = 63;
      inputScales[2][8][0] = -72;
      inputScales[2][8][1] = 267;
      inputScales[2][9][0] = 133;
      inputScales[2][9][1] = 459;
      inputScales[2][10][0] = 70;
      inputScales[2][10][1] = 55;
      inputScales[2][11][0] = 249;
      inputScales[2][11][1] = -353;
      inputScales[2][12][0] = -9;
      inputScales[2][12][1] = 33;
      inputScales[2][13][0] = -165;
      inputScales[2][13][1] = -92;
      inputScales[2][14][0] = 131;
      inputScales[2][14][1] = -26;
      inputScales[2][15][0] = 69;
      inputScales[2][15][1] = -77;
      inputScales[2][16][0] = -34;
      inputScales[2][16][1] = 9;
      inputScales[2][17][0] = 17;
      inputScales[2][17][1] = -17;
      inputScales[2][18][0] = -26;
      inputScales[2][18][1] = 102;
      inputScales[2][19][0] = -149;
      inputScales[2][19][1] = -169;
      inputScales[2][20][0] = 27;
      inputScales[2][20][1] = -74;
      inputScales[2][21][0] = -121;
      inputScales[2][21][1] = 24;
      inputScales[2][22][0] = 59;
      inputScales[2][22][1] = -52;
      inputScales[3][0][0] = -19;
      inputScales[3][0][1] = -1140;
      inputScales[3][1][0] = 43;
      inputScales[3][1][1] = -1297;
      inputScales[3][2][0] = -1203;
      inputScales[3][2][1] = 208;
      inputScales[3][3][0] = -227;
      inputScales[3][3][1] = -249;
      inputScales[3][4][0] = 188;
      inputScales[3][4][1] = -1052;
      inputScales[3][5][0] = -50;
      inputScales[3][5][1] = -672;
      inputScales[3][6][0] = 101;
      inputScales[3][6][1] = 18;
      inputScales[3][7][0] = 273;
      inputScales[3][7][1] = 462;
      inputScales[3][8][0] = 396;
      inputScales[3][8][1] = -86;
      inputScales[3][9][0] = -541;
      inputScales[3][9][1] = -70;
      inputScales[3][10][0] = 43;
      inputScales[3][10][1] = 88;
      inputScales[3][11][0] = -174;
      inputScales[3][11][1] = -18;
      inputScales[3][12][0] = 32;
      inputScales[3][12][1] = -27;
      inputScales[3][13][0] = 27;
      inputScales[3][13][1] = -96;
      inputScales[3][14][0] = -3;
      inputScales[3][14][1] = -74;
      inputScales[3][15][0] = -83;
      inputScales[3][15][1] = -17;
      inputScales[3][16][0] = 116;
      inputScales[3][16][1] = 54;
      inputScales[3][17][0] = 77;
      inputScales[3][17][1] = -2;
      inputScales[3][18][0] = -17;
      inputScales[3][18][1] = -37;
      inputScales[3][19][0] = -79;
      inputScales[3][19][1] = 112;
      inputScales[3][20][0] = -104;
      inputScales[3][20][1] = 212;
      inputScales[3][21][0] = 24;
      inputScales[3][21][1] = 99;
      inputScales[3][22][0] = 0;
      inputScales[3][22][1] = -45;
      inputScales[4][0][0] = 144;
      inputScales[4][0][1] = -1080;
      inputScales[4][1][0] = 3;
      inputScales[4][1][1] = -991;
      inputScales[4][2][0] = -518;
      inputScales[4][2][1] = 92;
      inputScales[4][3][0] = 39;
      inputScales[4][3][1] = -77;
      inputScales[4][4][0] = -854;
      inputScales[4][4][1] = -4;
      inputScales[4][5][0] = 280;
      inputScales[4][5][1] = -283;
      inputScales[4][6][0] = -471;
      inputScales[4][6][1] = -833;
      inputScales[4][7][0] = -215;
      inputScales[4][7][1] = -434;
      inputScales[4][8][0] = -322;
      inputScales[4][8][1] = -13;
      inputScales[4][9][0] = -1;
      inputScales[4][9][1] = -26;
      inputScales[4][10][0] = 533;
      inputScales[4][10][1] = 161;
      inputScales[4][11][0] = 230;
      inputScales[4][11][1] = 230;
      inputScales[4][12][0] = 39;
      inputScales[4][12][1] = 31;
      inputScales[4][13][0] = 17;
      inputScales[4][13][1] = -3;
      inputScales[4][14][0] = 140;
      inputScales[4][14][1] = 29;
      inputScales[4][15][0] = 44;
      inputScales[4][15][1] = 68;
      inputScales[4][16][0] = 64;
      inputScales[4][16][1] = -154;
      inputScales[4][17][0] = 68;
      inputScales[4][17][1] = 149;
      inputScales[4][18][0] = -117;
      inputScales[4][18][1] = -114;
      inputScales[4][19][0] = 91;
      inputScales[4][19][1] = -133;
      inputScales[4][20][0] = 67;
      inputScales[4][20][1] = 143;
      inputScales[4][21][0] = -132;
      inputScales[4][21][1] = 125;
      inputScales[4][22][0] = -55;
      inputScales[4][22][1] = 114;
      inputScales[5][0][0] = -1080;
      inputScales[5][0][1] = 196;
      inputScales[5][1][0] = -1027;
      inputScales[5][1][1] = -472;
      inputScales[5][2][0] = -334;
      inputScales[5][2][1] = -1276;
      inputScales[5][3][0] = 230;
      inputScales[5][3][1] = -115;
      inputScales[5][4][0] = -247;
      inputScales[5][4][1] = -961;
      inputScales[5][5][0] = -31;
      inputScales[5][5][1] = 409;
      inputScales[5][6][0] = -602;
      inputScales[5][6][1] = 225;
      inputScales[5][7][0] = -1155;
      inputScales[5][7][1] = 99;
      inputScales[5][8][0] = 163;
      inputScales[5][8][1] = -86;
      inputScales[5][9][0] = -136;
      inputScales[5][9][1] = 288;
      inputScales[5][10][0] = -219;
      inputScales[5][10][1] = -362;
      inputScales[5][11][0] = -64;
      inputScales[5][11][1] = 30;
      inputScales[5][12][0] = -195;
      inputScales[5][12][1] = 11;
      inputScales[5][13][0] = -65;
      inputScales[5][13][1] = 42;
      inputScales[5][14][0] = 49;
      inputScales[5][14][1] = -10;
      inputScales[5][15][0] = -64;
      inputScales[5][15][1] = -64;
      inputScales[5][16][0] = 145;
      inputScales[5][16][1] = 150;
      inputScales[5][17][0] = 139;
      inputScales[5][17][1] = 14;
      inputScales[5][18][0] = 31;
      inputScales[5][18][1] = 50;
      inputScales[5][19][0] = 101;
      inputScales[5][19][1] = 170;
      inputScales[5][20][0] = -66;
      inputScales[5][20][1] = 86;
      inputScales[5][21][0] = 126;
      inputScales[5][21][1] = -7;
      inputScales[5][22][0] = 78;
      inputScales[5][22][1] = 68;
      inputScales[6][0][0] = -154;
      inputScales[6][0][1] = -1046;
      inputScales[6][1][0] = -64;
      inputScales[6][1][1] = -639;
      inputScales[6][2][0] = -1193;
      inputScales[6][2][1] = -2;
      inputScales[6][3][0] = 253;
      inputScales[6][3][1] = 154;
      inputScales[6][4][0] = -1246;
      inputScales[6][4][1] = -183;
      inputScales[6][5][0] = -89;
      inputScales[6][5][1] = -354;
      inputScales[6][6][0] = -1023;
      inputScales[6][6][1] = 237;
      inputScales[6][7][0] = 271;
      inputScales[6][7][1] = 73;
      inputScales[6][8][0] = -426;
      inputScales[6][8][1] = -1213;
      inputScales[6][9][0] = 50;
      inputScales[6][9][1] = 26;
      inputScales[6][10][0] = 326;
      inputScales[6][10][1] = 145;
      inputScales[6][11][0] = 307;
      inputScales[6][11][1] = -57;
      inputScales[6][12][0] = 28;
      inputScales[6][12][1] = 120;
      inputScales[6][13][0] = -143;
      inputScales[6][13][1] = 191;
      inputScales[6][14][0] = -108;
      inputScales[6][14][1] = -27;
      inputScales[6][15][0] = 20;
      inputScales[6][15][1] = 22;
      inputScales[6][16][0] = 26;
      inputScales[6][16][1] = 105;
      inputScales[6][17][0] = -125;
      inputScales[6][17][1] = 175;
      inputScales[6][18][0] = -143;
      inputScales[6][18][1] = -167;
      inputScales[6][19][0] = 4;
      inputScales[6][19][1] = 5;
      inputScales[6][20][0] = -96;
      inputScales[6][20][1] = -86;
      inputScales[6][21][0] = -129;
      inputScales[6][21][1] = -86;
      inputScales[6][22][0] = -66;
      inputScales[6][22][1] = 204;
      inputScales[7][0][0] = -144;
      inputScales[7][0][1] = -715;
      inputScales[7][1][0] = 154;
      inputScales[7][1][1] = -1078;
      inputScales[7][2][0] = -1097;
      inputScales[7][2][1] = 283;
      inputScales[7][3][0] = 281;
      inputScales[7][3][1] = -203;
      inputScales[7][4][0] = -1031;
      inputScales[7][4][1] = 170;
      inputScales[7][5][0] = 125;
      inputScales[7][5][1] = 268;
      inputScales[7][6][0] = -1426;
      inputScales[7][6][1] = -139;
      inputScales[7][7][0] = 84;
      inputScales[7][7][1] = -30;
      inputScales[7][8][0] = -1307;
      inputScales[7][8][1] = -131;
      inputScales[7][9][0] = 86;
      inputScales[7][9][1] = -1006;
      inputScales[7][10][0] = 22;
      inputScales[7][10][1] = -43;
      inputScales[7][11][0] = 283;
      inputScales[7][11][1] = 83;
      inputScales[7][12][0] = 16;
      inputScales[7][12][1] = -90;
      inputScales[7][13][0] = -78;
      inputScales[7][13][1] = -8;
      inputScales[7][14][0] = 44;
      inputScales[7][14][1] = -70;
      inputScales[7][15][0] = -25;
      inputScales[7][15][1] = 64;
      inputScales[7][16][0] = -24;
      inputScales[7][16][1] = 71;
      inputScales[7][17][0] = -169;
      inputScales[7][17][1] = -6;
      inputScales[7][18][0] = 137;
      inputScales[7][18][1] = -77;
      inputScales[7][19][0] = -91;
      inputScales[7][19][1] = -91;
      inputScales[7][20][0] = -28;
      inputScales[7][20][1] = 76;
      inputScales[7][21][0] = -82;
      inputScales[7][21][1] = 149;
      inputScales[7][22][0] = -77;
      inputScales[7][22][1] = -97;
      inputScales[8][0][0] = 10;
      inputScales[8][0][1] = 986;
      inputScales[8][1][0] = 1048;
      inputScales[8][1][1] = 165;
      inputScales[8][2][0] = -491;
      inputScales[8][2][1] = -114;
      inputScales[8][3][0] = 253;
      inputScales[8][3][1] = 405;
      inputScales[8][4][0] = -51;
      inputScales[8][4][1] = 199;
      inputScales[8][5][0] = -71;
      inputScales[8][5][1] = 149;
      inputScales[8][6][0] = 213;
      inputScales[8][6][1] = -432;
      inputScales[8][7][0] = -640;
      inputScales[8][7][1] = -218;
      inputScales[8][8][0] = 105;
      inputScales[8][8][1] = 55;
      inputScales[8][9][0] = -317;
      inputScales[8][9][1] = -46;
      inputScales[8][10][0] = -338;
      inputScales[8][10][1] = 992;
      inputScales[8][11][0] = -312;
      inputScales[8][11][1] = 642;
      inputScales[8][12][0] = 24;
      inputScales[8][12][1] = -53;
      inputScales[8][13][0] = -19;
      inputScales[8][13][1] = 42;
      inputScales[8][14][0] = 49;
      inputScales[8][14][1] = 90;
      inputScales[8][15][0] = -67;
      inputScales[8][15][1] = -31;
      inputScales[8][16][0] = -12;
      inputScales[8][16][1] = 141;
      inputScales[8][17][0] = -51;
      inputScales[8][17][1] = -23;
      inputScales[8][18][0] = -107;
      inputScales[8][18][1] = 41;
      inputScales[8][19][0] = -106;
      inputScales[8][19][1] = 94;
      inputScales[8][20][0] = 88;
      inputScales[8][20][1] = -120;
      inputScales[8][21][0] = 5;
      inputScales[8][21][1] = 91;
      inputScales[8][22][0] = 111;
      inputScales[8][22][1] = -84;
      inputScales[9][0][0] = -120;
      inputScales[9][0][1] = 966;
      inputScales[9][1][0] = 614;
      inputScales[9][1][1] = 265;
      inputScales[9][2][0] = -346;
      inputScales[9][2][1] = -276;
      inputScales[9][3][0] = -209;
      inputScales[9][3][1] = -60;
      inputScales[9][4][0] = -38;
      inputScales[9][4][1] = -39;
      inputScales[9][5][0] = 188;
      inputScales[9][5][1] = 254;
      inputScales[9][6][0] = 136;
      inputScales[9][6][1] = -342;
      inputScales[9][7][0] = 59;
      inputScales[9][7][1] = 106;
      inputScales[9][8][0] = -31;
      inputScales[9][8][1] = -407;
      inputScales[9][9][0] = -159;
      inputScales[9][9][1] = 207;
      inputScales[9][10][0] = 861;
      inputScales[9][10][1] = 81;
      inputScales[9][11][0] = -347;
      inputScales[9][11][1] = 1245;
      inputScales[9][12][0] = 10;
      inputScales[9][12][1] = -110;
      inputScales[9][13][0] = -145;
      inputScales[9][13][1] = 12;
      inputScales[9][14][0] = -25;
      inputScales[9][14][1] = 27;
      inputScales[9][15][0] = -123;
      inputScales[9][15][1] = 28;
      inputScales[9][16][0] = 58;
      inputScales[9][16][1] = -52;
      inputScales[9][17][0] = -27;
      inputScales[9][17][1] = 30;
      inputScales[9][18][0] = -162;
      inputScales[9][18][1] = -15;
      inputScales[9][19][0] = -5;
      inputScales[9][19][1] = -110;
      inputScales[9][20][0] = -169;
      inputScales[9][20][1] = 162;
      inputScales[9][21][0] = -73;
      inputScales[9][21][1] = 92;
      inputScales[9][22][0] = -80;
      inputScales[9][22][1] = 39;
      inputScales[10][0][0] = -97;
      inputScales[10][0][1] = 96;
      inputScales[10][1][0] = 5;
      inputScales[10][1][1] = -17;
      inputScales[10][2][0] = -62;
      inputScales[10][2][1] = 84;
      inputScales[10][3][0] = 68;
      inputScales[10][3][1] = 78;
      inputScales[10][4][0] = 72;
      inputScales[10][4][1] = -1241;
      inputScales[10][5][0] = 109;
      inputScales[10][5][1] = 72;
      inputScales[10][6][0] = 91;
      inputScales[10][6][1] = 50;
      inputScales[10][7][0] = 24;
      inputScales[10][7][1] = 177;
      inputScales[10][8][0] = 205;
      inputScales[10][8][1] = -59;
      inputScales[10][9][0] = 108;
      inputScales[10][9][1] = 55;
      inputScales[10][10][0] = -27;
      inputScales[10][10][1] = 87;
      inputScales[10][11][0] = -33;
      inputScales[10][11][1] = -68;
      inputScales[10][12][0] = -164;
      inputScales[10][12][1] = -116;
      inputScales[10][13][0] = -125;
      inputScales[10][13][1] = -186;
      inputScales[10][14][0] = -1;
      inputScales[10][14][1] = 169;
      inputScales[10][15][0] = -4;
      inputScales[10][15][1] = -105;
      inputScales[10][16][0] = -82;
      inputScales[10][16][1] = 105;
      inputScales[10][17][0] = -193;
      inputScales[10][17][1] = 41;
      inputScales[10][18][0] = 1;
      inputScales[10][18][1] = -197;
      inputScales[10][19][0] = -77;
      inputScales[10][19][1] = -147;
      inputScales[10][20][0] = -108;
      inputScales[10][20][1] = 18;
      inputScales[10][21][0] = -22;
      inputScales[10][21][1] = -134;
      inputScales[10][22][0] = -45;
      inputScales[10][22][1] = 64;
      inputScales[11][0][0] = -193;
      inputScales[11][0][1] = -22;
      inputScales[11][1][0] = 30;
      inputScales[11][1][1] = 103;
      inputScales[11][2][0] = 113;
      inputScales[11][2][1] = 86;
      inputScales[11][3][0] = 89;
      inputScales[11][3][1] = 82;
      inputScales[11][4][0] = 117;
      inputScales[11][4][1] = 75;
      inputScales[11][5][0] = 119;
      inputScales[11][5][1] = 947;
      inputScales[11][6][0] = 58;
      inputScales[11][6][1] = 44;
      inputScales[11][7][0] = -74;
      inputScales[11][7][1] = 130;
      inputScales[11][8][0] = -163;
      inputScales[11][8][1] = 163;
      inputScales[11][9][0] = -26;
      inputScales[11][9][1] = -122;
      inputScales[11][10][0] = 61;
      inputScales[11][10][1] = -31;
      inputScales[11][11][0] = -3;
      inputScales[11][11][1] = -67;
      inputScales[11][12][0] = -121;
      inputScales[11][12][1] = 20;
      inputScales[11][13][0] = -80;
      inputScales[11][13][1] = 91;
      inputScales[11][14][0] = -34;
      inputScales[11][14][1] = 30;
      inputScales[11][15][0] = -60;
      inputScales[11][15][1] = -1;
      inputScales[11][16][0] = 61;
      inputScales[11][16][1] = -26;
      inputScales[11][17][0] = 78;
      inputScales[11][17][1] = -95;
      inputScales[11][18][0] = 102;
      inputScales[11][18][1] = -168;
      inputScales[11][19][0] = -14;
      inputScales[11][19][1] = 162;
      inputScales[11][20][0] = -110;
      inputScales[11][20][1] = 2;
      inputScales[11][21][0] = -88;
      inputScales[11][21][1] = -64;
      inputScales[11][22][0] = 154;
      inputScales[11][22][1] = -9;
      inputScales[12][0][0] = 7;
      inputScales[12][0][1] = 154;
      inputScales[12][1][0] = 80;
      inputScales[12][1][1] = -160;
      inputScales[12][2][0] = -34;
      inputScales[12][2][1] = -129;
      inputScales[12][3][0] = 57;
      inputScales[12][3][1] = 2;
      inputScales[12][4][0] = 65;
      inputScales[12][4][1] = -107;
      inputScales[12][5][0] = -115;
      inputScales[12][5][1] = -4;
      inputScales[12][6][0] = -108;
      inputScales[12][6][1] = -138;
      inputScales[12][7][0] = -41;
      inputScales[12][7][1] = -27;
      inputScales[12][8][0] = 158;
      inputScales[12][8][1] = -203;
      inputScales[12][9][0] = 84;
      inputScales[12][9][1] = -95;
      inputScales[12][10][0] = -18;
      inputScales[12][10][1] = 70;
      inputScales[12][11][0] = -66;
      inputScales[12][11][1] = -77;
      inputScales[12][12][0] = 123;
      inputScales[12][12][1] = 72;
      inputScales[12][13][0] = 28;
      inputScales[12][13][1] = 100;
      inputScales[12][14][0] = 28;
      inputScales[12][14][1] = -97;
      inputScales[12][15][0] = 71;
      inputScales[12][15][1] = -94;
      inputScales[12][16][0] = 7;
      inputScales[12][16][1] = -13;
      inputScales[12][17][0] = 485;
      inputScales[12][17][1] = -64;
      inputScales[12][18][0] = -96;
      inputScales[12][18][1] = 67;
      inputScales[12][19][0] = 33;
      inputScales[12][19][1] = -122;
      inputScales[12][20][0] = 36;
      inputScales[12][20][1] = 129;
      inputScales[12][21][0] = -177;
      inputScales[12][21][1] = 30;
      inputScales[12][22][0] = 87;
      inputScales[12][22][1] = 96;
      inputScales[13][0][0] = 12;
      inputScales[13][0][1] = 19;
      inputScales[13][1][0] = -112;
      inputScales[13][1][1] = -40;
      inputScales[13][2][0] = 90;
      inputScales[13][2][1] = 138;
      inputScales[13][3][0] = 30;
      inputScales[13][3][1] = -50;
      inputScales[13][4][0] = -111;
      inputScales[13][4][1] = -99;
      inputScales[13][5][0] = -51;
      inputScales[13][5][1] = -76;
      inputScales[13][6][0] = -96;
      inputScales[13][6][1] = -118;
      inputScales[13][7][0] = -150;
      inputScales[13][7][1] = -17;
      inputScales[13][8][0] = 78;
      inputScales[13][8][1] = 59;
      inputScales[13][9][0] = -27;
      inputScales[13][9][1] = -6;
      inputScales[13][10][0] = -71;
      inputScales[13][10][1] = -28;
      inputScales[13][11][0] = 70;
      inputScales[13][11][1] = 165;
      inputScales[13][12][0] = -1;
      inputScales[13][12][1] = 50;
      inputScales[13][13][0] = -9;
      inputScales[13][13][1] = -176;
      inputScales[13][14][0] = -167;
      inputScales[13][14][1] = 55;
      inputScales[13][15][0] = 121;
      inputScales[13][15][1] = 160;
      inputScales[13][16][0] = -177;
      inputScales[13][16][1] = 47;
      inputScales[13][17][0] = 0;
      inputScales[13][17][1] = 63;
      inputScales[13][18][0] = -69;
      inputScales[13][18][1] = -1085;
      inputScales[13][19][0] = -10;
      inputScales[13][19][1] = 21;
      inputScales[13][20][0] = -102;
      inputScales[13][20][1] = 99;
      inputScales[13][21][0] = 96;
      inputScales[13][21][1] = 124;
      inputScales[13][22][0] = -86;
      inputScales[13][22][1] = 13;
      inputScales[14][0][0] = -133;
      inputScales[14][0][1] = -61;
      inputScales[14][1][0] = -82;
      inputScales[14][1][1] = 24;
      inputScales[14][2][0] = 84;
      inputScales[14][2][1] = -62;
      inputScales[14][3][0] = -4;
      inputScales[14][3][1] = 133;
      inputScales[14][4][0] = -12;
      inputScales[14][4][1] = -38;
      inputScales[14][5][0] = 16;
      inputScales[14][5][1] = 62;
      inputScales[14][6][0] = -8;
      inputScales[14][6][1] = -101;
      inputScales[14][7][0] = 101;
      inputScales[14][7][1] = -79;
      inputScales[14][8][0] = -77;
      inputScales[14][8][1] = -48;
      inputScales[14][9][0] = -30;
      inputScales[14][9][1] = 81;
      inputScales[14][10][0] = 72;
      inputScales[14][10][1] = -181;
      inputScales[14][11][0] = -20;
      inputScales[14][11][1] = 111;
      inputScales[14][12][0] = -148;
      inputScales[14][12][1] = -32;
      inputScales[14][13][0] = 139;
      inputScales[14][13][1] = -55;
      inputScales[14][14][0] = 58;
      inputScales[14][14][1] = 39;
      inputScales[14][15][0] = -32;
      inputScales[14][15][1] = 64;
      inputScales[14][16][0] = -3;
      inputScales[14][16][1] = 66;
      inputScales[14][17][0] = -78;
      inputScales[14][17][1] = 120;
      inputScales[14][18][0] = 101;
      inputScales[14][18][1] = 12;
      inputScales[14][19][0] = -103;
      inputScales[14][19][1] = 1031;
      inputScales[14][20][0] = -56;
      inputScales[14][20][1] = -64;
      inputScales[14][21][0] = -104;
      inputScales[14][21][1] = 53;
      inputScales[14][22][0] = -180;
      inputScales[14][22][1] = -52;
      inputScales[15][0][0] = -43;
      inputScales[15][0][1] = -102;
      inputScales[15][1][0] = -69;
      inputScales[15][1][1] = -162;
      inputScales[15][2][0] = 79;
      inputScales[15][2][1] = 44;
      inputScales[15][3][0] = 148;
      inputScales[15][3][1] = -12;
      inputScales[15][4][0] = -246;
      inputScales[15][4][1] = 31;
      inputScales[15][5][0] = -45;
      inputScales[15][5][1] = 13;
      inputScales[15][6][0] = 30;
      inputScales[15][6][1] = 100;
      inputScales[15][7][0] = -99;
      inputScales[15][7][1] = -132;
      inputScales[15][8][0] = -87;
      inputScales[15][8][1] = -10;
      inputScales[15][9][0] = -158;
      inputScales[15][9][1] = 17;
      inputScales[15][10][0] = -28;
      inputScales[15][10][1] = -154;
      inputScales[15][11][0] = -97;
      inputScales[15][11][1] = -194;
      inputScales[15][12][0] = 84;
      inputScales[15][12][1] = 88;
      inputScales[15][13][0] = 84;
      inputScales[15][13][1] = -18;
      inputScales[15][14][0] = 16;
      inputScales[15][14][1] = 72;
      inputScales[15][15][0] = 43;
      inputScales[15][15][1] = -43;
      inputScales[15][16][0] = -187;
      inputScales[15][16][1] = -132;
      inputScales[15][17][0] = 57;
      inputScales[15][17][1] = 198;
      inputScales[15][18][0] = 33;
      inputScales[15][18][1] = 79;
      inputScales[15][19][0] = -114;
      inputScales[15][19][1] = 76;
      inputScales[15][20][0] = -74;
      inputScales[15][20][1] = -1102;
      inputScales[15][21][0] = 61;
      inputScales[15][21][1] = -154;
      inputScales[15][22][0] = 15;
      inputScales[15][22][1] = -66;
      inputScales[16][0][0] = 85;
      inputScales[16][0][1] = -74;
      inputScales[16][1][0] = -57;
      inputScales[16][1][1] = 107;
      inputScales[16][2][0] = 140;
      inputScales[16][2][1] = 103;
      inputScales[16][3][0] = 32;
      inputScales[16][3][1] = -108;
      inputScales[16][4][0] = 40;
      inputScales[16][4][1] = 155;
      inputScales[16][5][0] = -57;
      inputScales[16][5][1] = -16;
      inputScales[16][6][0] = 90;
      inputScales[16][6][1] = 29;
      inputScales[16][7][0] = 127;
      inputScales[16][7][1] = 108;
      inputScales[16][8][0] = -8;
      inputScales[16][8][1] = -191;
      inputScales[16][9][0] = 80;
      inputScales[16][9][1] = -114;
      inputScales[16][10][0] = 190;
      inputScales[16][10][1] = 97;
      inputScales[16][11][0] = 19;
      inputScales[16][11][1] = -79;
      inputScales[16][12][0] = -36;
      inputScales[16][12][1] = 97;
      inputScales[16][13][0] = 107;
      inputScales[16][13][1] = -93;
      inputScales[16][14][0] = 78;
      inputScales[16][14][1] = -128;
      inputScales[16][15][0] = 8;
      inputScales[16][15][1] = 122;
      inputScales[16][16][0] = 1;
      inputScales[16][16][1] = 77;
      inputScales[16][17][0] = -129;
      inputScales[16][17][1] = -152;
      inputScales[16][18][0] = -93;
      inputScales[16][18][1] = 32;
      inputScales[16][19][0] = -50;
      inputScales[16][19][1] = 23;
      inputScales[16][20][0] = 9;
      inputScales[16][20][1] = 19;
      inputScales[16][21][0] = 107;
      inputScales[16][21][1] = 960;
      inputScales[16][22][0] = -1;
      inputScales[16][22][1] = -83;
      inputScales[17][0][0] = 58;
      inputScales[17][0][1] = -57;
      inputScales[17][1][0] = -68;
      inputScales[17][1][1] = -58;
      inputScales[17][2][0] = 35;
      inputScales[17][2][1] = -70;
      inputScales[17][3][0] = -49;
      inputScales[17][3][1] = 101;
      inputScales[17][4][0] = -1;
      inputScales[17][4][1] = -23;
      inputScales[17][5][0] = -75;
      inputScales[17][5][1] = 1157;
      inputScales[17][6][0] = -30;
      inputScales[17][6][1] = -37;
      inputScales[17][7][0] = 109;
      inputScales[17][7][1] = -161;
      inputScales[17][8][0] = 30;
      inputScales[17][8][1] = -50;
      inputScales[17][9][0] = 175;
      inputScales[17][9][1] = 33;
      inputScales[17][10][0] = -52;
      inputScales[17][10][1] = 132;
      inputScales[17][11][0] = 72;
      inputScales[17][11][1] = -19;
      inputScales[17][12][0] = 129;
      inputScales[17][12][1] = -159;
      inputScales[17][13][0] = 37;
      inputScales[17][13][1] = 28;
      inputScales[17][14][0] = -7;
      inputScales[17][14][1] = -14;
      inputScales[17][15][0] = -5;
      inputScales[17][15][1] = 13;
      inputScales[17][16][0] = 137;
      inputScales[17][16][1] = 212;
      inputScales[17][17][0] = -97;
      inputScales[17][17][1] = 171;
      inputScales[17][18][0] = -54;
      inputScales[17][18][1] = 135;
      inputScales[17][19][0] = 71;
      inputScales[17][19][1] = -18;
      inputScales[17][20][0] = 63;
      inputScales[17][20][1] = -23;
      inputScales[17][21][0] = 114;
      inputScales[17][21][1] = 955;
      inputScales[17][22][0] = 73;
      inputScales[17][22][1] = 826;
      inputScales[18][0][0] = -80;
      inputScales[18][0][1] = 82;
      inputScales[18][1][0] = -101;
      inputScales[18][1][1] = -100;
      inputScales[18][2][0] = 59;
      inputScales[18][2][1] = -27;
      inputScales[18][3][0] = -87;
      inputScales[18][3][1] = 109;
      inputScales[18][4][0] = 92;
      inputScales[18][4][1] = 8;
      inputScales[18][5][0] = 73;
      inputScales[18][5][1] = -9;
      inputScales[18][6][0] = 79;
      inputScales[18][6][1] = -21;
      inputScales[18][7][0] = -133;
      inputScales[18][7][1] = 39;
      inputScales[18][8][0] = 144;
      inputScales[18][8][1] = -142;
      inputScales[18][9][0] = 100;
      inputScales[18][9][1] = -15;
      inputScales[18][10][0] = -50;
      inputScales[18][10][1] = 39;
      inputScales[18][11][0] = 46;
      inputScales[18][11][1] = -30;
      inputScales[18][12][0] = -54;
      inputScales[18][12][1] = -81;
      inputScales[18][13][0] = 1;
      inputScales[18][13][1] = -51;
      inputScales[18][14][0] = 219;
      inputScales[18][14][1] = 90;
      inputScales[18][15][0] = 64;
      inputScales[18][15][1] = -57;
      inputScales[18][16][0] = -136;
      inputScales[18][16][1] = 28;
      inputScales[18][17][0] = -55;
      inputScales[18][17][1] = -133;
      inputScales[18][18][0] = -42;
      inputScales[18][18][1] = -111;
      inputScales[18][19][0] = 56;
      inputScales[18][19][1] = 95;
      inputScales[18][20][0] = 48;
      inputScales[18][20][1] = -184;
      inputScales[18][21][0] = 136;
      inputScales[18][21][1] = -43;
      inputScales[18][22][0] = -87;
      inputScales[18][22][1] = -109;
      inputScales[19][0][0] = -99;
      inputScales[19][0][1] = 76;
      inputScales[19][1][0] = 81;
      inputScales[19][1][1] = -36;
      inputScales[19][2][0] = -5;
      inputScales[19][2][1] = -53;
      inputScales[19][3][0] = 61;
      inputScales[19][3][1] = -12;
      inputScales[19][4][0] = 92;
      inputScales[19][4][1] = -70;
      inputScales[19][5][0] = 139;
      inputScales[19][5][1] = -59;
      inputScales[19][6][0] = 166;
      inputScales[19][6][1] = -19;
      inputScales[19][7][0] = 101;
      inputScales[19][7][1] = 25;
      inputScales[19][8][0] = 13;
      inputScales[19][8][1] = 129;
      inputScales[19][9][0] = -47;
      inputScales[19][9][1] = -47;
      inputScales[19][10][0] = -104;
      inputScales[19][10][1] = 4;
      inputScales[19][11][0] = 5;
      inputScales[19][11][1] = 70;
      inputScales[19][12][0] = 130;
      inputScales[19][12][1] = 164;
      inputScales[19][13][0] = 93;
      inputScales[19][13][1] = -16;
      inputScales[19][14][0] = -112;
      inputScales[19][14][1] = 128;
      inputScales[19][15][0] = 47;
      inputScales[19][15][1] = -124;
      inputScales[19][16][0] = 148;
      inputScales[19][16][1] = -107;
      inputScales[19][17][0] = 144;
      inputScales[19][17][1] = 83;
      inputScales[19][18][0] = 75;
      inputScales[19][18][1] = 61;
      inputScales[19][19][0] = -10;
      inputScales[19][19][1] = -103;
      inputScales[19][20][0] = 25;
      inputScales[19][20][1] = 65;
      inputScales[19][21][0] = -40;
      inputScales[19][21][1] = -88;
      inputScales[19][22][0] = 3;
      inputScales[19][22][1] = -1;
      inputScales[20][0][0] = -153;
      inputScales[20][0][1] = 136;
      inputScales[20][1][0] = -185;
      inputScales[20][1][1] = -40;
      inputScales[20][2][0] = -134;
      inputScales[20][2][1] = 107;
      inputScales[20][3][0] = 34;
      inputScales[20][3][1] = -44;
      inputScales[20][4][0] = -118;
      inputScales[20][4][1] = -177;
      inputScales[20][5][0] = -43;
      inputScales[20][5][1] = -121;
      inputScales[20][6][0] = -117;
      inputScales[20][6][1] = -57;
      inputScales[20][7][0] = 38;
      inputScales[20][7][1] = 83;
      inputScales[20][8][0] = -46;
      inputScales[20][8][1] = -129;
      inputScales[20][9][0] = -29;
      inputScales[20][9][1] = 196;
      inputScales[20][10][0] = 121;
      inputScales[20][10][1] = -127;
      inputScales[20][11][0] = 62;
      inputScales[20][11][1] = 40;
      inputScales[20][12][0] = 57;
      inputScales[20][12][1] = 95;
      inputScales[20][13][0] = -96;
      inputScales[20][13][1] = -166;
      inputScales[20][14][0] = -126;
      inputScales[20][14][1] = -104;
      inputScales[20][15][0] = -92;
      inputScales[20][15][1] = -65;
      inputScales[20][16][0] = -24;
      inputScales[20][16][1] = 79;
      inputScales[20][17][0] = -133;
      inputScales[20][17][1] = -145;
      inputScales[20][18][0] = -241;
      inputScales[20][18][1] = -155;
      inputScales[20][19][0] = 66;
      inputScales[20][19][1] = -16;
      inputScales[20][20][0] = -65;
      inputScales[20][20][1] = -41;
      inputScales[20][21][0] = -117;
      inputScales[20][21][1] = 96;
      inputScales[20][22][0] = -52;
      inputScales[20][22][1] = 6;
      inputScales[21][0][0] = -191;
      inputScales[21][0][1] = -137;
      inputScales[21][1][0] = -152;
      inputScales[21][1][1] = -1;
      inputScales[21][2][0] = 49;
      inputScales[21][2][1] = -5;
      inputScales[21][3][0] = -121;
      inputScales[21][3][1] = 69;
      inputScales[21][4][0] = -174;
      inputScales[21][4][1] = 112;
      inputScales[21][5][0] = 126;
      inputScales[21][5][1] = 89;
      inputScales[21][6][0] = -103;
      inputScales[21][6][1] = -59;
      inputScales[21][7][0] = -131;
      inputScales[21][7][1] = 109;
      inputScales[21][8][0] = -221;
      inputScales[21][8][1] = -150;
      inputScales[21][9][0] = -119;
      inputScales[21][9][1] = 116;
      inputScales[21][10][0] = 25;
      inputScales[21][10][1] = -13;
      inputScales[21][11][0] = 35;
      inputScales[21][11][1] = -180;
      inputScales[21][12][0] = -43;
      inputScales[21][12][1] = 66;
      inputScales[21][13][0] = -34;
      inputScales[21][13][1] = 164;
      inputScales[21][14][0] = -80;
      inputScales[21][14][1] = 132;
      inputScales[21][15][0] = -45;
      inputScales[21][15][1] = 43;
      inputScales[21][16][0] = 137;
      inputScales[21][16][1] = 123;
      inputScales[21][17][0] = 16;
      inputScales[21][17][1] = 145;
      inputScales[21][18][0] = 127;
      inputScales[21][18][1] = -80;
      inputScales[21][19][0] = 115;
      inputScales[21][19][1] = 98;
      inputScales[21][20][0] = 106;
      inputScales[21][20][1] = 102;
      inputScales[21][21][0] = 51;
      inputScales[21][21][1] = 52;
      inputScales[21][22][0] = 101;
      inputScales[21][22][1] = 78;
      inputScales[22][0][0] = 146;
      inputScales[22][0][1] = -92;
      inputScales[22][1][0] = -168;
      inputScales[22][1][1] = 134;
      inputScales[22][2][0] = -23;
      inputScales[22][2][1] = -186;
      inputScales[22][3][0] = 52;
      inputScales[22][3][1] = -136;
      inputScales[22][4][0] = -130;
      inputScales[22][4][1] = -137;
      inputScales[22][5][0] = -161;
      inputScales[22][5][1] = -122;
      inputScales[22][6][0] = -55;
      inputScales[22][6][1] = 72;
      inputScales[22][7][0] = 27;
      inputScales[22][7][1] = 146;
      inputScales[22][8][0] = -78;
      inputScales[22][8][1] = 160;
      inputScales[22][9][0] = -25;
      inputScales[22][9][1] = 44;
      inputScales[22][10][0] = 12;
      inputScales[22][10][1] = -103;
      inputScales[22][11][0] = -73;
      inputScales[22][11][1] = 139;
      inputScales[22][12][0] = -119;
      inputScales[22][12][1] = -73;
      inputScales[22][13][0] = -90;
      inputScales[22][13][1] = -54;
      inputScales[22][14][0] = -90;
      inputScales[22][14][1] = 42;
      inputScales[22][15][0] = -34;
      inputScales[22][15][1] = -146;
      inputScales[22][16][0] = -174;
      inputScales[22][16][1] = -53;
      inputScales[22][17][0] = 113;
      inputScales[22][17][1] = 68;
      inputScales[22][18][0] = -78;
      inputScales[22][18][1] = 58;
      inputScales[22][19][0] = -12;
      inputScales[22][19][1] = -37;
      inputScales[22][20][0] = 98;
      inputScales[22][20][1] = 44;
      inputScales[22][21][0] = 17;
      inputScales[22][21][1] = -92;
      inputScales[22][22][0] = 1;
      inputScales[22][22][1] = 99;
      biases[0][0] = -1989;
      biases[0][1] = -2156;
      biases[0][2] = 3102;
      biases[0][3] = 4012;
      biases[0][4] = 4010;
      biases[0][5] = 5097;
      biases[0][6] = 5082;
      biases[0][7] = 6198;
      biases[0][8] = -2060;
      biases[0][9] = -2941;
      biases[0][10] = 10;
      biases[0][11] = 33;
      biases[0][12] = 80;
      biases[0][13] = -20;
      biases[0][14] = 53;
      biases[0][15] = 66;
      biases[0][16] = -14;
      biases[0][17] = -2029;
      biases[0][18] = 46;
      biases[0][19] = 44;
      biases[0][20] = -59;
      biases[0][21] = -57;
      biases[0][22] = 5;
      biases[1][0] = -49;
      biases[1][1] = 95;
      biases[1][2] = 8;
      biases[1][3] = 44;
      biases[1][4] = -15;
      biases[1][5] = -43;
      biases[1][6] = -44;
      biases[1][7] = 7;
      biases[1][8] = -57;
      biases[1][9] = 108;
      biases[1][10] = 6;
      biases[1][11] = -75;
      biases[1][12] = -6;
      biases[1][13] = 63;
      biases[1][14] = -51;
      biases[1][15] = 23;
      biases[1][16] = 42;
      biases[1][17] = -44;
      biases[1][18] = -67;
      biases[1][19] = -26;
      biases[1][20] = 38;
      biases[1][21] = 52;
      biases[1][22] = 26;
      outputBias[0] = 100;
      outputBias[1] = -1;
      slopes[0][0][0] = 70;
      slopes[0][0][1] = 61;
      slopes[0][0][2] = 2124;
      slopes[0][0][3] = 920;
      slopes[0][0][4] = 958;
      slopes[0][0][5] = 1948;
      slopes[0][0][6] = 1174;
      slopes[0][0][7] = 954;
      slopes[0][0][8] = 82;
      slopes[0][0][9] = 303;
      slopes[0][0][10] = 24;
      slopes[0][0][11] = 4;
      slopes[0][0][12] = 8;
      slopes[0][0][13] = 98;
      slopes[0][0][14] = 1;
      slopes[0][0][15] = 47;
      slopes[0][0][16] = 24;
      slopes[0][0][17] = 25;
      slopes[0][0][18] = 60;
      slopes[0][0][19] = 73;
      slopes[0][0][20] = 81;
      slopes[0][0][21] = 4;
      slopes[0][0][22] = 49;
      slopes[0][1][0] = 1051;
      slopes[0][1][1] = 863;
      slopes[0][1][2] = 0;
      slopes[0][1][3] = 138;
      slopes[0][1][4] = 73;
      slopes[0][1][5] = 47;
      slopes[0][1][6] = 59;
      slopes[0][1][7] = 4;
      slopes[0][1][8] = 872;
      slopes[0][1][9] = 1078;
      slopes[0][1][10] = 66;
      slopes[0][1][11] = 4;
      slopes[0][1][12] = 6;
      slopes[0][1][13] = 1;
      slopes[0][1][14] = 16;
      slopes[0][1][15] = 1;
      slopes[0][1][16] = 38;
      slopes[0][1][17] = 21;
      slopes[0][1][18] = 43;
      slopes[0][1][19] = 36;
      slopes[0][1][20] = 56;
      slopes[0][1][21] = 18;
      slopes[0][1][22] = 1;
      slopes[1][0][0] = 35;
      slopes[1][0][1] = 62;
      slopes[1][0][2] = 82;
      slopes[1][0][3] = 24;
      slopes[1][0][4] = 69;
      slopes[1][0][5] = 11;
      slopes[1][0][6] = 49;
      slopes[1][0][7] = 96;
      slopes[1][0][8] = 74;
      slopes[1][0][9] = 9;
      slopes[1][0][10] = 1034;
      slopes[1][0][11] = 16;
      slopes[1][0][12] = 28;
      slopes[1][0][13] = 945;
      slopes[1][0][14] = 24;
      slopes[1][0][15] = 991;
      slopes[1][0][16] = 1;
      slopes[1][0][17] = 68;
      slopes[1][0][18] = 48;
      slopes[1][0][19] = 40;
      slopes[1][0][20] = 90;
      slopes[1][0][21] = 11;
      slopes[1][0][22] = 7;
      slopes[1][1][0] = 3;
      slopes[1][1][1] = 20;
      slopes[1][1][2] = 60;
      slopes[1][1][3] = 142;
      slopes[1][1][4] = 103;
      slopes[1][1][5] = 23;
      slopes[1][1][6] = 195;
      slopes[1][1][7] = 94;
      slopes[1][1][8] = 25;
      slopes[1][1][9] = 43;
      slopes[1][1][10] = 51;
      slopes[1][1][11] = 2029;
      slopes[1][1][12] = 1068;
      slopes[1][1][13] = 16;
      slopes[1][1][14] = 975;
      slopes[1][1][15] = 4;
      slopes[1][1][16] = 2102;
      slopes[1][1][17] = 3152;
      slopes[1][1][18] = 21;
      slopes[1][1][19] = 0;
      slopes[1][1][20] = 20;
      slopes[1][1][21] = 1;
      slopes[1][1][22] = 19;
      outputSlopes[0][0] = 985;
      outputSlopes[0][1] = 860;
      outputSlopes[1][0] = 982;
      outputSlopes[1][1] = 1054;
      residualScale = 573;
      residualAdjustment = -10;
      residualBaseline = -124;
  }

  int PReLU(int input, int negativeSlope, int positiveSlope) {
      int output = 0;
      if (input >= 0)
          output = input * positiveSlope / 1024;
      else
          output = input * negativeSlope / 1024;
      return output;
  }

  int calculateFinalLayers(bool W_IN[23], int n) {
      int outputSum = 0;
      for (int i = 0; i < 23; ++i) {
          int sum = 0;
          for (int j = 0; j < 23; ++j) {
              sum += inputScales[i][j][W_IN[j]];
          }
          outputSum += PReLU(sum + biases[n][i], slopes[n][0][i], slopes[n][1][i]);
      }
      return PReLU(outputSum + outputBias[n], outputSlopes[n][0], outputSlopes[n][1]);
  }

  int Store[2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2];

  int Lookup(bool W_IN[23], int n) {
      if (Store[n][W_IN[0]][W_IN[1]][W_IN[2]][W_IN[3]][W_IN[4]][W_IN[5]][W_IN[6]][W_IN[7]][W_IN[8]][W_IN[9]][W_IN[10]][W_IN[11]][W_IN[12]]
          [W_IN[13]][W_IN[14]][W_IN[15]][W_IN[16]][W_IN[17]][W_IN[18]][W_IN[19]][W_IN[20]][W_IN[21]][W_IN[22]] == 0) {
          Store[n][W_IN[0]][W_IN[1]][W_IN[2]][W_IN[3]][W_IN[4]][W_IN[5]][W_IN[6]][W_IN[7]][W_IN[8]][W_IN[9]][W_IN[10]][W_IN[11]][W_IN[12]]
              [W_IN[13]][W_IN[14]][W_IN[15]][W_IN[16]][W_IN[17]][W_IN[18]][W_IN[19]][W_IN[20]][W_IN[21]][W_IN[22]] = calculateFinalLayers(W_IN, n);
      }
      return Store[n][W_IN[0]][W_IN[1]][W_IN[2]][W_IN[3]][W_IN[4]][W_IN[5]][W_IN[6]][W_IN[7]][W_IN[8]][W_IN[9]][W_IN[10]][W_IN[11]][W_IN[12]]
          [W_IN[13]][W_IN[14]][W_IN[15]][W_IN[16]][W_IN[17]][W_IN[18]][W_IN[19]][W_IN[20]][W_IN[21]][W_IN[22]];
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
      Reductions[i] = int((reductionTableScale + std::log(Threads.size()) * 32) * std::log(i) + reductionTableAdjustment);
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
    int moveCount, captureCount, quietCount, improvement, step10Reduction;

    // Step 1. Initialize node
    Thread* thisThread = pos.this_thread();
    ss->inCheck        = pos.checkers();
    priorCapture       = pos.captured_piece();
    Color us           = pos.side_to_move();
    moveCount          = captureCount = quietCount = ss->moveCount = step10Reduction = 0;
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
        improvement = 0;
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

    // Set up the improvement variable, which is the difference between the current
    // static evaluation and the previous static evaluation at our turn (if we were
    // in check at our previous move we look at the move prior to it). The improvement
    // margin and the improving flag are used in various pruning heuristics.
    improvement =   (ss-2)->staticEval != VALUE_NONE ? ss->staticEval - (ss-2)->staticEval
                  : (ss-4)->staticEval != VALUE_NONE ? ss->staticEval - (ss-4)->staticEval
                  :                                    173;
    improving = improvement > 0;

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
        &&  eval - futility_margin(depth, cutNode && !ss->ttHit, improving) - (ss-1)->statScore / futilityPruningStatScoreDivisor >= beta
        &&  eval >= beta
        &&  eval < 24923) // larger than VALUE_KNOWN_WIN, but smaller than TB wins
        return eval;

    // Step 9. Null move search with verification search (~35 Elo)
    if (   !PvNode
        && (ss-1)->currentMove != MOVE_NULL
        && (ss-1)->statScore < nullMoveStatScoreThreshold
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
    if (PvNode
        && !ttMove) {
        depth -= 2 + 2 * (ss->ttHit && tte->depth() >= depth);
    }

    if (depth <= 0)
        return qsearch<PV>(pos, ss, alpha, beta);

    if (cutNode
        && depth >= 8
        && !ttMove) {
        depth -= 2;
    }

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

      int r = reduction(improvement, depth, moveCount, delta, thisThread->rootDelta);

      // Step 14. Pruning at shallow depth (~120 Elo). Depth conditions are important for mate finding.
      if (  !rootNode
          && pos.non_pawn_material(us)
          && bestValue > VALUE_TB_LOSS_IN_MAX_PLY)
      {
          // Skip quiet moves if movecount exceeds our FutilityMoveCount threshold (~8 Elo)
          moveCountPruning = moveCount >= futility_move_count(improving, depth);

          // Reduced depth of the next LMR search
          int lmrDepth = newDepth - (r * lmrDepthScale / 1024 / 1024);

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
      bool W_IN[23] = {};

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

          if (value < singularBeta)
          {
              W_IN[2] = true;
          }

          if (value < singularBeta - 21)
          {
              W_IN[3] = true;
              depth += depth < 13;
          }

          if (singularBeta >= beta && W_IN[2] == false)
              return singularBeta;
      }

      if (ttValue >= beta)
          W_IN[4] = true;

      if (PvNode)
          W_IN[5] = true;

      if (cutNode)
          W_IN[6] = true;

      if (1 <= depth && depth <= 4)
          W_IN[12] = true;

      if (5 <= depth && depth <= 9)
          W_IN[13] = true;

      if (10 <= depth && depth <= 14)
          W_IN[7] = true;

      if (15 <= depth && depth <= 19)
          W_IN[14] = true;

      if (20 <= depth)
          W_IN[15] = true;

      if (ttValue <= value)
          W_IN[8] = true;

      if (ttValue <= alpha)
          W_IN[9] = true;

      if (givesCheck)
          W_IN[10] = true;

      if (move == ss->killers[0]
          && (*contHist[0])[movedPiece][to_sq(move)] >= 5168)
          W_IN[11] = true;

      if (ttCapture)
          W_IN[16] = true;

      if (ttMove)
          W_IN[17] = true;

      if (move == ttMove)
          W_IN[18] = true;

      if ((ss+1)->cutoffCnt >= 4)
          W_IN[19] = true;

      if ((ss-1)->moveCount >= 9)
          W_IN[20] = true;

      if (ss->ttPv && !likelyFailLow)
          W_IN[21] = true;

      if (tte->depth() >= depth + 3)
          W_IN[22] = true;

      extension = Lookup(W_IN, 0);
      r += Lookup(W_IN, 1);

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

      ss->statScore =  (statScoreMainHistoryScale * thisThread->mainHistory[us][from_to(move)]
                     + statScoreContHistoryZero * (*contHist[0])[movedPiece][to_sq(move)]
                     + statScoreContHistoryOne * (*contHist[1])[movedPiece][to_sq(move)]
                     + statScoreContHistoryThree * (*contHist[3])[movedPiece][to_sq(move)]
                     + statScoreAdjustment);

      // Decrease/increase reduction for moves with a good/bad history (~25 Elo)
      r -= ss->statScore / (statScoreScale + statScoreDepthScale * (depth > statScoreDepthLower && depth < statScoreDepthUpper));

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
          int totalAdjustment = r * lmrDepthScaleTwo - extension * 1024 + (ss->residual);
          Depth d = std::clamp(initialDepth - (totalAdjustment / (1024 * 1024)), 1, newDepth + 1 + (r <= LMRDepthReductionThres));

          (ss+1)->residual = residualScale * (totalAdjustment % (1024 * 1024)) / 512 + residualAdjustment;
          value = -search<NonPV>(pos, ss+1, -(alpha+1), -alpha, d, true);
          (ss+1)->residual = residualBaseline;

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
