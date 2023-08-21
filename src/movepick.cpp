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

#include <cassert>

#include "bitboard.h"
#include "movepick.h"

namespace Stockfish {

namespace {

    const int PolicyMap[64][64] =
        {{0, 3033, 1804, 1310, 1002, 625, 842, 805, 9093, 553, 259, 0, 0, 0, 0, 0, 9855, 137, 314, 0, 0, 0, 0, 0, 6780, 0, 0, 356, 0, 0, 0, 0, 3185, 0, 0, 0, 175, 0, 0, 0, 1408, 0, 0, 0, 0, 175, 0, 0, 555, 0, 0, 0, 0, 0, 94, 0, 248, 0, 0, 0, 0, 0, 0, 75},
        {754, 0, 18870, 14579, 194, 208, 216, 235, 645, 710, 2189, 237, 0, 0, 0, 0, 135, 502, 345, 276, 0, 0, 0, 0, 0, 449, 0, 0, 211, 0, 0, 0, 0, 375, 0, 0, 0, 158, 0, 0, 0, 184, 0, 0, 0, 0, 96, 0, 0, 93, 0, 0, 0, 0, 0, 36, 0, 75, 0, 0, 0, 0, 0, 0},
        {373, 548, 0, 6083, 257, 270, 258, 208, 258, 979, 888, 3207, 1135, 0, 0, 0, 313, 931, 405, 1180, 688, 0, 0, 0, 0, 0, 357, 0, 0, 382, 0, 0, 0, 0, 228, 0, 0, 0, 401, 0, 0, 0, 159, 0, 0, 0, 0, 377, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0},
        {317, 288, 695, 0, 7773, 411, 579, 224, 0, 228, 1169, 724, 3304, 688, 0, 0, 0, 1039, 960, 994, 1122, 585, 0, 0, 468, 0, 0, 493, 0, 0, 577, 0, 0, 0, 0, 274, 0, 0, 0, 128, 0, 0, 0, 187, 0, 0, 0, 0, 0, 0, 0, 173, 0, 0, 0, 0, 0, 0, 0, 149, 0, 0, 0, 0},
        {189, 266, 204, 448, 0, 3276, 567, 400, 0, 0, 227, 559, 653, 1512, 228, 0, 0, 0, 415, 352, 437, 315, 233, 0, 0, 211, 0, 0, 324, 0, 0, 246, 189, 0, 0, 0, 261, 0, 0, 0, 0, 0, 0, 0, 129, 0, 0, 0, 0, 0, 0, 0, 86, 0, 0, 0, 0, 0, 0, 0, 123, 0, 0, 0},
        {121, 142, 177, 311, 758, 0, 1783, 355, 0, 0, 0, 99, 499, 653, 639, 65, 0, 0, 0, 241, 138, 366, 175, 132, 0, 0, 272, 0, 0, 277, 0, 0, 0, 218, 0, 0, 0, 193, 0, 0, 101, 0, 0, 0, 0, 115, 0, 0, 0, 0, 0, 0, 0, 115, 0, 0, 0, 0, 0, 0, 0, 79, 0, 0},
        {209, 209, 230, 448, 569, 922, 0, 1258, 0, 0, 0, 0, 219, 381, 890, 299, 0, 0, 0, 0, 224, 152, 590, 80, 0, 0, 0, 209, 0, 0, 392, 0, 0, 0, 189, 0, 0, 0, 419, 0, 0, 80, 0, 0, 0, 0, 257, 0, 41, 0, 0, 0, 0, 0, 204, 0, 0, 0, 0, 0, 0, 0, 152, 0},
        {97, 140, 94, 164, 195, 209, 903, 0, 0, 0, 0, 0, 0, 65, 326, 578, 0, 0, 0, 0, 0, 134, 13, 255, 0, 0, 0, 0, 115, 0, 0, 347, 0, 0, 0, 173, 0, 0, 0, 249, 0, 0, 155, 0, 0, 0, 0, 178, 0, 53, 0, 0, 0, 0, 0, 193, 21, 0, 0, 0, 0, 0, 0, 194},
        {2075, 1038, 3994, 0, 0, 0, 0, 0, 0, 1891, 1107, 797, 886, 687, 1186, 534, 2701, 1046, 26730, 0, 0, 0, 0, 0, 1764, 11988, 392, 0, 0, 0, 0, 0, 1068, 0, 0, 466, 0, 0, 0, 0, 610, 0, 0, 0, 283, 0, 0, 0, 292, 0, 0, 0, 0, 129, 0, 0, 207, 0, 0, 0, 0, 0, 37, 0},
        {1128, 594, 2579, 116, 0, 0, 0, 0, 865, 0, 17212, 10193, 302, 304, 354, 185, 1417, 1060, 6855, 265, 0, 0, 0, 0, 83, 600, 239, 1624, 0, 0, 0, 0, 0, 398, 0, 0, 1425, 0, 0, 0, 0, 203, 0, 0, 0, 966, 0, 0, 0, 108, 0, 0, 0, 0, 658, 0, 0, 48, 0, 0, 0, 0, 0, 59},
        {95, 647, 1092, 1917, 553, 0, 0, 0, 262, 737, 0, 6244, 735, 824, 805, 165, 263, 1733, 1425, 3625, 1342, 0, 0, 0, 968, 905, 493, 1248, 727, 0, 0, 0, 0, 0, 437, 0, 0, 534, 0, 0, 0, 0, 274, 0, 0, 0, 186, 0, 0, 0, 215, 0, 0, 0, 0, 46, 0, 0, 101, 0, 0, 0, 0, 0},
        {0, 86, 511, 595, 1487, 126, 0, 0, 239, 279, 564, 0, 5658, 340, 360, 213, 0, 150, 690, 569, 2543, 303, 0, 0, 0, 227, 367, 355, 174, 356, 0, 0, 261, 0, 0, 249, 0, 0, 238, 0, 0, 0, 0, 200, 0, 0, 0, 207, 0, 0, 0, 109, 0, 0, 0, 0, 0, 0, 0, 126, 0, 0, 0, 0},
        {0, 0, 488, 1189, 573, 1021, 567, 0, 305, 345, 365, 446, 0, 2622, 543, 379, 0, 0, 1181, 1668, 620, 3265, 709, 0, 0, 0, 1299, 1206, 435, 1141, 1086, 0, 0, 1239, 0, 0, 286, 0, 0, 322, 447, 0, 0, 0, 172, 0, 0, 0, 0, 0, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 148, 0, 0, 0},
        {0, 0, 0, 120, 462, 711, 455, 113, 192, 238, 263, 341, 575, 0, 1708, 327, 0, 0, 0, 357, 476, 617, 618, 216, 0, 0, 0, 366, 278, 283, 249, 171, 0, 0, 262, 0, 0, 203, 0, 0, 0, 123, 0, 0, 0, 148, 0, 0, 38, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0},
        {0, 0, 0, 0, 192, 682, 1008, 424, 236, 197, 422, 351, 500, 910, 0, 1184, 0, 0, 0, 0, 364, 497, 863, 464, 0, 0, 0, 0, 489, 238, 466, 116, 0, 0, 0, 292, 0, 0, 409, 0, 0, 0, 254, 0, 0, 0, 464, 0, 0, 122, 0, 0, 0, 0, 185, 0, 38, 0, 0, 0, 0, 0, 158, 0},
        {0, 0, 0, 0, 0, 58, 338, 544, 103, 146, 162, 182, 229, 287, 743, 0, 0, 0, 0, 0, 0, 64, 341, 554, 0, 0, 0, 0, 0, 180, 38, 214, 0, 0, 0, 0, 238, 0, 0, 225, 0, 0, 0, 166, 0, 0, 0, 173, 0, 0, 75, 0, 0, 0, 0, 195, 0, 49, 0, 0, 0, 0, 0, 130},
        {1454, 127, 2591, 0, 0, 0, 0, 0, 3960, 10329, 273, 0, 0, 0, 0, 0, 0, 3477, 2057, 1784, 1880, 1210, 1369, 1176, 3612, 9809, 419, 0, 0, 0, 0, 0, 1570, 267, 8645, 0, 0, 0, 0, 0, 812, 0, 0, 8553, 0, 0, 0, 0, 376, 0, 0, 0, 5414, 0, 0, 0, 323, 0, 0, 0, 0, 963, 0, 0},
        {64, 482, 266, 842, 0, 0, 0, 0, 1388, 1426, 2361, 448, 0, 0, 0, 0, 1559, 0, 16868, 23252, 492, 494, 579, 417, 1580, 2001, 2864, 410, 0, 0, 0, 0, 218, 1200, 560, 1371, 0, 0, 0, 0, 0, 369, 0, 0, 499, 0, 0, 0, 0, 187, 0, 0, 0, 355, 0, 0, 0, 133, 0, 0, 0, 0, 143, 0},
        {253, 772, 389, 3545, 529, 0, 0, 0, 1114, 1082, 1024, 2185, 4001, 0, 0, 0, 355, 1060, 0, 7110, 519, 387, 354, 241, 1025, 1380, 1156, 4519, 6266, 0, 0, 0, 490, 3371, 576, 5313, 774, 0, 0, 0, 0, 0, 320, 0, 0, 416, 0, 0, 0, 0, 234, 0, 0, 0, 265, 0, 0, 0, 89, 0, 0, 0, 0, 137},
        {0, 590, 297, 510, 631, 421, 0, 0, 0, 205, 2261, 723, 2836, 847, 0, 0, 441, 555, 780, 0, 5742, 544, 446, 272, 0, 665, 1987, 755, 12899, 1082, 0, 0, 0, 1677, 942, 309, 1324, 1164, 0, 0, 511, 0, 0, 417, 0, 0, 548, 0, 0, 0, 0, 199, 0, 0, 0, 95, 0, 0, 0, 187, 0, 0, 0, 0},
        {0, 0, 226, 169, 594, 332, 297, 0, 0, 0, 299, 466, 806, 1337, 520, 0, 284, 386, 306, 606, 0, 2568, 616, 404, 0, 0, 515, 597, 671, 1097, 536, 0, 0, 0, 286, 582, 392, 454, 302, 0, 0, 161, 0, 0, 302, 0, 0, 196, 78, 0, 0, 0, 212, 0, 0, 0, 0, 0, 0, 0, 167, 0, 0, 0},
        {0, 0, 0, 249, 248, 469, 147, 230, 0, 0, 0, 203, 481, 647, 651, 124, 229, 226, 182, 250, 642, 0, 1564, 443, 0, 0, 0, 298, 575, 591, 549, 237, 0, 0, 0, 293, 436, 245, 348, 314, 0, 0, 309, 0, 0, 173, 0, 0, 0, 154, 0, 0, 0, 171, 0, 0, 44, 0, 0, 0, 0, 44, 0, 0},
        {0, 0, 0, 0, 200, 101, 579, 156, 0, 0, 0, 0, 143, 430, 950, 434, 191, 218, 256, 366, 449, 712, 0, 1108, 0, 0, 0, 0, 380, 442, 625, 376, 0, 0, 0, 0, 339, 260, 526, 86, 0, 0, 0, 295, 0, 0, 445, 0, 0, 0, 158, 0, 0, 0, 299, 0, 0, 73, 0, 0, 0, 0, 228, 0},
        {0, 0, 0, 0, 0, 112, 87, 212, 0, 0, 0, 0, 0, 117, 332, 433, 151, 178, 142, 195, 268, 291, 872, 0, 0, 0, 0, 0, 0, 54, 313, 472, 0, 0, 0, 0, 0, 137, 65, 246, 0, 0, 0, 0, 232, 0, 0, 286, 0, 0, 0, 63, 0, 0, 0, 170, 0, 0, 47, 0, 0, 0, 0, 188},
        {1350, 0, 0, 4140, 0, 0, 0, 0, 2313, 183, 5300, 0, 0, 0, 0, 0, 5251, 8267, 575, 0, 0, 0, 0, 0, 0, 8526, 5127, 5021, 2297, 1558, 1572, 2859, 4637, 7819, 472, 0, 0, 0, 0, 0, 1446, 375, 3325, 0, 0, 0, 0, 0, 770, 0, 0, 1355, 0, 0, 0, 0, 504, 0, 0, 0, 1171, 0, 0, 0},
        {0, 314, 0, 0, 970, 0, 0, 0, 845, 665, 2927, 1601, 0, 0, 0, 0, 1735, 1985, 4440, 4290, 0, 0, 0, 0, 1336, 0, 13869, 31756, 628, 496, 543, 525, 2090, 1930, 3321, 4463, 0, 0, 0, 0, 1286, 574, 3468, 1516, 0, 0, 0, 0, 0, 282, 0, 0, 1021, 0, 0, 0, 0, 132, 0, 0, 0, 596, 0, 0},
        {0, 0, 301, 0, 0, 568, 0, 0, 638, 230, 545, 547, 1729, 0, 0, 0, 161, 2387, 1517, 3955, 748, 0, 0, 0, 632, 1626, 0, 5302, 515, 416, 360, 323, 195, 2829, 1733, 4805, 902, 0, 0, 0, 877, 367, 604, 630, 1410, 0, 0, 0, 0, 0, 409, 0, 0, 633, 0, 0, 0, 0, 203, 0, 0, 0, 599, 0},
        {164, 0, 0, 444, 0, 0, 286, 0, 0, 336, 1365, 365, 1361, 624, 0, 0, 0, 694, 1275, 967, 8392, 2429, 0, 0, 644, 644, 1223, 0, 7288, 423, 476, 399, 0, 722, 1444, 1063, 6886, 1102, 0, 0, 0, 300, 1416, 618, 1131, 532, 0, 0, 104, 0, 0, 288, 0, 0, 574, 0, 0, 0, 0, 384, 0, 0, 0, 94},
        {0, 203, 0, 0, 294, 0, 0, 198, 0, 0, 315, 322, 446, 374, 447, 0, 0, 0, 408, 760, 730, 2028, 428, 0, 241, 418, 377, 652, 0, 3063, 560, 466, 0, 0, 648, 849, 659, 1783, 616, 0, 0, 0, 343, 487, 352, 828, 349, 0, 0, 187, 0, 0, 153, 0, 0, 116, 90, 0, 0, 0, 236, 0, 0, 0},
        {0, 0, 134, 0, 0, 349, 0, 0, 0, 0, 0, 246, 233, 457, 396, 165, 0, 0, 0, 265, 477, 606, 564, 220, 211, 308, 224, 304, 591, 0, 1710, 441, 0, 0, 0, 307, 548, 601, 614, 177, 0, 0, 0, 366, 300, 279, 123, 204, 0, 0, 212, 0, 0, 278, 0, 0, 0, 46, 0, 0, 0, 195, 0, 0},
        {0, 0, 0, 121, 0, 0, 548, 0, 0, 0, 0, 0, 112, 223, 597, 76, 0, 0, 0, 0, 216, 335, 752, 404, 151, 275, 185, 257, 331, 687, 0, 894, 0, 0, 0, 0, 230, 231, 637, 342, 0, 0, 0, 0, 196, 118, 399, 140, 0, 0, 0, 146, 0, 0, 199, 0, 0, 0, 70, 0, 0, 0, 174, 0},
        {0, 0, 0, 0, 155, 0, 0, 349, 0, 0, 0, 0, 0, 100, 64, 277, 0, 0, 0, 0, 0, 49, 303, 520, 167, 174, 177, 208, 190, 231, 540, 0, 0, 0, 0, 0, 0, 63, 284, 392, 0, 0, 0, 0, 0, 160, 104, 262, 0, 0, 0, 0, 139, 0, 0, 180, 0, 0, 0, 89, 0, 0, 0, 176},
        {3818, 0, 0, 0, 202, 0, 0, 0, 1071, 0, 0, 305, 0, 0, 0, 0, 1558, 509, 691, 0, 0, 0, 0, 0, 5242, 3124, 904, 0, 0, 0, 0, 0, 0, 5169, 2014, 1781, 1297, 1008, 982, 997, 4283, 2423, 678, 0, 0, 0, 0, 0, 725, 295, 411, 0, 0, 0, 0, 0, 28176, 0, 0, 285, 0, 0, 0, 0},
        {0, 283, 0, 0, 0, 787, 0, 0, 0, 576, 0, 0, 1945, 0, 0, 0, 473, 951, 1284, 2890, 0, 0, 0, 0, 2552, 2688, 5637, 1989, 0, 0, 0, 0, 1567, 0, 25658, 17565, 685, 319, 456, 213, 3056, 1818, 5933, 2063, 0, 0, 0, 0, 367, 399, 1648, 1792, 0, 0, 0, 0, 0, 175, 0, 0, 1196, 0, 0, 0},
        {0, 0, 289, 0, 0, 0, 663, 0, 0, 0, 407, 0, 0, 859, 0, 0, 899, 292, 605, 687, 1634, 0, 0, 0, 264, 2553, 1782, 8752, 711, 0, 0, 0, 385, 1240, 0, 9386, 496, 317, 384, 362, 148, 1506, 1441, 3635, 585, 0, 0, 0, 146, 283, 358, 378, 1183, 0, 0, 0, 0, 0, 203, 0, 0, 624, 0, 0},
        {0, 0, 0, 240, 0, 0, 0, 204, 241, 0, 0, 255, 0, 0, 616, 0, 0, 565, 907, 339, 1099, 749, 0, 0, 0, 653, 1392, 1099, 6886, 943, 0, 0, 274, 470, 974, 0, 8423, 350, 299, 321, 0, 389, 1528, 971, 2691, 1284, 0, 0, 0, 226, 725, 415, 783, 339, 0, 0, 105, 0, 0, 309, 0, 0, 213, 0},
        {155, 0, 0, 0, 284, 0, 0, 0, 0, 297, 0, 0, 247, 0, 0, 238, 0, 0, 446, 976, 367, 1633, 544, 0, 0, 0, 1390, 994, 643, 1721, 1484, 0, 247, 286, 329, 678, 0, 2772, 454, 305, 0, 0, 1334, 948, 768, 2526, 583, 0, 0, 0, 510, 678, 293, 659, 340, 0, 0, 130, 0, 0, 269, 0, 0, 141},
        {0, 96, 0, 0, 0, 179, 0, 0, 0, 0, 137, 0, 0, 164, 0, 0, 0, 0, 0, 189, 228, 299, 184, 159, 0, 0, 0, 201, 416, 528, 530, 140, 132, 133, 158, 232, 712, 0, 1205, 202, 0, 0, 0, 181, 503, 572, 695, 266, 0, 0, 0, 155, 217, 289, 213, 91, 0, 0, 93, 0, 0, 173, 0, 0},
        {0, 0, 180, 0, 0, 0, 287, 0, 0, 0, 0, 116, 0, 0, 452, 0, 0, 0, 0, 0, 151, 191, 433, 101, 0, 0, 0, 0, 243, 332, 524, 378, 142, 167, 215, 213, 258, 621, 0, 857, 0, 0, 0, 0, 210, 421, 703, 304, 0, 0, 0, 0, 168, 153, 264, 37, 0, 0, 0, 117, 0, 0, 252, 0},
        {0, 0, 0, 53, 0, 0, 0, 212, 0, 0, 0, 0, 138, 0, 0, 215, 0, 0, 0, 0, 0, 120, 52, 169, 0, 0, 0, 0, 0, 79, 287, 285, 102, 130, 125, 184, 269, 252, 547, 0, 0, 0, 0, 0, 0, 94, 207, 350, 0, 0, 0, 0, 0, 117, 69, 177, 0, 0, 0, 0, 100, 0, 0, 256},
        {1111, 0, 0, 0, 0, 677, 0, 0, 1805, 0, 0, 0, 5434, 0, 0, 0, 3716, 0, 0, 6168, 0, 0, 0, 0, 7023, 353, 8121, 0, 0, 0, 0, 0, 12295, 14550, 646, 0, 0, 0, 0, 0, 0, 3397, 1634, 946, 766, 577, 517, 495, 3255, 12986, 534, 0, 0, 0, 0, 0, 610, 105, 770, 0, 0, 0, 0, 0},
        {0, 134, 0, 0, 0, 0, 69, 0, 0, 300, 0, 0, 0, 65, 0, 0, 0, 298, 0, 0, 189, 0, 0, 0, 156, 562, 247, 353, 0, 0, 0, 0, 1562, 1796, 4810, 293, 0, 0, 0, 0, 1551, 0, 13233, 10906, 260, 179, 232, 95, 1591, 1547, 2967, 258, 0, 0, 0, 0, 55, 192, 131, 236, 0, 0, 0, 0},
        {0, 0, 154, 0, 0, 0, 0, 200, 0, 0, 279, 0, 0, 0, 626, 0, 0, 0, 374, 0, 0, 769, 0, 0, 798, 5921, 496, 10171, 1069, 0, 0, 0, 1867, 2527, 1650, 4296, 12157, 0, 0, 0, 412, 1279, 0, 5524, 549, 458, 236, 190, 1033, 1629, 1660, 2165, 4679, 0, 0, 0, 231, 1203, 379, 3829, 707, 0, 0, 0},
        {0, 0, 0, 177, 0, 0, 0, 0, 0, 0, 0, 218, 0, 0, 0, 441, 465, 0, 0, 245, 0, 0, 707, 0, 0, 1170, 510, 369, 685, 1502, 0, 0, 0, 373, 2252, 898, 4770, 524, 0, 0, 164, 202, 820, 0, 4733, 393, 265, 175, 0, 117, 2178, 876, 2614, 365, 0, 0, 0, 508, 269, 391, 462, 721, 0, 0},
        {0, 0, 0, 0, 136, 0, 0, 0, 117, 0, 0, 0, 131, 0, 0, 0, 0, 143, 0, 0, 225, 0, 0, 237, 0, 0, 327, 363, 285, 247, 162, 0, 0, 0, 375, 593, 533, 1152, 417, 0, 108, 104, 323, 655, 0, 1840, 262, 207, 0, 0, 220, 480, 611, 1104, 241, 0, 0, 0, 186, 119, 353, 393, 112, 0},
        {69, 0, 0, 0, 0, 118, 0, 0, 0, 55, 0, 0, 0, 196, 0, 0, 0, 0, 115, 0, 0, 140, 0, 0, 0, 0, 0, 156, 143, 214, 151, 191, 0, 0, 0, 130, 349, 435, 517, 198, 83, 93, 200, 202, 424, 0, 1100, 192, 0, 0, 0, 126, 433, 536, 570, 85, 0, 0, 0, 100, 129, 269, 136, 138},
        {0, 79, 0, 0, 0, 0, 292, 0, 0, 0, 132, 0, 0, 0, 256, 0, 0, 0, 0, 174, 0, 0, 258, 0, 0, 0, 0, 0, 174, 167, 313, 108, 0, 0, 0, 0, 177, 347, 468, 286, 109, 109, 164, 177, 223, 603, 0, 673, 0, 0, 0, 0, 229, 294, 519, 222, 0, 0, 0, 0, 90, 155, 212, 84},
        {0, 0, 36, 0, 0, 0, 0, 129, 0, 0, 0, 63, 0, 0, 0, 156, 0, 0, 0, 0, 97, 0, 0, 157, 0, 0, 0, 0, 0, 92, 63, 168, 0, 0, 0, 0, 0, 83, 184, 310, 52, 68, 101, 122, 125, 175, 301, 0, 0, 0, 0, 0, 0, 84, 207, 335, 0, 0, 0, 0, 0, 120, 75, 137},
        {228, 0, 0, 0, 0, 0, 22, 0, 228, 0, 0, 0, 0, 24, 0, 0, 302, 0, 0, 0, 88, 0, 0, 0, 409, 0, 0, 155, 0, 0, 0, 0, 464, 4308, 132, 0, 0, 0, 0, 0, 7091, 5267, 35731, 0, 0, 0, 0, 0, 0, 7312, 607, 457, 328, 226, 318, 114, 7552, 7321, 1818, 0, 0, 0, 0, 0},
        {0, 57, 0, 0, 0, 0, 0, 276, 0, 76, 0, 0, 0, 0, 898, 0, 0, 146, 0, 0, 0, 1084, 0, 0, 0, 157, 0, 0, 1513, 0, 0, 0, 97, 244, 220, 1713, 0, 0, 0, 0, 3762, 1831, 6348, 173, 0, 0, 0, 0, 2451, 0, 22977, 8246, 100, 100, 96, 52, 1822, 1670, 3706, 117, 0, 0, 0, 0},
        {0, 0, 77, 0, 0, 0, 0, 0, 0, 0, 132, 0, 0, 0, 0, 127, 0, 0, 201, 0, 0, 0, 261, 0, 0, 0, 219, 0, 0, 405, 0, 0, 233, 488, 330, 593, 611, 0, 0, 0, 248, 1276, 1430, 3201, 724, 0, 0, 0, 188, 1120, 0, 7052, 261, 277, 214, 90, 52, 1112, 1184, 2189, 485, 0, 0, 0},
        {0, 0, 0, 145, 0, 0, 0, 0, 0, 0, 0, 130, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0, 0, 196, 226, 0, 0, 293, 0, 0, 249, 0, 0, 387, 223, 342, 341, 415, 0, 0, 0, 201, 716, 811, 2075, 273, 0, 0, 122, 147, 757, 0, 4676, 256, 246, 146, 0, 78, 693, 679, 1690, 165, 0, 0},
        {0, 0, 0, 0, 67, 0, 0, 0, 0, 0, 0, 0, 118, 0, 0, 0, 282, 0, 0, 0, 118, 0, 0, 0, 0, 656, 0, 0, 151, 0, 0, 322, 0, 0, 1166, 920, 222, 830, 827, 0, 0, 0, 1136, 1399, 423, 2763, 590, 0, 71, 84, 198, 337, 0, 1501, 132, 113, 0, 0, 469, 1357, 513, 1166, 293, 0},
        {0, 0, 0, 0, 0, 78, 0, 0, 93, 0, 0, 0, 0, 157, 0, 0, 0, 106, 0, 0, 0, 90, 0, 0, 0, 0, 97, 0, 0, 164, 0, 0, 0, 0, 0, 98, 183, 180, 180, 137, 0, 0, 0, 139, 364, 349, 435, 101, 45, 92, 196, 144, 419, 0, 924, 131, 0, 0, 0, 65, 279, 453, 312, 69},
        {35, 0, 0, 0, 0, 0, 154, 0, 0, 68, 0, 0, 0, 0, 150, 0, 0, 0, 75, 0, 0, 0, 172, 0, 0, 0, 0, 191, 0, 0, 134, 0, 0, 0, 0, 0, 99, 97, 235, 57, 0, 0, 0, 0, 129, 398, 404, 237, 69, 61, 135, 148, 162, 437, 0, 698, 0, 0, 0, 0, 85, 245, 461, 260},
        {0, 26, 0, 0, 0, 0, 0, 213, 0, 0, 52, 0, 0, 0, 0, 137, 0, 0, 0, 56, 0, 0, 0, 84, 0, 0, 0, 0, 136, 0, 0, 171, 0, 0, 0, 0, 0, 61, 12, 123, 0, 0, 0, 0, 0, 47, 123, 358, 56, 57, 59, 96, 77, 119, 312, 0, 0, 0, 0, 0, 0, 25, 171, 318},
        {356, 0, 0, 0, 0, 0, 0, 26, 520, 0, 0, 0, 0, 0, 34, 0, 817, 0, 0, 0, 0, 71, 0, 0, 1298, 0, 0, 0, 80, 0, 0, 0, 1457, 0, 0, 171, 0, 0, 0, 0, 1513, 77, 231, 0, 0, 0, 0, 0, 5483, 2164, 276, 0, 0, 0, 0, 0, 0, 2961, 869, 532, 391, 229, 157, 275},
        {0, 70, 0, 0, 0, 0, 0, 0, 0, 56, 0, 0, 0, 0, 0, 41, 0, 97, 0, 0, 0, 0, 94, 0, 0, 155, 0, 0, 0, 193, 0, 0, 0, 100, 0, 0, 150, 0, 0, 0, 164, 155, 300, 222, 0, 0, 0, 0, 2655, 2050, 3112, 289, 0, 0, 0, 0, 2079, 0, 22942, 12131, 115, 169, 111, 84},
        {0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 74, 0, 0, 0, 0, 0, 0, 0, 142, 0, 0, 0, 0, 93, 0, 0, 151, 0, 0, 0, 209, 0, 0, 0, 208, 0, 0, 294, 0, 0, 177, 297, 248, 745, 334, 0, 0, 0, 171, 1453, 1137, 2819, 317, 0, 0, 0, 130, 933, 0, 7534, 142, 171, 201, 140},
        {0, 0, 0, 76, 0, 0, 0, 0, 0, 0, 0, 115, 0, 0, 0, 0, 0, 0, 0, 145, 0, 0, 0, 0, 0, 0, 0, 149, 0, 0, 0, 130, 97, 0, 0, 305, 0, 0, 272, 0, 0, 227, 975, 368, 949, 415, 0, 0, 0, 226, 1335, 762, 2401, 484, 0, 0, 103, 120, 548, 0, 6536, 256, 217, 151},
        {0, 0, 0, 0, 114, 0, 0, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 0, 0, 0, 152, 0, 0, 0, 278, 0, 0, 0, 179, 0, 0, 0, 0, 506, 0, 0, 335, 0, 0, 170, 0, 0, 514, 177, 225, 166, 161, 0, 0, 0, 147, 667, 543, 1533, 128, 0, 120, 74, 231, 511, 0, 2470, 280, 314},
        {0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 66, 0, 0, 75, 0, 0, 0, 0, 87, 0, 0, 0, 274, 0, 0, 0, 134, 0, 0, 0, 0, 337, 0, 0, 124, 0, 0, 0, 0, 0, 346, 217, 220, 157, 216, 0, 0, 0, 81, 526, 438, 615, 27, 101, 104, 136, 216, 459, 0, 1406, 236},
        {0, 0, 0, 0, 0, 0, 188, 0, 59, 0, 0, 0, 0, 0, 146, 0, 0, 58, 0, 0, 0, 0, 111, 0, 0, 0, 176, 0, 0, 0, 162, 0, 0, 0, 0, 170, 0, 0, 192, 0, 0, 0, 0, 0, 150, 121, 200, 70, 0, 0, 0, 0, 161, 227, 366, 252, 56, 98, 71, 179, 291, 407, 0, 1195},
        {11, 0, 0, 0, 0, 0, 0, 159, 0, 41, 0, 0, 0, 0, 0, 145, 0, 0, 45, 0, 0, 0, 0, 193, 0, 0, 0, 83, 0, 0, 0, 187, 0, 0, 0, 0, 121, 0, 0, 150, 0, 0, 0, 0, 0, 110, 65, 162, 0, 0, 0, 0, 0, 33, 177, 380, 55, 57, 79, 124, 191, 167, 661, 0}};

  enum Stages {
    MAIN_TT, CAPTURE_INIT, GOOD_CAPTURE, REFUTATION, QUIET_INIT, QUIET, BAD_CAPTURE,
    EVASION_TT, EVASION_INIT, EVASION,
    PROBCUT_TT, PROBCUT_INIT, PROBCUT,
    QSEARCH_TT, QCAPTURE_INIT, QCAPTURE, QCHECK_INIT, QCHECK
  };

  // partial_insertion_sort() sorts moves in descending order up to and including
  // a given limit. The order of moves smaller than the limit is left unspecified.
  void partial_insertion_sort(ExtMove* begin, ExtMove* end, int limit) {

    for (ExtMove *sortedEnd = begin, *p = begin + 1; p < end; ++p)
        if (p->value >= limit)
        {
            ExtMove tmp = *p, *q;
            *p = *++sortedEnd;
            for (q = sortedEnd; q != begin && *(q - 1) < tmp; --q)
                *q = *(q - 1);
            *q = tmp;
        }
  }

} // namespace


/// Constructors of the MovePicker class. As arguments we pass information
/// to help it to return the (presumably) good moves first, to decide which
/// moves to return (in the quiescence search, for instance, we only want to
/// search captures, promotions, and some checks) and how important good move
/// ordering is at the current node.

/// MovePicker constructor for the main search
MovePicker::MovePicker(const Position& p, Move ttm, Depth d, const ButterflyHistory* mh,
                                                             const CapturePieceToHistory* cph,
                                                             const PieceToHistory** ch,
                                                             Move cm,
                                                             const Move* killers)
           : pos(p), mainHistory(mh), captureHistory(cph), continuationHistory(ch),
             ttMove(ttm), refutations{{killers[0], 0}, {killers[1], 0}, {cm, 0}}, depth(d)
{
  assert(d > 0);

  stage = (pos.checkers() ? EVASION_TT : MAIN_TT) +
          !(ttm && pos.pseudo_legal(ttm));
}

/// MovePicker constructor for quiescence search
MovePicker::MovePicker(const Position& p, Move ttm, Depth d, const ButterflyHistory* mh,
                                                             const CapturePieceToHistory* cph,
                                                             const PieceToHistory** ch,
                                                             Square rs)
           : pos(p), mainHistory(mh), captureHistory(cph), continuationHistory(ch), ttMove(ttm), recaptureSquare(rs), depth(d)
{
  assert(d <= 0);

  stage = (pos.checkers() ? EVASION_TT : QSEARCH_TT) +
          !(   ttm
            && pos.pseudo_legal(ttm));
}

/// MovePicker constructor for ProbCut: we generate captures with SEE greater
/// than or equal to the given threshold.
MovePicker::MovePicker(const Position& p, Move ttm, Value th, const CapturePieceToHistory* cph)
           : pos(p), captureHistory(cph), ttMove(ttm), threshold(th)
{
  assert(!pos.checkers());

  stage = PROBCUT_TT + !(ttm && pos.capture_stage(ttm)
                             && pos.pseudo_legal(ttm)
                             && pos.see_ge(ttm, threshold));
}

/// MovePicker::score() assigns a numerical value to each move in a list, used
/// for sorting. Captures are ordered by Most Valuable Victim (MVV), preferring
/// captures with a good history. Quiets moves are ordered using the history tables.
template<GenType Type>
void MovePicker::score() {

  static_assert(Type == CAPTURES || Type == QUIETS || Type == EVASIONS, "Wrong type");

  [[maybe_unused]] Bitboard threatenedByPawn, threatenedByMinor, threatenedByRook, threatenedPieces;
  if constexpr (Type == QUIETS)
  {
      Color us = pos.side_to_move();

      threatenedByPawn  = pos.attacks_by<PAWN>(~us);
      threatenedByMinor = pos.attacks_by<KNIGHT>(~us) | pos.attacks_by<BISHOP>(~us) | threatenedByPawn;
      threatenedByRook  = pos.attacks_by<ROOK>(~us) | threatenedByMinor;

      // Pieces threatened by pieces of lesser material value
      threatenedPieces = (pos.pieces(us, QUEEN) & threatenedByRook)
                       | (pos.pieces(us, ROOK)  & threatenedByMinor)
                       | (pos.pieces(us, KNIGHT, BISHOP) & threatenedByPawn);
  }

  for (auto& m : *this) {
      if constexpr (Type == CAPTURES)
          m.value = (7 * int(PieceValue[pos.piece_on(to_sq(m))])
              + (*captureHistory)[pos.moved_piece(m)][to_sq(m)][type_of(pos.piece_on(to_sq(m)))]) / 16;

      else if constexpr (Type == QUIETS)
      {
          Piece     pc = pos.moved_piece(m);
          PieceType pt = type_of(pos.moved_piece(m));
          Square    from = from_sq(m);
          Square    to = to_sq(m);

          // histories
          m.value = 2 * (*mainHistory)[pos.side_to_move()][from_to(m)];
          m.value += 2 * (*continuationHistory[0])[pc][to];
          m.value += (*continuationHistory[1])[pc][to];
          m.value += (*continuationHistory[3])[pc][to];
          m.value += (*continuationHistory[5])[pc][to];

          // bonus for checks
          m.value += bool(pos.check_squares(pt) & to) * 16384;

          // bonus for escaping from capture
          m.value += threatenedPieces & from ?
              (pt == QUEEN && !(to & threatenedByRook) ? 50000
                  : pt == ROOK && !(to & threatenedByMinor) ? 25000
                  : !(to & threatenedByPawn) ? 15000
                  : 0)
              : 0;

          // malus for putting piece en prise
          m.value -= !(threatenedPieces & from) ?
              (pt == QUEEN ? bool(to & threatenedByRook) * 50000
                  + bool(to & threatenedByMinor) * 10000
                  + bool(to & threatenedByPawn) * 20000
                  : pt == ROOK ? bool(to & threatenedByMinor) * 25000
                  + bool(to & threatenedByPawn) * 10000
                  : pt != PAWN ? bool(to & threatenedByPawn) * 15000
                  : 0)
              : 0;
      }

      else // Type == EVASIONS
      {
          if (pos.capture_stage(m))
              m.value = PieceValue[pos.piece_on(to_sq(m))]
              - Value(type_of(pos.moved_piece(m)))
              + (1 << 28);
          else
              m.value = (*mainHistory)[pos.side_to_move()][from_to(m)]
              + (*continuationHistory[0])[pos.moved_piece(m)][to_sq(m)];
      }
      dbg_mean_of(m.value);
      

      long long adjustment = (long long)(m.value) * (long long)(PolicyMap[int(from_sq(m))][int(to_sq(m))]) / (long long)(131072);
      m.value = m.value - adjustment; 
  }
}

/// MovePicker::select() returns the next move satisfying a predicate function.
/// It never returns the TT move.
template<MovePicker::PickType T, typename Pred>
Move MovePicker::select(Pred filter) {

  while (cur < endMoves)
  {
      if constexpr (T == Best)
          std::swap(*cur, *std::max_element(cur, endMoves));

      if (*cur != ttMove && filter())
          return *cur++;

      cur++;
  }
  return MOVE_NONE;
}

/// MovePicker::next_move() is the most important method of the MovePicker class. It
/// returns a new pseudo-legal move every time it is called until there are no more
/// moves left, picking the move with the highest score from a list of generated moves.
Move MovePicker::next_move(bool skipQuiets) {

top:
  switch (stage) {

  case MAIN_TT:
  case EVASION_TT:
  case QSEARCH_TT:
  case PROBCUT_TT:
      ++stage;
      return ttMove;

  case CAPTURE_INIT:
  case PROBCUT_INIT:
  case QCAPTURE_INIT:
      cur = endBadCaptures = moves;
      endMoves = generate<CAPTURES>(pos, cur);

      score<CAPTURES>();
      partial_insertion_sort(cur, endMoves, std::numeric_limits<int>::min());
      ++stage;
      goto top;

  case GOOD_CAPTURE:
      if (select<Next>([&](){
                       return pos.see_ge(*cur, Value(-cur->value)) ?
                              // Move losing capture to endBadCaptures to be tried later
                              true : (*endBadCaptures++ = *cur, false); }))
          return *(cur - 1);

      // Prepare the pointers to loop over the refutations array
      cur = std::begin(refutations);
      endMoves = std::end(refutations);

      // If the countermove is the same as a killer, skip it
      if (   refutations[0].move == refutations[2].move
          || refutations[1].move == refutations[2].move)
          --endMoves;

      ++stage;
      [[fallthrough]];

  case REFUTATION:
      if (select<Next>([&](){ return    *cur != MOVE_NONE
                                    && !pos.capture_stage(*cur)
                                    &&  pos.pseudo_legal(*cur); }))
          return *(cur - 1);
      ++stage;
      [[fallthrough]];

  case QUIET_INIT:
      if (!skipQuiets)
      {
          cur = endBadCaptures;
          endMoves = generate<QUIETS>(pos, cur);

          score<QUIETS>();
          partial_insertion_sort(cur, endMoves, -3000 * depth);
      }

      ++stage;
      [[fallthrough]];

  case QUIET:
      if (   !skipQuiets
          && select<Next>([&](){return   *cur != refutations[0].move
                                      && *cur != refutations[1].move
                                      && *cur != refutations[2].move;}))
          return *(cur - 1);

      // Prepare the pointers to loop over the bad captures
      cur = moves;
      endMoves = endBadCaptures;

      ++stage;
      [[fallthrough]];

  case BAD_CAPTURE:
      return select<Next>([](){ return true; });

  case EVASION_INIT:
      cur = moves;
      endMoves = generate<EVASIONS>(pos, cur);

      score<EVASIONS>();
      ++stage;
      [[fallthrough]];

  case EVASION:
      return select<Best>([](){ return true; });

  case PROBCUT:
      return select<Next>([&](){ return pos.see_ge(*cur, threshold); });

  case QCAPTURE:
      if (select<Next>([&](){ return   depth > DEPTH_QS_RECAPTURES
                                    || to_sq(*cur) == recaptureSquare; }))
          return *(cur - 1);

      // If we did not find any move and we do not try checks, we have finished
      if (depth != DEPTH_QS_CHECKS)
          return MOVE_NONE;

      ++stage;
      [[fallthrough]];

  case QCHECK_INIT:
      cur = moves;
      endMoves = generate<QUIET_CHECKS>(pos, cur);

      ++stage;
      [[fallthrough]];

  case QCHECK:
      return select<Next>([](){ return true; });
  }

  assert(false);
  return MOVE_NONE; // Silence warning
}

} // namespace Stockfish
