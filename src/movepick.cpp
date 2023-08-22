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

        const int PolicyMap[64][64] = {
{0,-129,148,203,95,13,-53,-173,-284,57,1009,0,0,0,0,0,-222,1283,43,0,0,0,0,0,-124,0,0,238,0,0,0,0,-33,0,0,0,-119,0,0,0,-42,0,0,0,0,209,0,0,224,0,0,0,0,0,164,0,552,0,0,0,0,0,0,114},
{-229,0,-55,51,-84,-141,-207,-213,-50,-100,81,1351,0,0,0,0,209,-106,1453,-89,0,0,0,0,0,-117,0,0,85,0,0,0,0,26,0,0,0,-93,0,0,0,-29,0,0,0,0,-231,0,0,554,0,0,0,0,0,-382,0,197,0,0,0,0,0,0},
{-243,-118,0,-61,-147,-236,-231,-225,-47,509,-66,161,515,0,0,0,254,613,-76,1002,532,0,0,0,0,0,-51,0,0,190,0,0,0,0,103,0,0,0,43,0,0,0,26,0,0,0,0,-295,0,0,366,0,0,0,0,0,0,0,451,0,0,0,0,0},
{-207,-241,-147,0,-185,-246,-228,-207,0,42,40,-41,179,909,0,0,0,-21,483,-107,952,140,0,0,-73,0,0,47,0,0,-109,0,0,0,0,-39,0,0,0,-157,0,0,0,30,0,0,0,0,0,0,0,144,0,0,0,0,0,0,0,693,0,0,0,0},
{165,-212,-151,-182,0,-277,-169,1756,0,0,352,-147,-158,224,512,0,0,0,197,1044,-104,323,159,0,0,-136,0,0,-48,0,0,39,-148,0,0,0,30,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,290,0,0,0,0,0,0,0,539,0,0,0},
{-50,-135,106,246,98,0,-153,-191,0,0,0,183,516,-38,549,-261,0,0,0,323,1450,-32,710,-119,0,0,179,0,0,8,0,0,0,134,0,0,0,3,0,0,-217,0,0,0,0,-19,0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,461,0,0},
{-140,-169,-142,-104,-108,-198,0,-357,0,0,0,0,1339,116,198,-168,0,0,0,0,117,1557,-6,203,0,0,0,142,0,0,-77,0,0,0,-39,0,0,0,-53,0,0,-418,0,0,0,0,-87,0,-195,0,0,0,0,0,346,0,0,0,0,0,0,0,38,0},
{-19,44,248,385,121,-258,-194,0,0,0,0,0,0,474,428,-210,0,0,0,0,0,206,518,-202,0,0,0,0,15,0,0,-100,0,0,0,-134,0,0,0,-5,0,0,-14,0,0,0,0,-40,0,-269,0,0,0,0,0,-70,-210,0,0,0,0,0,0,473},
{-159,31,199,0,0,0,0,0,0,63,72,62,205,133,-129,-94,-115,1325,1142,0,0,0,0,0,-81,819,80,0,0,0,0,0,-112,0,0,3,0,0,0,0,-19,0,0,0,-58,0,0,0,194,0,0,0,0,-241,0,0,197,0,0,0,0,0,-338,0},
{-272,-218,-258,-114,0,0,0,0,-259,0,28,36,-107,-107,-13,-218,25,-115,475,1120,0,0,0,0,262,-138,1394,81,0,0,0,0,0,-26,0,0,84,0,0,0,0,42,0,0,0,97,0,0,0,497,0,0,0,0,282,0,0,164,0,0,0,0,0,-298},
{-456,-264,-225,-224,-185,0,0,0,-195,-75,0,-54,14,-60,-116,-52,-132,1,31,110,601,0,0,0,-173,242,11,255,16,0,0,0,0,0,-123,0,0,-223,0,0,0,0,-21,0,0,0,-216,0,0,0,255,0,0,0,0,-331,0,0,298,0,0,0,0,0},
{0,-355,-281,-322,-219,-140,0,0,-189,-89,-12,0,-22,-45,-13,-174,0,125,240,108,85,406,0,0,0,-40,355,242,280,-56,0,0,-115,0,0,-73,0,0,-114,0,0,0,0,88,0,0,0,-221,0,0,0,213,0,0,0,0,0,0,0,311,0,0,0,0},
{0,0,-311,-267,-357,-234,-316,0,-156,-91,-153,-70,0,-8,-58,-180,0,0,172,41,107,204,274,0,0,0,-19,474,61,424,-134,0,0,-100,0,0,2,0,0,-214,-254,0,0,0,-138,0,0,0,0,0,0,0,282,0,0,0,0,0,0,0,56,0,0,0},
{0,0,0,-192,-321,-354,-338,-390,-222,59,-40,102,-21,0,12,93,0,0,0,137,1198,-115,508,-239,0,0,0,103,195,-116,108,-124,0,0,-36,0,0,-35,0,0,0,-200,0,0,0,-62,0,0,-289,0,0,0,0,176,0,0,0,0,0,0,0,-5,0,0},
{0,0,0,0,-208,-206,-293,-440,-237,-225,-74,-85,128,171,0,-315,0,0,0,0,695,168,-177,-199,0,0,0,0,-53,416,-258,-49,0,0,0,16,0,0,-58,0,0,0,52,0,0,0,-27,0,0,314,0,0,0,0,8,0,-63,0,0,0,0,0,250,0},
{0,0,0,0,0,146,-145,-379,-22,-191,-1,181,-204,-96,481,0,0,0,0,0,0,493,805,-85,0,0,0,0,0,77,506,-146,0,0,0,0,8,0,0,-110,0,0,0,261,0,0,0,448,0,0,-35,0,0,0,0,402,0,-293,0,0,0,0,0,105},
{-16,-295,-185,0,0,0,0,0,-189,108,595,0,0,0,0,0,0,182,22,0,-46,59,92,-77,-58,1025,1139,0,0,0,0,0,-101,615,132,0,0,0,0,0,9,0,0,-44,0,0,0,0,242,0,0,0,116,0,0,0,243,0,0,0,0,188,0,0},
{-402,-181,-227,-37,0,0,0,0,-283,-79,46,141,0,0,0,0,-84,0,190,-73,19,131,166,3,134,-95,601,480,0,0,0,0,-58,-41,360,-97,0,0,0,0,0,-50,0,0,-82,0,0,0,0,198,0,0,0,-253,0,0,0,-80,0,0,0,0,-368,0},
{-176,-345,-151,-247,-207,0,0,0,-287,-103,-130,-92,111,0,0,0,-29,-74,0,14,37,-68,50,-207,-17,180,63,728,216,0,0,0,-201,-39,22,179,0,0,0,0,0,0,22,0,0,-48,0,0,0,0,258,0,0,0,-109,0,0,0,23,0,0,0,0,30},
{0,-223,-374,-164,-267,-209,0,0,0,-231,-68,-134,-71,54,0,0,-86,-45,-1,0,96,52,138,-39,0,-33,129,113,305,133,0,0,0,-63,223,-60,314,-124,0,0,-269,0,0,-28,0,0,-246,0,0,0,0,94,0,0,0,-162,0,0,0,58,0,0,0,0},
{0,0,-228,-270,-244,-346,-320,0,0,0,-140,-120,-188,-108,-98,0,-104,-89,-7,92,0,34,-16,-100,0,0,253,762,-3,125,-152,0,0,0,36,158,-3,0,-179,0,0,-95,0,0,-142,0,0,-289,-73,0,0,0,135,0,0,0,0,0,0,0,284,0,0,0},
{0,0,0,-179,-246,-82,-357,-312,0,0,0,29,-6,-104,-132,-277,-163,46,-29,-21,70,0,-12,-14,0,0,0,204,498,22,5,-236,0,0,0,-21,229,-136,-183,-225,0,0,26,0,0,-123,0,0,0,54,0,0,0,-171,0,0,-232,0,0,0,0,158,0,0},
{0,0,0,0,-172,-185,-2,-413,0,0,0,0,39,59,-120,-304,-181,11,6,-97,-12,116,0,-217,0,0,0,0,334,750,-216,240,0,0,0,0,36,233,-183,27,0,0,0,-52,0,0,-127,0,0,0,-104,0,0,0,-131,0,0,-268,0,0,0,0,-104,0},
{0,0,0,0,0,-183,-143,-165,0,0,0,0,0,332,373,-193,-111,-52,97,16,66,125,370,0,0,0,0,0,0,812,1127,-147,0,0,0,0,0,19,62,-175,0,0,0,0,10,0,0,-60,0,0,0,148,0,0,0,105,0,0,-176,0,0,0,0,189},
{-38,0,0,-39,0,0,0,0,-113,-41,287,0,0,0,0,0,-76,240,530,0,0,0,0,0,0,-97,-88,-51,11,-105,-83,2,297,1263,808,0,0,0,0,0,-120,147,62,0,0,0,0,0,207,0,0,387,0,0,0,0,31,0,0,0,-225,0,0,0},
{0,-68,0,0,-108,0,0,0,-201,-74,138,-106,0,0,0,0,-174,-29,199,702,0,0,0,0,-24,0,97,140,-64,-52,-260,-43,457,309,1169,393,0,0,0,0,-149,83,554,47,0,0,0,0,0,213,0,0,-63,0,0,0,0,56,0,0,0,-105,0,0},
{0,0,-64,0,0,-152,0,0,-84,-319,-40,-69,185,0,0,0,-274,74,-95,97,281,0,0,0,149,-98,0,-25,-132,14,-103,-7,-53,241,83,937,295,0,0,0,-287,-14,141,90,-17,0,0,0,0,0,188,0,0,-125,0,0,0,0,-3,0,0,0,-284,0},
{-286,0,0,-196,0,0,-316,0,0,-184,-149,-37,-108,-78,0,0,0,-21,10,-97,112,82,0,0,22,-67,-43,0,-8,101,-155,13,0,60,641,180,1262,-19,0,0,0,-68,203,-36,14,-128,0,0,-208,0,0,127,0,0,122,0,0,0,0,29,0,0,0,-300},
{0,-246,0,0,-233,0,0,-309,0,0,0,-43,-8,-35,-152,0,0,0,79,0,-84,126,69,0,86,-81,-1,91,0,1,-14,-31,0,0,211,983,345,511,-13,0,0,0,47,61,-74,205,-253,0,0,144,0,0,-51,0,0,-221,-200,0,0,0,139,0,0,0},
{0,0,-251,0,0,-109,0,0,0,0,0,27,3,-20,-262,-130,0,0,0,165,241,2,30,-146,74,-23,-38,61,51,0,-90,91,0,0,0,266,770,84,116,1,0,0,0,25,72,-37,-87,-214,0,0,-91,0,0,-68,0,0,0,-240,0,0,0,4,0,0},
{0,0,0,-201,0,0,-243,0,0,0,0,0,36,558,-126,-128,0,0,0,0,560,90,50,-163,261,-103,62,77,102,196,0,-129,0,0,0,0,614,830,262,575,0,0,0,0,84,394,-157,48,0,0,0,77,0,0,-59,0,0,0,-9,0,0,0,-30,0},
{0,0,0,0,-246,0,0,-196,0,0,0,0,0,210,230,-189,0,0,0,0,0,643,600,-170,-123,-42,-131,-131,4,52,131,0,0,0,0,0,0,578,1361,276,0,0,0,0,0,159,78,-86,0,0,0,0,201,0,0,-54,0,0,0,-78,0,0,0,-60},
{-90,0,0,0,1,0,0,0,-38,0,0,87,0,0,0,0,-170,600,437,0,0,0,0,0,-44,176,791,0,0,0,0,0,0,32,91,36,17,-243,-323,-81,524,1102,604,0,0,0,0,0,286,272,10,0,0,0,0,0,138,0,0,137,0,0,0,0},
{0,46,0,0,0,-122,0,0,0,12,0,0,132,0,0,0,-157,-72,332,137,0,0,0,0,-27,-132,222,521,0,0,0,0,-92,0,7,23,-6,-150,-230,-75,-72,260,667,222,0,0,0,0,-117,214,-28,100,0,0,0,0,0,133,0,0,-171,0,0,0},
{0,0,-145,0,0,0,-2,0,0,0,-109,0,0,230,0,0,-41,-70,-179,286,129,0,0,0,-222,-182,-92,267,354,0,0,0,160,20,0,-57,-26,-30,-178,-182,-121,403,312,454,74,0,0,0,-61,86,317,87,-55,0,0,0,0,0,70,0,0,-122,0,0},
{0,0,0,-244,0,0,0,-195,-128,0,0,-66,0,0,-135,0,0,-23,-79,-98,209,1,0,0,0,-115,32,-63,102,80,0,0,-6,21,19,0,-48,-29,-296,-52,0,-76,461,406,383,159,0,0,0,-32,-1,175,141,-142,0,0,-240,0,0,65,0,0,-322,0},
{-167,0,0,0,-90,0,0,0,0,-13,0,0,-47,0,0,-211,0,0,91,173,-48,142,59,0,0,0,26,160,-47,51,-112,0,26,-81,6,-52,0,5,-123,-50,0,0,231,380,267,737,-173,0,0,0,-38,158,193,-180,-65,0,0,-234,0,0,7,0,0,-188},
{0,-165,0,0,0,-113,0,0,0,0,-134,0,0,-192,0,0,0,0,0,116,322,34,48,-41,0,0,0,229,134,76,-21,-247,-72,-166,-131,-39,-11,0,-10,58,0,0,0,-29,424,353,427,194,0,0,0,-220,254,-6,-130,-286,0,0,-82,0,0,-49,0,0},
{0,0,-181,0,0,0,-15,0,0,0,0,-16,0,0,-77,0,0,0,0,0,319,483,150,8,0,0,0,0,522,172,-126,71,-176,87,-105,-52,23,88,0,122,0,0,0,0,222,617,204,79,0,0,0,0,194,-38,-99,-266,0,0,0,-44,0,0,-148,0},
{0,0,0,13,0,0,0,-135,0,0,0,0,449,0,0,-296,0,0,0,0,0,313,235,-54,0,0,0,0,0,218,189,13,93,0,-47,-19,127,-61,58,0,0,0,0,0,0,427,698,477,0,0,0,0,0,-219,39,-100,0,0,0,0,-111,0,0,83},
{-197,0,0,0,0,-165,0,0,-212,0,0,0,201,0,0,0,-206,0,0,306,0,0,0,0,-71,476,160,0,0,0,0,0,128,381,615,0,0,0,0,0,0,80,-37,-129,-193,-267,-233,-120,642,437,979,0,0,0,0,0,-17,-119,-154,0,0,0,0,0},
{0,-38,0,0,0,0,-230,0,0,-7,0,0,0,236,0,0,0,-97,0,0,237,0,0,0,-158,-116,799,290,0,0,0,0,1,-4,63,333,0,0,0,0,54,0,-33,-100,-243,-259,-241,-177,-149,557,198,172,0,0,0,0,-232,-58,1,-85,0,0,0,0},
{0,0,-26,0,0,0,0,-350,0,0,-113,0,0,0,55,0,0,0,-212,0,0,229,0,0,101,134,-154,233,130,0,0,0,18,77,123,135,372,0,0,0,234,55,0,-11,-77,-169,-97,-413,-193,188,472,-10,72,0,0,0,-175,-273,-9,-64,-25,0,0,0},
{0,0,0,-243,0,0,0,0,0,0,0,-56,0,0,0,-288,-102,0,0,-145,0,0,48,0,0,51,230,-115,495,247,0,0,0,40,97,42,184,81,0,0,121,92,76,0,-49,-127,-38,0,0,285,-4,495,159,-174,0,0,0,-244,-72,41,-101,-176,0,0},
{0,0,0,0,-205,0,0,0,-50,0,0,0,-219,0,0,0,0,107,0,0,-96,0,0,-122,0,0,106,290,43,268,-85,0,0,0,130,73,370,240,146,0,-21,-173,47,18,0,102,61,-99,0,0,83,82,498,326,92,0,0,0,-144,-13,-155,266,-314,0},
{-38,0,0,0,0,-248,0,0,0,-95,0,0,0,-191,0,0,0,0,152,0,0,-74,0,0,0,0,0,79,352,-34,394,-121,0,0,0,712,54,35,96,31,-55,38,-25,-47,31,0,157,136,0,0,0,285,134,526,156,278,0,0,0,-55,509,-152,-251,-175},
{0,44,0,0,0,0,-265,0,0,0,173,0,0,0,-120,0,0,0,0,-3,0,0,53,0,0,0,0,0,-191,544,-119,-189,0,0,0,0,516,155,112,-36,-91,198,-118,-19,-34,104,0,25,0,0,0,0,632,248,531,-129,0,0,0,0,-23,26,-95,-157},
{0,0,-227,0,0,0,0,-95,0,0,0,147,0,0,0,-27,0,0,0,0,180,0,0,-130,0,0,0,0,0,155,273,-105,0,0,0,0,0,673,216,53,-26,-311,-65,-43,-281,-55,12,0,0,0,0,0,0,300,271,520,0,0,0,0,0,-142,-421,-102},
{-112,0,0,0,0,0,-96,0,-150,0,0,0,0,228,0,0,-218,0,0,0,457,0,0,0,-58,0,0,300,0,0,0,0,18,2231,157,0,0,0,0,0,138,296,986,0,0,0,0,0,0,57,-24,-141,-132,-277,-175,-147,9,-51,89,0,0,0,0,0},
{0,-105,0,0,0,0,0,-266,0,-229,0,0,0,0,200,0,0,-50,0,0,0,490,0,0,0,-160,0,0,157,0,0,0,544,-126,1361,278,0,0,0,0,249,165,170,689,0,0,0,0,194,0,84,-156,-121,-67,-214,-218,-104,-112,-1,43,0,0,0,0},
{0,0,-281,0,0,0,0,0,0,0,-235,0,0,0,0,22,0,0,-160,0,0,0,171,0,0,0,-113,0,0,308,0,0,-14,104,-38,1070,296,0,0,0,-16,202,116,90,469,0,0,0,147,359,0,-6,-21,-71,-13,55,-51,-21,3,-109,-176,0,0,0},
{0,0,0,-368,0,0,0,0,0,0,0,-160,0,0,0,0,0,0,0,-302,0,0,0,87,15,0,0,-147,0,0,89,0,0,-86,840,-152,1001,214,0,0,0,700,228,88,0,129,0,0,183,169,194,0,32,41,-102,-36,0,-264,143,16,56,223,0,0},
{0,0,0,0,-389,0,0,0,0,0,0,0,-216,0,0,0,254,0,0,0,-148,0,0,0,0,-179,0,0,-158,0,0,-6,0,0,-89,1040,-150,751,5,0,0,0,501,75,122,269,361,0,-45,138,23,0,0,142,-33,54,0,0,42,147,13,-56,-354,0},
{0,0,0,0,0,-211,0,0,23,0,0,0,0,-175,0,0,0,86,0,0,0,-145,0,0,0,0,243,0,0,-176,0,0,0,0,0,246,610,-109,1027,-8,0,0,0,531,169,259,81,394,166,-5,24,45,36,0,143,-63,0,0,0,11,-153,-20,-139,-105},
{-45,0,0,0,0,0,-266,0,0,-45,0,0,0,0,-310,0,0,0,10,0,0,0,-131,0,0,0,0,726,0,0,-57,0,0,0,0,0,-67,1190,-111,274,0,0,0,0,866,437,205,54,259,-108,-49,-139,-1,105,0,124,0,0,0,0,344,-72,-132,-18},
{0,0,0,0,0,0,0,-132,0,0,-60,0,0,0,0,34,0,0,0,686,0,0,0,-282,0,0,0,0,409,0,0,-34,0,0,0,0,0,241,2267,165,0,0,0,0,0,1794,237,47,264,162,-176,-169,-103,-134,116,0,0,0,0,0,0,663,106,246},
{-88,0,0,0,0,0,0,-346,-47,0,0,0,0,0,-24,0,-257,0,0,0,0,844,0,0,-100,0,0,0,460,0,0,0,-125,0,0,231,0,0,0,0,-105,2514,189,0,0,0,0,0,737,591,-21,0,0,0,0,0,0,43,-165,27,-84,-204,-155,-137},
{0,-273,0,0,0,0,0,0,0,-169,0,0,0,0,0,134,0,-140,0,0,0,0,173,0,0,-166,0,0,0,434,0,0,0,-100,0,0,456,0,0,0,471,8,919,169,0,0,0,0,233,680,384,682,0,0,0,0,41,0,180,-164,-163,-218,-193,-295},
{0,0,-46,0,0,0,0,0,0,0,-9,0,0,0,0,0,0,0,-190,0,0,0,0,-209,0,0,-11,0,0,0,-127,0,0,0,1,0,0,609,0,0,-7,1151,-42,173,133,0,0,0,680,637,797,390,35,0,0,0,-198,-38,0,12,-146,-37,-201,-151},
{0,0,0,-74,0,0,0,0,0,0,0,-79,0,0,0,0,0,0,0,-72,0,0,0,0,0,0,0,32,0,0,0,-11,132,0,0,-77,0,0,351,0,0,-71,538,-98,547,182,0,0,0,271,298,343,433,625,0,0,116,-61,89,0,40,10,-206,-128},
{0,0,0,0,-65,0,0,0,0,0,0,0,-32,0,0,0,0,0,0,0,-42,0,0,0,-181,0,0,0,60,0,0,0,0,78,0,0,206,0,0,237,0,0,-100,698,-41,1262,76,0,0,0,217,368,631,261,424,0,-99,-15,-264,-160,0,55,-182,-1},
{0,0,0,0,0,-235,0,0,0,0,0,0,0,-113,0,0,-11,0,0,0,0,-62,0,0,0,-97,0,0,0,245,0,0,0,0,-112,0,0,25,0,0,0,0,0,59,797,-13,629,193,0,0,0,124,249,577,280,326,-179,-31,-128,-97,151,0,139,-167},
{0,0,0,0,0,0,202,0,-294,0,0,0,0,0,162,0,0,-79,0,0,0,0,-156,0,0,0,161,0,0,0,-35,0,0,0,0,729,0,0,-121,0,0,0,0,0,-151,2013,-263,424,0,0,0,0,-365,81,427,177,263,-85,-270,99,-144,340,0,89},
{-359,0,0,0,0,0,0,-211,0,224,0,0,0,0,0,-181,0,0,-85,0,0,0,0,-183,0,0,0,98,0,0,0,-107,0,0,0,0,577,0,0,26,0,0,0,0,0,33,731,-77,0,0,0,0,0,1845,399,679,14,-35,59,-14,-79,-149,245,0}
        };

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

      m.value += PolicyMap[int(from_sq(m))][int(to_sq(m))];
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
