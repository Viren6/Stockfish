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

        int PolicyMap[64][2][6] =
        {
        { {982, 1576, 2013, 2087, 1225, 3646}, {74, 525, 82, 3949, 2962, 2567} },
        { {205, 245, 2103, 1260, 572, 0}, {2046, 41, 4103, 1063, 2120, 368} },
        { {286, 245, 2452, 2035, 63, 934}, {1430, 1767, 3416, 946, 2684, 82} },
        { {4826, 1061, 1063, 1464, 123, 243}, {3027, 1268, 0, 1362, 4981, 2483} },
        { {1306, 1104, 1876, 572, 1117, 286}, {1513, 2853, 286, 1452, 1798, 491} },
        { {1665, 5256, 41, 2548, 900, 41}, {41, 899, 1021, 2676, 1592, 1112} },
        { {4367, 450, 3633, 3679, 940, 1860}, {898, 2163, 736, 986, 573, 1717} },
        { {937, 3546, 523, 1385, 777, 1059}, {1785, 3102, 3821, 1186, 3912, 1888} },
        { {1145, 1063, 1553, 1985, 900, 2645}, {1506, 204, 2206, 41, 3176, 2604} },
        { {2044, 777, 405, 41, 0, 407}, {2119, 2000, 808, 2616, 1019, 3570} },
        { {1268, 3575, 1546, 2115, 538, 1632}, {4678, 327, 1023, 4180, 877, 3279} },
        { {3009, 491, 2204, 3097, 3532, 1306}, {450, 2779, 205, 3185, 1229, 2284} },
        { {3242, 1768, 2931, 871, 4567, 900}, {365, 2184, 4574, 82, 245, 242} },
        { {3573, 2173, 327, 1053, 1961, 490}, {3687, 307, 1848, 572, 777, 41} },
        { {531, 5386, 900, 491, 3056, 3727}, {2537, 1996, 1837, 327, 613, 5684} },
        { {1198, 3246, 1957, 3166, 1380, 794}, {4162, 1629, 2243, 1422, 1390, 2025} },
        { {286, 1142, 220, 2115, 324, 0}, {817, 3979, 4215, 491, 1996, 245} },
        { {368, 2706, 1425, 1517, 123, 3657}, {1944, 1542, 532, 1185, 327, 2126} },
        { {1232, 859, 1882, 2702, 1961, 613}, {424, 205, 2169, 0, 2114, 614} },
        { {2121, 2079, 5151, 654, 327, 4242}, {811, 39, 1060, 82, 1472, 0} },
        { {941, 450, 1917, 3089, 5003, 1785}, {1432, 309, 900, 4227, 777, 818} },
        { {899, 1851, 573, 532, 307, 2588}, {1840, 532, 1063, 3656, 327, 1961} },
        { {41, 1054, 0, 1550, 4749, 1470}, {1376, 1427, 2255, 1110, 1716, 4871} },
        { {368, 2996, 5617, 3082, 123, 731}, {1632, 533, 1052, 5107, 1338, 2622} },
        { {939, 1161, 450, 607, 0, 731}, {1023, 1092, 0, 41, 1308, 82} },
        { {1453, 4002, 3067, 2151, 532, 1674}, {3681, 1620, 981, 859, 1786, 531} },
        { {1636, 532, 1997, 2524, 777, 1138}, {1513, 3469, 980, 1186, 1387, 2647} },
        { {2450, 3072, 82, 2484, 1350, 1717}, {2783, 327, 2041, 123, 286, 41} },
        { {4059, 1714, 3697, 1493, 41, 2681}, {41, 2328, 1062, 2479, 399, 409} },
        { {0, 3641, 695, 1063, 695, 1483}, {4403, 2602, 123, 2515, 3408, 3722} },
        { {1103, 3121, 736, 1355, 1877, 1908}, {1738, 451, 407, 327, 1101, 286} },
        { {324, 1717, 2968, 1594, 2060, 1592}, {42, 41, 205, 82, 489, 817} },
        { {0, 573, 2031, 1775, 980, 1849}, {3343, 286, 41, 4122, 952, 3024} },
        { {2166, 164, 41, 926, 41, 2158}, {2532, 41, 205, 1186, 82, 3707} },
        { {1226, 926, 700, 82, 41, 2074}, {2802, 1403, 3146, 2114, 607, 4353} },
        { {1472, 2396, 3895, 1803, 1145, 532}, {1528, 3827, 532, 736, 2123, 1063} },
        { {654, 1874, 1089, 327, 2655, 558}, {2166, 1249, 81, 981, 286, 163} },
        { {7764, 1453, 570, 4905, 1766, 2637}, {123, 1592, 3937, 4582, 2858, 1634} },
        { {1862, 1389, 653, 41, 828, 6666}, {3561, 376, 1989, 2362, 1878, 954} },
        { {4227, 5287, 163, 2125, 164, 941}, {1227, 1799, 1472, 2077, 2891, 245} },
        { {1832, 1463, 3607, 736, 1023, 3828}, {35, 1794, 465, 3025, 654, 2076} },
        { {245, 1353, 2075, 5914, 318, 4936}, {3217, 1960, 532, 1541, 5983, 4837} },
        { {636, 2494, 1753, 981, 1799, 1022}, {2204, 4212, 82, 616, 909, 1063} },
        { {491, 82, 1343, 368, 1875, 4061}, {1102, 4847, 654, 736, 3210, 0} },
        { {918, 1424, 286, 570, 2561, 1186}, {1844, 654, 1635, 1238, 286, 981} },
        { {3084, 205, 614, 1425, 3008, 2762}, {5218, 245, 574, 1336, 1781, 846} },
        { {3001, 573, 2287, 1596, 1309, 1028}, {1506, 919, 1159, 490, 1592, 971} },
        { {122, 392, 2334, 1187, 1219, 4530}, {2708, 4640, 1639, 409, 2355, 491} },
        { {1028, 2568, 286, 1879, 4055, 1531}, {924, 2312, 1915, 1149, 1810, 2042} },
        { {1022, 2078, 123, 681, 3527, 777}, {4003, 82, 2856, 2741, 4157, 2438} },
        { {3504, 1962, 1704, 777, 1015, 945}, {1891, 1609, 6264, 0, 2156, 123} },
        { {1012, 3187, 734, 3191, 3114, 3211}, {2910, 1362, 2198, 1308, 409, 204} },
        { {3673, 2681, 1745, 2813, 123, 1924}, {368, 607, 1779, 2605, 4686, 204} },
        { {164, 3461, 1647, 286, 1423, 3432}, {3677, 1939, 532, 2696, 2725, 409} },
        { {859, 2003, 1584, 0, 450, 3361}, {496, 41, 1007, 3974, 2033, 1560} },
        { {1423, 793, 3053, 5180, 4595, 1639}, {286, 0, 515, 1550, 368, 1747} },
        { {1395, 5669, 3610, 2822, 409, 1796}, {41, 2114, 3182, 608, 1708, 647} },
        { {164, 818, 1321, 2890, 4642, 879}, {571, 736, 1490, 409, 1141, 245} },
        { {818, 3870, 858, 695, 1023, 1512}, {777, 314, 1095, 2239, 4184, 245} },
        { {2333, 3143, 5049, 654, 1859, 1880}, {3443, 2158, 319, 1341, 1227, 2717} },
        { {531, 1758, 41, 4029, 614, 900}, {4258, 935, 1303, 2341, 1056, 1542} },
        { {1768, 980, 816, 82, 2150, 2203}, {818, 3295, 1561, 41, 2453, 1472} },
        { {2367, 614, 409, 1468, 242, 736}, {82, 2045, 2910, 695, 2508, 1912} },
        { {1465, 1347, 610, 1471, 4763, 5457}, {5480, 4611, 408, 957, 2820, 4146} }
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

  for (auto& m : *this)
  {
      if constexpr (Type == CAPTURES)
          m.value =  (7 * int(PieceValue[pos.piece_on(to_sq(m))])
                   + (*captureHistory)[pos.moved_piece(m)][to_sq(m)][type_of(pos.piece_on(to_sq(m)))]) / 16;

      else if constexpr (Type == QUIETS)
      {
          Piece     pc   = pos.moved_piece(m);
          PieceType pt   = type_of(pos.moved_piece(m));
          Square    from = from_sq(m);
          Square    to   = to_sq(m);

          // histories
          m.value =  2 * (*mainHistory)[pos.side_to_move()][from_to(m)];
          m.value += 2 * (*continuationHistory[0])[pc][to];
          m.value +=     (*continuationHistory[1])[pc][to];
          m.value +=     (*continuationHistory[3])[pc][to];
          m.value +=     (*continuationHistory[5])[pc][to];

          // bonus for checks
          m.value += bool(pos.check_squares(pt) & to) * 16384;

          // bonus for escaping from capture
          m.value += threatenedPieces & from ?
                       (pt == QUEEN && !(to & threatenedByRook)  ? 50000
                      : pt == ROOK  && !(to & threatenedByMinor) ? 25000
                      :                !(to & threatenedByPawn)  ? 15000
                      :                                            0 )
                      :                                            0 ;

          // malus for putting piece en prise
          m.value -= !(threatenedPieces & from) ?
                        (pt == QUEEN ?   bool(to & threatenedByRook)  * 50000
                                       + bool(to & threatenedByMinor) * 10000
                                       + bool(to & threatenedByPawn)  * 20000
                       : pt == ROOK  ?   bool(to & threatenedByMinor) * 25000
                                       + bool(to & threatenedByPawn)  * 10000
                       : pt != PAWN ?    bool(to & threatenedByPawn)  * 15000
                       :                                                0 )
                       :                                                0 ;
      }
      
      else // Type == EVASIONS
      {
          if (pos.capture_stage(m))
              m.value =  PieceValue[pos.piece_on(to_sq(m))]
                       - Value(type_of(pos.moved_piece(m)))
                       + (1 << 28);
          else
              m.value =  (*mainHistory)[pos.side_to_move()][from_to(m)]
                       + (*continuationHistory[0])[pos.moved_piece(m)][to_sq(m)];
      }

      m.value += PolicyMap[int(from_sq(m))][0][(int(pos.moved_piece(m))-1) % 8] + PolicyMap[int(to_sq(m))][1][(int(pos.moved_piece(m)) - 1) % 8];
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
