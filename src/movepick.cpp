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
            {{982, 1413, 2259, 2577, 654, 2910}, {163, 572, 979, 4523, 2389, 2486}},
            {{286, 653, 2021, 326, 817, 82}, {738, 1512, 2713, 2043, 3919, 777}},
            {{1348, 1389, 2371, 3261, 449, 689}, {2900, 2259, 3008, 1470, 1948, 41}},
            {{6052, 163, 0, 1381, 368, 82}, {3026, 612, 2575, 709, 4900, 2402}},
            {{2367, 942, 1059, 490, 2506, 1389}, {1267, 3915, 775, 2433, 2942, 2208}},
            {{2238, 6973, 1267, 2140, 82, 1348}, {653, 735, 245, 2758, 531, 612}},
            {{4777, 859, 1180, 2943, 3147, 1124}, {572, 1918, 1553, 735, 82, 1636}},
            {{1019, 4773, 612, 1304, 41, 1059}, {1293, 3182, 3739, 1676, 2931, 2297}},
            {{1555, 2697, 1633, 1741, 613, 3707}, {1260, 1267, 982, 531, 3749, 1705}},
            {{1883, 1675, 287, 449, 653, 163}, {402, 1348, 725, 612, 1756, 4715}},
            {{1187, 5863, 2363, 2360, 1192, 41}, {4432, 613, 859, 4345, 386, 4177}},
            {{3581, 1061, 4411, 3751, 3043, 327}, {367, 1634, 286, 1304, 2209, 3101}},
            {{1853, 1442, 1052, 544, 3750, 2043}, {1877, 1774, 3919, 245, 82, 41}},
            {{3573, 2008, 817, 82, 3758, 695}, {3687, 1471, 1357, 247, 1511, 163}},
            {{1676, 5060, 1144, 1022, 4118, 3565}, {2536, 1097, 2408, 82, 533, 5521}},
            {{2668, 2593, 2611, 2268, 1185, 2429}, {4079, 1138, 2242, 3056, 2616, 3086}},
            {{1512, 1059, 793, 2034, 406, 612}, {2533, 3732, 5439, 530, 1587, 1308}},
            {{1838, 1888, 1178, 1353, 694, 5781}, {2681, 0, 163, 3474, 491, 1225}},
            {{2213, 1186, 1881, 3193, 0, 695}, {1241, 408, 1518, 82, 2686, 82}},
            {{812, 1181, 6458, 367, 449, 5141}, {1546, 1023, 815, 0, 981, 1227}},
            {{285, 777, 529, 2599, 6227, 1048}, {2985, 653, 1800, 2755, 408, 490}},
            {{1962, 2586, 775, 859, 694, 1362}, {1839, 941, 0, 5208, 367, 1144}},
            {{1349, 1544, 1349, 162, 5403, 326}, {1703, 530, 1926, 408, 1716, 6586}},
            {{2494, 4630, 3410, 4798, 0, 2855}, {1469, 1431, 326, 5435, 2892, 3276}},
            {{163, 1569, 1266, 1587, 940, 980}, {3638, 163, 490, 2657, 2289, 41}},
            {{1618, 4247, 1188, 1007, 409, 2000}, {4580, 2601, 981, 1922, 641, 1022}},
            {{737, 2247, 1996, 3504, 942, 245}, {1266, 4124, 204, 859, 1304, 2892}},
            {{980, 1682, 449, 3220, 3149, 1636}, {2291, 41, 2859, 163, 1267, 940}},
            {{3486, 2041, 3042, 1738, 572, 1538}, {491, 3227, 2207, 1743, 971, 82}},
            {{1102, 2415, 0, 410, 2248, 2136}, {4239, 1948, 736, 2351, 5124, 4540}},
            {{2330, 4265, 900, 2499, 1714, 1009}, {2555, 449, 1961, 654, 858, 204}},
            {{1103, 2863, 3458, 2903, 2223, 1837}, {1511, 817, 0, 83, 82, 489}},
            {{163, 163, 1052, 1448, 2369, 1195}, {4569, 858, 2737, 3061, 899, 1799}},
            {{2656, 818, 1430, 518, 0, 2485}, {2369, 1594, 939, 82, 204, 4523}},
            {{2125, 1090, 0, 0, 1104, 847}, {5336, 285, 1183, 1950, 613, 6396}},
            {{1392, 2070, 3732, 286, 655, 2452}, {2753, 4644, 43, 0, 1060, 409}},
            {{1635, 2118, 857, 0, 2655, 82}, {449, 2474, 694, 1799, 124, 940}},
            {{7765, 1209, 82, 1800, 163, 1084}, {83, 3310, 4754, 4500, 3675, 1716}},
            {{1533, 1634, 42, 3228, 1348, 4540}, {3396, 0, 681, 2118, 2204, 2508}},
            {{5617, 5614, 328, 2778, 2943, 204}, {737, 3026, 2617, 363, 3381, 245}},
            {{1996, 1381, 4589, 1310, 2002, 5707}, {1103, 2202, 547, 2288, 1062, 3384}},
            {{2247, 1517, 3301, 6895, 939, 4854}, {4363, 82, 940, 3502, 6721, 3612}},
            {{1144, 1757, 611, 1963, 1555, 1676}, {1633, 3885, 206, 2333, 0, 163}},
            {{492, 654, 444, 817, 1384, 4716}, {2899, 4438, 1554, 492, 4435, 738}},
            {{0, 2078, 491, 204, 2971, 1350}, {2743, 204, 819, 1974, 408, 1308}},
            {{4473, 777, 163, 531, 3172, 2679}, {5709, 0, 122, 1662, 2026, 1580}},
            {{2264, 982, 2696, 2332, 2208, 375}, {1342, 186, 1388, 1226, 1919, 2034}},
            {{326, 163, 1680, 286, 1219, 4446}, {2463, 5703, 1394, 983, 3501, 328}},
            {{1275, 4366, 490, 1716, 4298, 2185}, {163, 2722, 2406, 775, 1156, 3513}},
            {{1676, 2161, 0, 928, 4752, 368}, {3675, 245, 2286, 1842, 2603, 1538}},
            {{5222, 3269, 641, 1268, 694, 1435}, {2136, 2264, 6836, 326, 1991, 819}},
            {{1829, 3025, 530, 2865, 3688, 2476}, {4136, 1281, 1709, 819, 573, 899}},
            {{3755, 2518, 1090, 5101, 326, 2823}, {204, 449, 1453, 1787, 6073, 695}},
            {{41, 3216, 1891, 531, 2158, 2613}, {2697, 1695, 1103, 4248, 3788, 981}},
            {{2086, 2249, 1667, 1512, 41, 4178}, {578, 1553, 2641, 4873, 1378, 2948}},
            {{688, 82, 5178, 3381, 4759, 1883}, {1226, 410, 1252, 1140, 163, 1665}},
            {{1395, 3954, 3611, 2740, 367, 2695}, {490, 3994, 3101, 204, 163, 77}},
            {{204, 2697, 3036, 3462, 6277, 633}, {898, 449, 1736, 694, 1795, 1797}},
            {{328, 5666, 694, 2083, 449, 2492}, {326, 2030, 768, 2238, 4840, 2535}},
            {{3314, 3470, 6521, 204, 3331, 819}, {3852, 1750, 245, 1505, 4741, 3860}},
            {{777, 1268, 327, 3212, 82, 2126}, {2622, 614, 3510, 2832, 1464, 1543}},
            {{2012, 652, 2369, 450, 2638, 1794}, {2779, 2397, 3116, 1266, 3023, 83}},
            {{5227, 43, 326, 733, 243, 2043}, {163, 1472, 5608, 82, 3651, 3628}},
            {{1957, 2328, 1345, 1145, 4681, 4475}, {6381, 4775, 939, 1692, 2820, 4473}}
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
