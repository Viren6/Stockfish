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

#include "movepick.h"

#include <algorithm>
#include <cassert>
#include <iterator>
#include <utility>

#include "bitboard.h"
#include "position.h"

namespace Stockfish {

namespace {

    int PolicyMap[64][2][6] =
    {
        {{160, 218, 390, 694, 334, 694}, {165, 213, 14, 215, 590, 188}},
        {{538, 134, 384, 576, 900, 334}, {239, 0, 25, 415, 701, 385}},
        {{78, 213, 363, 614, 382, 203}, {217, 222, 203, 261, 186, 335}},
        {{565, 625, 235, 281, 290, 307}, {306, 8, 189, 246, 76, 379}},
        {{131, 709, 88, 89, 534, 50}, {206, 523, 641, 206, 75, 163}},
        {{187, 610, 479, 780, 594, 218}, {227, 475, 628, 87, 716, 489}},
        {{497, 636, 924, 20, 214, 120}, {668, 617, 169, 37, 796, 716}},
        {{205, 42, 84, 157, 317, 148}, {179, 11, 38, 1180, 834, 642}},
        {{301, 296, 49, 106, 410, 181}, {425, 396, 582, 169, 371, 15}},
        {{493, 322, 842, 209, 275, 379}, {349, 339, 575, 542, 364, 255}},
        {{376, 218, 543, 1109, 637, 487}, {77, 451, 170, 206, 377, 130}},
        {{416, 221, 273, 492, 282, 240}, {103, 807, 814, 553, 588, 13}},
        {{36, 159, 593, 378, 204, 101}, {194, 97, 541, 153, 316, 662}},
        {{825, 293, 491, 281, 574, 303}, {811, 27, 121, 337, 181, 142}},
        {{801, 176, 400, 252, 759, 62}, {469, 347, 93, 291, 105, 378}},
        {{445, 20, 256, 72, 0, 238}, {410, 314, 139, 370, 839, 250}},
        {{101, 147, 345, 203, 11, 375}, {33, 345, 184, 197, 407, 88}},
        {{73, 42, 86, 329, 132, 235}, {192, 696, 73, 842, 116, 389}},
        {{29, 498, 229, 0, 1026, 383}, {684, 75, 129, 268, 103, 222}},
        {{314, 46, 127, 56, 106, 276}, {159, 518, 55, 366, 286, 91}},
        {{629, 7, 353, 131, 99, 477}, {188, 295, 318, 351, 142, 838}},
        {{0, 3, 0, 439, 247, 730}, {324, 819, 208, 176, 158, 305}},
        {{0, 168, 582, 199, 549, 46}, {60, 684, 218, 609, 566, 862}},
        {{346, 244, 764, 380, 20, 437}, {79, 256, 307, 549, 87, 196}},
        {{102, 1082, 106, 35, 96, 0}, {576, 280, 109, 121, 99, 889}},
        {{174, 137, 247, 275, 993, 828}, {149, 791, 237, 91, 564, 177}},
        {{290, 445, 269, 576, 74, 324}, {217, 716, 372, 206, 877, 183}},
        {{360, 253, 220, 185, 96, 22}, {114, 61, 29, 309, 84, 378}},
        {{411, 303, 84, 331, 60, 457}, {115, 42, 486, 150, 386, 339}},
        {{29, 26, 149, 377, 52, 711}, {312, 839, 299, 256, 628, 106}},
        {{572, 135, 186, 704, 546, 201}, {676, 941, 24, 172, 176, 592}},
        {{592, 664, 132, 38, 119, 139}, {82, 232, 122, 409, 379, 59}},
        {{174, 594, 135, 115, 140, 142}, {358, 567, 539, 330, 308, 146}},
        {{130, 321, 373, 193, 247, 298}, {38, 397, 226, 258, 263, 117}},
        {{428, 206, 279, 91, 173, 251}, {263, 410, 141, 95, 48, 343}},
        {{168, 278, 212, 303, 375, 46}, {25, 181, 219, 410, 46, 176}},
        {{356, 75, 263, 78, 254, 572}, {85, 628, 295, 316, 205, 206}},
        {{887, 115, 368, 104, 337, 258}, {16, 691, 698, 381, 131, 231}},
        {{105, 256, 174, 248, 670, 804}, {721, 446, 265, 88, 77, 459}},
        {{683, 110, 267, 289, 203, 435}, {132, 483, 234, 162, 49, 521}},
        {{357, 234, 210, 0, 75, 230}, {151, 299, 40, 652, 326, 11}},
        {{671, 972, 170, 106, 508, 413}, {105, 602, 0, 259, 270, 414}},
        {{28, 11, 268, 13, 71, 402}, {422, 144, 419, 64, 13, 504}},
        {{550, 355, 452, 230, 84, 651}, {296, 401, 1002, 337, 279, 290}},
        {{465, 96, 49, 548, 157, 551}, {395, 104, 929, 158, 220, 448}},
        {{266, 141, 270, 722, 106, 130}, {638, 120, 321, 15, 219, 155}},
        {{502, 93, 13, 33, 164, 385}, {485, 330, 626, 312, 170, 107}},
        {{873, 294, 186, 722, 107, 353}, {612, 184, 46, 137, 81, 24}},
        {{235, 69, 347, 359, 16, 138}, {0, 482, 353, 106, 0, 405}},
        {{276, 330, 155, 986, 843, 560}, {169, 113, 95, 207, 540, 24}},
        {{730, 209, 843, 57, 285, 679}, {532, 215, 75, 90, 558, 308}},
        {{7, 43, 312, 116, 876, 347}, {257, 25, 456, 304, 34, 319}},
        {{278, 33, 603, 391, 183, 514}, {135, 138, 72, 367, 387, 0}},
        {{336, 1169, 250, 521, 637, 145}, {141, 123, 43, 341, 462, 110}},
        {{670, 47, 558, 134, 575, 133}, {633, 574, 29, 178, 164, 305}},
        {{392, 154, 281, 326, 50, 84}, {114, 548, 242, 134, 100, 456}},
        {{964, 311, 417, 322, 167, 504}, {190, 271, 37, 684, 11, 279}},
        {{912, 596, 102, 42, 102, 55}, {462, 20, 203, 496, 407, 336}},
        {{226, 287, 598, 971, 404, 84}, {184, 320, 368, 357, 69, 488}},
        {{345, 292, 61, 15, 125, 279}, {535, 338, 396, 402, 202, 256}},
        {{453, 212, 773, 185, 196, 337}, {341, 13, 99, 155, 237, 267}},
        {{509, 203, 307, 182, 53, 265}, {518, 435, 20, 188, 308, 244}},
        {{64, 416, 274, 441, 164, 477}, {885, 20, 11, 209, 285, 80}},
        {{0, 289, 61, 229, 128, 836}, {514, 13, 297, 110, 304, 507}}
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
