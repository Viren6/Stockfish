#!/usr/bin/env python3
"""Shrink Full_Threats rows in a Stockfish big net from 60144 to 53564."""

from __future__ import annotations

import argparse
import struct
from pathlib import Path

VERSION = 0x7AF32F20
OLD_THREAT_DIM = 60144
NEW_THREAT_DIM = 53564
HALF_DIM = 1024
PSQ_DIM = 64 * (11 * 64) // 2
PSQT_BUCKETS = 8
OLD_FEATURE_HASH = 0x8F234CB8
NEW_FEATURE_HASH = 0x8F234CB9
OLD_TRANSFORMER_HASH = OLD_FEATURE_HASH ^ (HALF_DIM * 2)
NEW_TRANSFORMER_HASH = NEW_FEATURE_HASH ^ (HALF_DIM * 2)

WHITE, BLACK = 0, 1
PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING = 1, 2, 3, 4, 5, 6
ALL_PIECES = [1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 13, 14]
OLD_NUM_VALID = [0, 6, 10, 8, 8, 10, 0, 0, 0, 6, 10, 8, 8, 10, 0, 0]
NEW_NUM_VALID = [0, 5, 9, 7, 7, 9, 0, 0, 0, 6, 9, 7, 7, 9, 0, 0]
MAP = [
    [0, 1, -1, 2, -1, -1],
    [0, 1, 2, 3, 4, -1],
    [0, 1, 2, 3, -1, -1],
    [0, 1, 2, 3, -1, -1],
    [0, 1, 2, 3, 4, -1],
    [-1, -1, -1, -1, -1, -1],
]


class Reader:
    def __init__(self, data: bytes):
        self.data = data
        self.pos = 0

    def u32(self) -> int:
        v = struct.unpack_from('<I', self.data, self.pos)[0]
        self.pos += 4
        return v

    def take(self, n: int) -> bytes:
        out = self.data[self.pos : self.pos + n]
        self.pos += n
        return out


def color_of(piece: int) -> int:
    return BLACK if piece >= 8 else WHITE


def type_of(piece: int) -> int:
    return piece & 7


def make_piece(color: int, pt: int) -> int:
    return pt + (8 if color == BLACK else 0)


def attacks(pt: int, frm: int, color: int | None = None) -> int:
    f, r = frm % 8, frm // 8
    bb = 0

    def add(nf: int, nr: int):
        nonlocal bb
        if 0 <= nf < 8 and 0 <= nr < 8:
            bb |= 1 << (nr * 8 + nf)

    if pt == PAWN:
        dr = 1 if color == WHITE else -1
        add(f - 1, r + dr)
        add(f + 1, r + dr)
    elif pt == KNIGHT:
        for df, dr in [(-2, -1), (-2, 1), (-1, -2), (-1, 2), (1, -2), (1, 2), (2, -1), (2, 1)]:
            add(f + df, r + dr)
    elif pt == KING:
        for df in (-1, 0, 1):
            for dr in (-1, 0, 1):
                if df or dr:
                    add(f + df, r + dr)
    else:
        dirs = []
        if pt in (BISHOP, QUEEN):
            dirs += [(-1, -1), (-1, 1), (1, -1), (1, 1)]
        if pt in (ROOK, QUEEN):
            dirs += [(-1, 0), (1, 0), (0, -1), (0, 1)]
        for df, dr in dirs:
            nf, nr = f + df, r + dr
            while 0 <= nf < 8 and 0 <= nr < 8:
                add(nf, nr)
                nf += df
                nr += dr
    return bb


def popcount(x: int) -> int:
    return x.bit_count()


def init_offsets(num_valid: list[int]):
    helper = [[0, 0] for _ in range(16)]
    offsets = [[0] * 64 for _ in range(16)]
    cum = 0
    for piece in ALL_PIECES:
        piece_cum = 0
        for frm in range(64):
            offsets[piece][frm] = piece_cum
            if type_of(piece) != PAWN:
                piece_cum += popcount(attacks(type_of(piece), frm))
            elif 8 <= frm <= 55:
                piece_cum += popcount(attacks(PAWN, frm, color_of(piece)))
        helper[piece] = [piece_cum, cum]
        cum += num_valid[piece] * piece_cum
    return helper, offsets


def index_lut2():
    out = [[[0] * 64 for _ in range(64)] for _ in range(16)]
    for piece in ALL_PIECES:
        pt = type_of(piece)
        for frm in range(64):
            atk = attacks(pt, frm, color_of(piece) if pt == PAWN else None)
            for to in range(64):
                out[piece][frm][to] = popcount(((1 << to) - 1) & atk)
    return out


def old_lut1(helper):
    idx = [[[OLD_THREAT_DIM] * 2 for _ in range(16)] for _ in range(16)]
    for attacker in ALL_PIECES:
        for attacked in ALL_PIECES:
            enemy = (attacker ^ attacked) == 8
            at, dt = type_of(attacker), type_of(attacked)
            m = MAP[at - 1][dt - 1]
            semi = at == dt and (enemy or at != PAWN)
            exc = m < 0
            base = helper[attacker][1] + (color_of(attacked) * (OLD_NUM_VALID[attacker] // 2) + m) * helper[attacker][0]
            idx[attacker][attacked][0] = OLD_THREAT_DIM if exc else base
            idx[attacker][attacked][1] = OLD_THREAT_DIM if (exc or semi) else base
    return idx


def new_lut1(helper):
    idx = [[[NEW_THREAT_DIM] * 2 for _ in range(16)] for _ in range(16)]
    for attacker in ALL_PIECES:
        buckets = [-1] * 16
        next_bucket = 0
        for attacked in ALL_PIECES:
            at, dt = type_of(attacker), type_of(attacked)
            m = MAP[at - 1][dt - 1]
            exc = m < 0 or (attacker == 1 and attacked == 9)
            if exc:
                continue
            canonical = attacked
            if at == dt and at != PAWN:
                canonical = make_piece(color_of(attacker), at)
            if buckets[canonical] < 0:
                buckets[canonical] = next_bucket
                next_bucket += 1
            base = helper[attacker][1] + buckets[canonical] * helper[attacker][0]
            idx[attacker][attacked][0] = base
            idx[attacker][attacked][1] = NEW_THREAT_DIM if (at == dt and at != PAWN) else base
        if next_bucket != NEW_NUM_VALID[attacker]:
            raise ValueError(f"bucket count mismatch for piece {attacker}: {next_bucket}")
    return idx


def make_index(lut1, offsets, lut2, dim, attacker, frm, to, attacked, is_new):
    d = frm < to
    frm2, to2 = frm, to
    if is_new and ((attacker ^ attacked) == 8) and ((attacker | attacked) > 9):
        frm2, to2 = to2, frm2
    idx = lut1[attacker][attacked][1 if d else 0]
    if idx >= dim:
        return dim
    return idx + offsets[attacker][frm2] + lut2[attacker][frm2][to2]


def build_mapping():
    old_helper, old_offsets = init_offsets(OLD_NUM_VALID)
    new_helper, new_offsets = init_offsets(NEW_NUM_VALID)
    if sum(NEW_NUM_VALID[p] * new_helper[p][0] for p in ALL_PIECES) != NEW_THREAT_DIM:
        raise ValueError('new dimensions do not add up to 53564')

    lut2 = index_lut2()
    o1 = old_lut1(old_helper)
    n1 = new_lut1(new_helper)

    mapped = [set() for _ in range(NEW_THREAT_DIM)]
    for attacker in ALL_PIECES:
        for frm in range(64):
            atk = attacks(type_of(attacker), frm, color_of(attacker) if type_of(attacker) == PAWN else None)
            for to in range(64):
                if not ((atk >> to) & 1):
                    continue
                for attacked in ALL_PIECES:
                    oi = make_index(o1, old_offsets, lut2, OLD_THREAT_DIM, attacker, frm, to, attacked, False)
                    ni = make_index(n1, new_offsets, lut2, NEW_THREAT_DIM, attacker, frm, to, attacked, True)
                    if ni < NEW_THREAT_DIM:
                        if oi >= OLD_THREAT_DIM:
                            raise ValueError('new index produced from excluded old index')
                        mapped[ni].add(oi)
    missing = [i for i, s in enumerate(mapped) if not s]
    if missing:
        raise ValueError(f'missing mappings for {len(missing)} indices')
    return [sorted(s) for s in mapped]


def read_sleb_section(r: Reader, count: int):
    magic = r.take(17)
    if magic != b'COMPRESSED_LEB128':
        raise ValueError('missing COMPRESSED_LEB128 marker')
    nbytes = r.u32()
    payload = r.take(nbytes)
    vals = []
    i = 0
    while len(vals) < count:
        shift = 0
        result = 0
        while True:
            b = payload[i]
            i += 1
            result |= (b & 0x7F) << shift
            shift += 7
            if (b & 0x80) == 0:
                if shift < 32 and (b & 0x40):
                    result |= - (1 << shift)
                vals.append(result)
                break
    if i != len(payload):
        raise ValueError('unused leb bytes')
    return vals


def write_sleb_section(values: list[int]) -> bytes:
    out = bytearray(b'COMPRESSED_LEB128')
    payload = bytearray()
    for v in values:
        x = int(v)
        while True:
            b = x & 0x7F
            x >>= 7
            done = (x == 0 and (b & 0x40) == 0) or (x == -1 and (b & 0x40) != 0)
            if done:
                payload.append(b)
                break
            payload.append(b | 0x80)
    out += struct.pack('<I', len(payload))
    out += payload
    return bytes(out)


def convert(inp: Path, out: Path):
    mapping = build_mapping()
    data = inp.read_bytes()
    r = Reader(data)

    version, net_hash, desc_size = r.u32(), r.u32(), r.u32()
    if version != VERSION:
        raise ValueError('unexpected net version')
    desc = r.take(desc_size)

    tr_hash = r.u32()
    if tr_hash != OLD_TRANSFORMER_HASH:
        raise ValueError(f'unexpected transformer hash {tr_hash:#x}')

    biases = read_sleb_section(r, HALF_DIM)
    threat_weights = list(struct.unpack(f'<{OLD_THREAT_DIM * HALF_DIM}b', r.take(OLD_THREAT_DIM * HALF_DIM)))
    dense_weights = read_sleb_section(r, PSQ_DIM * HALF_DIM)
    threat_psqt = read_sleb_section(r, (OLD_THREAT_DIM + PSQ_DIM) * PSQT_BUCKETS)
    tail = data[r.pos :]

    new_tw = [0] * (NEW_THREAT_DIM * HALF_DIM)
    new_tp = [0] * (NEW_THREAT_DIM * PSQT_BUCKETS)

    for ni, old_ids in enumerate(mapping):
        ref = old_ids[0]
        rb = ref * HALF_DIM
        nb = ni * HALF_DIM
        new_tw[nb : nb + HALF_DIM] = threat_weights[rb : rb + HALF_DIM]

        rp = ref * PSQT_BUCKETS
        np = ni * PSQT_BUCKETS
        new_tp[np : np + PSQT_BUCKETS] = threat_psqt[rp : rp + PSQT_BUCKETS]

        for oi in old_ids[1:]:
            ob = oi * HALF_DIM
            if threat_weights[ob : ob + HALF_DIM] != new_tw[nb : nb + HALF_DIM]:
                raise ValueError(f'threat row mismatch when merging old indices {ref} and {oi}')
            op = oi * PSQT_BUCKETS
            if threat_psqt[op : op + PSQT_BUCKETS] != new_tp[np : np + PSQT_BUCKETS]:
                raise ValueError(f'psqt row mismatch when merging old indices {ref} and {oi}')

    new_combined_psqt = new_tp + threat_psqt[OLD_THREAT_DIM * PSQT_BUCKETS :]

    out_bytes = bytearray()
    out_bytes += struct.pack('<III', VERSION, net_hash ^ 0x1, desc_size)
    out_bytes += desc
    out_bytes += struct.pack('<I', NEW_TRANSFORMER_HASH)
    out_bytes += write_sleb_section(biases)
    out_bytes += struct.pack(f'<{len(new_tw)}b', *new_tw)
    out_bytes += write_sleb_section(dense_weights)
    out_bytes += write_sleb_section(new_combined_psqt)
    out_bytes += tail

    out.write_bytes(out_bytes)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input_net', type=Path)
    ap.add_argument('output_net', type=Path)
    args = ap.parse_args()
    convert(args.input_net, args.output_net)


if __name__ == '__main__':
    main()
