"""The four standing opponents (O1)-(O4), as programs for
standing_opponent_ram.Machine.  Each `instance(T, seed)` returns (Program, input words) whose
run makes at least T work-memory accesses; the suite truncates the run at
exactly T accesses (the clocked opponent prefix that J simulates).  Every size
parameter is the input LENGTH (public), as with J's unary padding.

(O1) the constant reader of the round-two node game: one store to cell 0, then
     every access loads cell 0.
(O2) the inverse-permutation frontier solver of notes/inverse-snapshot-frontier.md:
     scatter i+1 to address pi(i) (testing the old value is zero), then
     ceil(log2 m) full scans of the inverse array with a register checksum.
(O3) STAND-IN for the hard-table writer of notes/output-linear-hard-tables.md
     (which exists only under H_SAT): writes K table words, word j = the j-th
     (cyclically) of the 24 three-input truth tables of maximal circuit size 4
     over B2 found by an exhaustive circuit search (not included) (8 table bits
     per word), then reads ONE bit at an index taken from the padding.  The
     table is a constant of the program text, so it is NOT hard as a whole
     (it is periodic with period 24): only its access pattern and its 8-bit
     blocks stand in for the real writer.
(O4) a depth-robust labelling evaluator with word labels: vertices 0..V-1 in
     topological order, parents v-1 and p(v), p(v) drawn by a public hash from
     the DRSample distribution (Alwen-Blocki-Harsha 2017, recalled, not
     accessed): g' uniform in [1, bitlen(v)], g = min(v, 2^g'),
     r uniform in [max(g/2, 2), g], p(v) = v - r.  The opcode of the hidden-word
     note is replaced by the add-rotate-xor mix
         label(v) = rol(label(v-1) + label(p(v)), 13) xor (v * K2).
     label(v-1) is kept in a register, label(p(v)) is loaded, label(v) stored.
"""
import random
from standing_opponent_ram import Program

HARD3 = [0x16, 0x17, 0x29, 0x2B, 0x49, 0x4D, 0x61, 0x68, 0x6B, 0x6D, 0x71, 0x79,
         0x86, 0x8E, 0x92, 0x94, 0x97, 0x9E, 0xB2, 0xB6, 0xD4, 0xD6, 0xE8, 0xE9]

O1 = Program([
    ('li', 1, 0), ('ldin', 3, 1),          # v = input[0]
    ('st', 1, 3),                          # access 1: mem[0] := v
    ('inlen', 4),                          # number of loads L = input length
    ('li', 5, 0), ('li', 6, 0),
    'loop:',
    ('bltu', 5, 4, 'body'), ('jmp', 'done'),
    'body:',
    ('ld', 7, 1),                          # load mem[0]
    ('roli', 6, 6, 1), ('xor', 6, 6, 7),   # acc := rol(acc,1) xor value
    ('addi', 5, 5, 1), ('jmp', 'loop'),
    'done:',
    ('andi', 6, 6, 1), ('halt', 6),
])

O2 = Program([
    ('inlen', 1),                          # m
    ('li', 2, 0),
    'scat:',
    ('bltu', 2, 1, 'scat_body'), ('jmp', 'scans'),
    'scat_body:',
    ('ldin', 3, 2),                        # a = pi(i)
    ('ld', 4, 3),                          # old = A[a]
    ('bnz', 4, 'fail'),                    # validation
    ('addi', 5, 2, 1), ('st', 3, 5),       # A[pi(i)] := i+1
    ('addi', 2, 2, 1), ('jmp', 'scat'),
    'scans:',
    ('li', 6, 0), ('li', 7, 1),            # s = ceil(log2 m)
    'lg:',
    ('bltu', 7, 1, 'lg_body'), ('jmp', 'lg_done'),
    'lg_body:',
    ('shli', 7, 7, 1), ('addi', 6, 6, 1), ('jmp', 'lg'),
    'lg_done:',
    ('li', 8, 0), ('li', 9, 0),
    'scan_loop:',
    ('bltu', 8, 6, 'scan_body'), ('jmp', 'finish'),
    'scan_body:',
    ('li', 10, 0),
    'inner:',
    ('bltu', 10, 1, 'inner_body'), ('addi', 8, 8, 1), ('jmp', 'scan_loop'),
    'inner_body:',
    ('ld', 11, 10),                        # A[j]
    ('muli', 9, 9, 3), ('add', 9, 9, 11),  # c := 3c + A[j]
    ('addi', 10, 10, 1), ('jmp', 'inner'),
    'finish:',
    ('andi', 9, 9, 1), ('halt', 9),
    'fail:',
    ('li', 12, 0), ('halt', 12),
])

O3 = Program([
    ('inlen', 1), ('subi', 1, 1, 1),       # K = input length - 1 table words
    ('li', 2, 0), ('li', 3, 0),
    'wl:',
    ('bltu', 2, 1, 'wb'), ('jmp', 'rd'),
    'wb:',
    ('lic', 4, 3, 'HARD3'),                # constant of the program text
    ('st', 2, 4),                          # table word j
    ('addi', 2, 2, 1), ('addi', 3, 3, 1),
    ('li', 5, 24), ('bltu', 3, 5, 'wl'),
    ('li', 3, 0), ('jmp', 'wl'),
    'rd:',
    ('li', 6, 0), ('ldin', 7, 6),          # index from the padding
    ('shri', 8, 7, 3), ('modu', 8, 8, 1),  # word = (idx >> 3) mod K
    ('ld', 9, 8),
    ('andi', 10, 7, 7), ('shr', 9, 9, 10), ('andi', 9, 9, 1),
    ('halt', 9),
], consts={'HARD3': HARD3})

# (O3u): (O3) with the single padding-indexed read replaced by reads of every
# table word: the union over all extensions (all padding indices) of (O3)'s
# one read, which is what a game that must be right on every extension of the
# opponent prefix faces at a cut.
O3U = Program([
    ('inlen', 1), ('subi', 1, 1, 1),
    ('li', 2, 0), ('li', 3, 0),
    'wl:',
    ('bltu', 2, 1, 'wb'), ('jmp', 'rd'),
    'wb:',
    ('lic', 4, 3, 'HARD3'), ('st', 2, 4),
    ('addi', 2, 2, 1), ('addi', 3, 3, 1),
    ('li', 5, 24), ('bltu', 3, 5, 'wl'),
    ('li', 3, 0), ('jmp', 'wl'),
    'rd:',
    ('li', 6, 0), ('li', 7, 0),
    'rl:',
    ('bltu', 6, 1, 'rb'), ('jmp', 'rdone'),
    'rb:',
    ('ld', 9, 6), ('xor', 7, 7, 9), ('addi', 6, 6, 1), ('jmp', 'rl'),
    'rdone:',
    ('andi', 7, 7, 1), ('halt', 7),
], consts={'HARD3': HARD3})

K1 = 0x9E3779B97F4A7C15
K2 = 0xC2B2AE3D27D4EB4F
O4 = Program([
    ('inlen', 1),                          # V vertices
    ('li', 2, 0), ('ldin', 3, 2),          # label(0) = seed
    ('st', 2, 3),
    ('li', 4, 1),                          # v
    ('li', 5, 1), ('li', 6, 2),            # L = bitlen(v), pw = 2^L
    'vl:',
    ('bltu', 4, 1, 'vb'), ('jmp', 'vdone'),
    'vb:',
    ('bltu', 4, 6, 'nolg'),
    ('addi', 5, 5, 1), ('shli', 6, 6, 1),
    'nolg:',
    ('muli', 7, 4, K1), ('shri', 8, 7, 29), ('xor', 7, 7, 8),   # h = mix(v), public
    ('modu', 8, 7, 5), ('addi', 8, 8, 1),                       # g' in [1, L]
    ('li', 9, 1), ('shl', 9, 9, 8),                             # 2^g'
    ('bltu', 9, 4, 'gok'), ('mov', 9, 4),                       # g = min(v, 2^g')
    'gok:',
    ('shri', 10, 9, 1), ('li', 11, 2),
    ('bltu', 11, 10, 'lok'), ('mov', 10, 11),                   # lo = max(g/2, 2)
    'lok:',
    ('bltu', 9, 10, 'small'),                                   # g < lo only for v = 1
    ('sub', 11, 9, 10), ('addi', 11, 11, 1),                    # g - lo + 1
    ('shri', 12, 7, 7), ('modu', 12, 12, 11), ('add', 12, 12, 10),  # r
    ('sub', 13, 4, 12), ('jmp', 'pdone'),                       # p = v - r
    'small:',
    ('subi', 13, 4, 1),
    'pdone:',
    ('ld', 14, 13),                                             # label(p(v))
    ('add', 15, 3, 14), ('roli', 15, 15, 13),
    ('muli', 12, 4, K2), ('xor', 15, 15, 12),                   # ARX mix
    ('st', 4, 15),                                              # label(v)
    ('mov', 3, 15),
    ('addi', 4, 4, 1), ('jmp', 'vl'),
    'vdone:',
    ('andi', 3, 3, 1), ('halt', 3),
])


# EXTRA (not one of the four standing opponents): the "overwrite ladder" of
# the truth-claim games, 8 cells: each rung loads the cell chosen by the
# current register (which depends on the previous loaded word), mixes, and
# overwrites the same cell.
L8 = Program([
    ('inlen', 1),
    ('li', 2, 0), ('ldin', 3, 2),
    ('li', 4, 0),
    'll:',
    ('bltu', 4, 1, 'lb'), ('jmp', 'ldone'),
    'lb:',
    ('andi', 5, 3, 7),
    ('ld', 6, 5),
    ('add', 3, 3, 6), ('roli', 3, 3, 7), ('xori', 3, 3, 0x5BD1),
    ('st', 5, 3),
    ('addi', 4, 4, 1), ('jmp', 'll'),
    'ldone:',
    ('andi', 3, 3, 1), ('halt', 3),
])


def o2_full(m):
    return 2 * m + m * max(0, (m - 1).bit_length())


def instance(name, T, seed=20261127):
    rng = random.Random(f"{seed}-{name}-{T}")   # str seed: deterministic across processes
    if name == 'O1':
        return O1, [rng.randrange(1, 1 << 16)] + [0] * max(0, T - 2)
    if name == 'O2':
        m = 2
        while o2_full(m) < T:
            m += 1
        pi = list(range(m))
        rng.shuffle(pi)
        return O2, pi
    if name == 'O3':
        K = max(1, T - 1)
        return O3, [rng.randrange(8 * K)] + [0] * K
    if name == 'O3u':
        K = (T + 1) // 2
        return O3U, [0] * (K + 1)
    if name == 'L8':
        return L8, [rng.randrange(1, 1 << 16)] + [0] * ((T + 1) // 2 - 1)
    if name == 'O4':
        V = (T + 2) // 2
        return O4, [rng.randrange(1, 1 << 16)] + [0] * (V - 1)
    raise ValueError(name)


NAMES = ('O1', 'O2', 'O3', 'O3u', 'O4', 'L8')   # L8 is an extra (the overwrite ladder)
