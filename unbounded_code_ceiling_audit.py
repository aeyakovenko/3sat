"""Audit of the unbounded-code ceiling: every predicate on W words of w bits has a
program with at most W*(w+1) executed instructions, and most predicates need almost N=W*w.

The interpreter below implements only what the construction uses from the native RAM of
exact-clocks-for-two-word-sat-inputs.md: a LOAD with a literal address into a fresh
register, and an unsigned less-than branch of a register against a literal. Terminal
verdicts are free. Each executed LOAD or branch costs one step.
"""

from itertools import product
from random import Random

import numpy as np


def binary_search_program(table, prune):
    """Build the bit-scan program for a truth table of shape (2^w,)*W, word 0 first.

    A node is ('leaf', verdict), ('load', address, child) or
    ('blt', address, literal, child_if_less, child_otherwise). Register i holds input word i.
    With prune=True a subtree on which the predicate is constant becomes a leaf.
    """
    words = table.ndim
    size = table.shape[0]

    def constant(block):
        first = bool(block.flat[0])
        return first if (block.all() if first else not block.any()) else None

    def search(block, position, lo, hi):
        # `block` is the table with words before `position` fixed and word `position`
        # restricted to lo..hi (axis 0).
        if prune:
            value = constant(block)
            if value is not None:
                return ('leaf', value)
        if lo == hi:
            return next_word(block[0], position + 1)
        middle = (lo + hi + 1) // 2
        return ('blt', position, middle,
                search(block[:middle - lo], position, lo, middle - 1),
                search(block[middle - lo:], position, middle, hi))

    def next_word(block, position):
        if position == words:
            return ('leaf', bool(block))
        if prune:
            value = constant(block)
            if value is not None:
                return ('leaf', value)
        return ('load', position, search(block, position, 0, size - 1))

    return next_word(table, 0)


def run(program, memory):
    """Execute the tree on the given input words; return (verdict, executed steps)."""
    registers = {}
    node, steps = program, 0
    while node[0] != 'leaf':
        steps += 1
        if node[0] == 'load':
            _, address, node = node
            registers[address] = memory[address]
        else:
            _, register, literal, less, otherwise = node
            node = less if registers[register] < literal else otherwise
    return node[1], steps


def check(table, prune):
    words, size = table.ndim, table.shape[0]
    width = size.bit_length() - 1
    program = binary_search_program(table, prune)
    worst, histogram = 0, {}
    for memory in product(range(size), repeat=words):
        verdict, steps = run(program, memory)
        assert verdict == bool(table[memory]), memory
        worst = max(worst, steps)
        histogram[steps] = histogram.get(steps, 0) + 1
    assert worst <= words * (width + 1)
    return worst, dict(sorted(histogram.items()))


def sign_plane(p, q, m, n):
    # Catalog of exact-nine-step-clock-for-four-sat-words.md: words P, Q, M, N.
    return not ((p & m) or (q & n) or (m == n == 15))


def cube_cycle_satisfiable(*memory):
    # Catalog of shuffled-four-cube-cycle-banks-in-ordinary-sat.md: word i holds mask bits
    # 4i..4i+3; the bank is satisfiable exactly when two cyclically adjacent bits are both 0.
    mask = sum(value << (4 * position) for position, value in enumerate(memory))
    rotated = ((mask << 1) & 0xffff) | (mask >> 15)
    return (mask | rotated) != 0xffff


def tabulate(predicate, words, width):
    table = np.zeros((2 ** width,) * words, dtype=bool)
    for memory in product(range(2 ** width), repeat=words):
        table[memory] = predicate(*memory)
    return table


def instruction_choices(steps, width):
    # Generous count of the distinct instructions available at one tree position of a
    # program with at most `steps` executed instructions per path, in static single
    # assignment form: an operand is one of at most `steps` earlier results or one of the
    # 2^width literals. LOAD has one operand; STORE, the 20 ALU operations and the 3
    # comparison branches have two.
    operands = steps + 2 ** width
    return operands + 24 * operands ** 2


def majority_floor(words, width):
    """Largest T such that programs of depth <= T compute fewer than half of all predicates.

    A program with at most T executed instructions per path is a labelling of the
    2^(T+1)-1 positions of the complete binary tree of depth T by an instruction, ACCEPT,
    REJECT or 'unused'. It computes at most one predicate, so the number of predicates with
    clock <= T is at most (choices+3)^(2^(T+1)-1) <= 2^((2^(T+1)-1)*bit_length(choices+3)).
    This is below 2^(2^N-1), half of all predicates, when the exponents compare that way.
    """
    bits = words * width
    best = -1
    for steps in range(words * (width + 1) + 1):
        positions = 2 ** (steps + 1) - 1
        log_upper = (instruction_choices(steps, width) + 3).bit_length()
        if positions * log_upper < 2 ** bits - 1:
            best = steps
    return best


if __name__ == '__main__':
    # 1. Every one of the 65,536 predicates of one four-bit word.
    worst_overall = 0
    for code in range(2 ** 16):
        table = np.array([code >> value & 1 for value in range(16)], dtype=bool)
        worst_overall = max(worst_overall, check(table, prune=False)[0])
    print(f'One 4-bit word: all 65536 predicates decided; worst clock {worst_overall} = 1*(4+1)')

    # 2. Random predicates of two four-bit words.
    rng = Random(20261127)
    worst_overall = 0
    for _ in range(2000):
        code = rng.getrandbits(256)
        table = np.array([code >> index & 1 for index in range(256)], dtype=bool).reshape(16, 16)
        worst_overall = max(worst_overall, check(table, prune=False)[0])
    print(f'Two 4-bit words: 2000 random predicates decided; worst clock {worst_overall} <= 2*(4+1)')

    # 3. The two 16-bit SAT catalogs, with and without pruning of constant subtrees.
    for name, predicate in (('sign-plane', sign_plane), ('cube-cycle', cube_cycle_satisfiable)):
        table = tabulate(predicate, 4, 4)
        plain, _ = check(table, prune=False)
        pruned, histogram = check(table, prune=True)
        print(f'{name} catalog, all 65536 files: plain bit scan {plain} = 4*(4+1); '
              f'pruned bit scan worst case {pruned}, histogram {histogram}')

    # 4. Counting floor: more than half of all predicates have clock above T.
    print('Majority floor T (more than half of all predicates on N bits need more than T steps):')
    for width, words in ((4, 1), (4, 2), (4, 4), (5, 4), (4, 8), (8, 8), (16, 16), (16, 64)):
        bits = words * width
        floor = majority_floor(words, width)
        print(f'  w={width:2d} W={words:3d} N={bits:5d}: T={floor:5d}, N-T={bits - floor:2d}, '
              f'ceiling W(w+1)={words * (width + 1)}')
