"""Execute the nonuniform threshold-tree construction on finite truth tables."""

from itertools import product
from random import Random


def compile_program(n, width, table, *, share_suffixes=False):
    """One permanent program per fixed labelling, with only fixed successors."""
    word_count = (n + width - 1) // width
    lengths = [min(width, n - i * width) for i in range(word_count)]
    # If possible, save a full word for the final literal lookup.
    order = list(range(1, word_count)) + [0]
    saved = min(lengths[0], width.bit_length() - 1)
    cut = max(saved, min(lengths[0], n.bit_length() - 2))
    suffix_programs = {}
    instructions = []

    def emit(*op):
        instructions.append(op)
        return len(instructions) - 1

    def word(position, known):
        address = order[position]
        length = lengths[address]
        last = position == word_count - 1

        def thresholds(high_prefix, unknown):
            if last and unknown == cut and share_suffixes:
                start = known | (high_prefix << (width * address))
                # Address zero is the last word. Its remaining completions
                # are consecutive input integers in the truth table.
                assert address == 0
                key = (high_prefix, tuple(table[start:start + (1 << cut)]))
                if key not in suffix_programs:
                    suffix_programs[key] = build_thresholds(high_prefix, unknown)
                return suffix_programs[key]
            return build_thresholds(high_prefix, unknown)

        def build_thresholds(high_prefix, unknown):
            if unknown == 0 and not last:
                return word(position + 1, known | (high_prefix << (width * address)))
            if last and unknown == saved:
                literal = sum(table[known | ((high_prefix + j) << (width * address))] << j
                              for j in range(1 << saved))
                verdict = emit('test')
                low_bit = emit('and', 1, verdict)
                select = emit('shift', literal, low_bit)
                return emit('and', (1 << saved) - 1, select)
            half = 1 << (unknown - 1)
            left = thresholds(high_prefix, unknown - 1)
            right = thresholds(high_prefix + half, unknown - 1)
            return emit('le', high_prefix + half - 1, left, right)

        return emit('load', address, thresholds(0, length))

    return word(0, 0), instructions, n + word_count - saved + 4


def run(program, root, address_words):
    pc, register, cost = root, 0, 0
    while True:
        cost += 1
        op, *args = program[pc]
        if op == 'load':
            address, pc = args
            register = address_words[address]
        elif op == 'le':
            threshold, left, right = args
            pc = left if register <= threshold else right
        elif op == 'and':
            value, pc = args
            register &= value
        elif op == 'shift':
            value, pc = args
            register = value >> register
        else:
            assert op == 'test'
            return register != 0, cost


def check():
    rng, programs, executions = Random(71), 0, 0
    for n in range(1, 10):
        for width in (2, 3, 4, 5, 8):
            if (n + width - 1) // width > 1 << width:
                continue
            tables = (product((0, 1), repeat=1 << n) if n <= 3 else
                      [[rng.randrange(2) for _ in range(1 << n)] for _ in range(3)])
            for table in tables:
                root, program, deadline = compile_program(n, width, table)
                programs += 1
                for x, expected in enumerate(table):
                    words = [(x >> offset) & ((1 << width) - 1) for offset in range(0, n, width)]
                    answer, cost = run(program, root, words)
                    assert answer == bool(expected) and cost == deadline
                    executions += 1
    print(f'{programs} fixed programs, {executions} exact executions including partial tail words')


def check_shared_suffixes():
    rng = Random(193)
    checked = runs = 0
    for n, width in ((3, 2), (6, 3), (8, 5), (10, 4), (12, 6), (16, 8)):
        tables = [[rng.randrange(2) for _ in range(1 << n)],
                  [x.bit_count() % 2 for x in range(1 << n)]]
        for table in tables:
            root, shared, deadline = compile_program(n, width, table, share_suffixes=True)
            _, unshared, previous_deadline = compile_program(n, width, table)
            assert len(shared) <= len(unshared) and deadline == previous_deadline
            if n >= 6 and table is tables[1]:
                assert len(shared) < len(unshared)
            for x, expected in enumerate(table):
                words = [(x >> offset) & ((1 << width) - 1) for offset in range(0, n, width)]
                answer, steps = run(shared, root, words)
                assert answer == bool(expected) and steps == deadline
                runs += 1
            checked += 1
    print(f'{checked} shared programs, {runs} exact executions, identical clocks')


if __name__ == '__main__':
    check()
    check_shared_suffixes()
