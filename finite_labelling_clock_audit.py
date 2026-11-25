"""Execute the nonuniform threshold-tree construction on finite truth tables."""

from itertools import product
from random import Random


def compile_program(n, width, table):
    """One permanent program per fixed labelling, with only fixed successors."""
    word_count = (n + width - 1) // width
    lengths = [min(width, n - i * width) for i in range(word_count)]
    # If possible, save a full word for the final literal lookup.
    order = list(range(1, word_count)) + [0]
    saved = min(lengths[0], width.bit_length() - 1)
    instructions = []

    def emit(*op):
        instructions.append(op)
        return len(instructions) - 1

    def word(position, known):
        address = order[position]
        length = lengths[address]
        last = position == word_count - 1

        def thresholds(high_prefix, unknown):
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


if __name__ == '__main__':
    check()
