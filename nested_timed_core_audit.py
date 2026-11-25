"""Check nested canonical cubes and concrete bounded-run/error certificates."""

from collections import Counter
from itertools import product

import pycosat

from one_byte_dense_successor_audit import clause, encode, parse
from selector_parity_cube_audit import minimum, padding, physical_template


def sat(rows):
    return pycosat.solve(list(rows)) != 'UNSAT'


def variables(rows):
    return max(abs(literal) for row in rows for literal in row)


def anchored_cube(seed, sources, dimension, lengths):
    fixed, selectors, _ = physical_template(*sources, dimension, h=4)
    old = variables(seed)
    offset = 10 * ((old + 3 + 9) // 10)
    gap = {clause(i, i + 1, i + 2) for i in range(old + 1, offset - 1)}

    def translate(row):
        return clause(*(z + offset if z > 0 else z - offset for z in row))

    shared = seed | gap | {translate(row) for row in fixed}
    cubes = []
    for mask in product((0, 1), repeat=dimension):
        cube = shared | {translate((p, q, end[bit]))
                         for (p, q, *end), bit in zip(selectors, mask)}
        cubes.append((mask, cube))
    zero = cubes[0][1]
    size = len(encode(zero))
    v, c = variables(zero), len(zero)
    first = minimum(v, c, 4 * len(str(v+c+10)) + 20) + 2
    return [[(mask, rows | extra) for mask, rows in cubes]
            for extra in (padding(v, c, first + i) for i in range(lengths))], size + first


def verify_block(seed, sources, dimension):
    blocks, base_size = anchored_cube(seed, sources, dimension, 2)
    expected = tuple(sat(src) and sat(seed) for src in sources)
    body = encode(seed).split(b'\n', 1)[1] + b'\n'
    for i, block in enumerate(blocks):
        texts = {mask: encode(rows) for mask, rows in block}
        zero = texts[(0,) * dimension]
        offsets = {}
        for mask, rows in block:
            raw = texts[mask]
            assert len(raw) == base_size + i and parse(raw) == rows
            assert seed < rows and raw.split(b'\n', 1)[1].startswith(body)
            assert max(Counter(abs(z) for row in rows for z in row).values()) <= 4
            assert sat(rows) == expected[sum(mask) % 2]
            if sum(mask) == 1:
                diffs = [(j, x ^ y) for j, (x, y) in enumerate(zip(zero, raw)) if x != y]
                assert len(diffs) == 1 and diffs[0][1] == 1
                offsets[mask.index(1)] = diffs[0][0]
        assert len(set(offsets.values())) == dimension
        for mask, rows in block:
            made = bytearray(zero)
            for j, bit in enumerate(mask):
                made[offsets[j]] ^= bit
            assert bytes(made) == texts[mask]
    return blocks


def width(raw):
    return 16 * (((8 * len(raw) + 1).bit_length() + 15) // 16)


def words(raw, w):
    step = w // 8
    return tuple(int.from_bytes(raw[j:j+step], 'little') for j in range(0, len(raw), step))


def recognizer(raw, verdict):
    # Fixed text: compare width and length, then literal-load and compare each
    # word. Every mismatch jumps to one fixed self-loop. Both terminals are free.
    w = width(raw)
    checks = [('jne', 'width', w), ('jne', 'length', 8*len(raw))]
    for address, value in enumerate(words(raw, w)):
        checks.extend((('load', address), ('jne', 'x', value)))
    return tuple(checks), verdict


def run(program, raw, deadline):
    instructions, answer = program
    w = width(raw)
    memory = words(raw, w)
    mask = (1 << w) - 1
    regs = {'width': w, 'length': 8 * len(raw), 'x': 0}
    for time, op in enumerate(instructions):
        if time >= deadline:
            return None
        if op[0] == 'load':
            addr = op[1] & mask
            regs['x'] = memory[addr] if addr < len(memory) else 0
        elif regs[op[1]] != (op[2] & mask):
            # The next instruction is an unconditional branch to itself. This
            # fixed point cannot reach a terminal for any remaining deadline.
            return None
    return answer if len(instructions) <= deadline else None


def main():
    seed = {clause(1, 2, 3)}
    sat_core = {clause(1, -2, 3)}
    unsat_core = set(product((1, -1), (2, -2), (3, -3)))
    yes, no = encode(seed), encode(unsat_core)
    examples = [(yes, True), (no, False)]
    pool = [((), True), ((), False), recognizer(yes, True), recognizer(no, False)]
    vertices = errors = timeouts = 0
    for j, sources in enumerate(((sat_core, sat_core), (unsat_core, sat_core),
                                 (sat_core, sat_core)), 1):
        block = verify_block(seed, sources, j)
        corners = [(encode(rows), sat(rows)) for length in block for _, rows in length]
        for prog in pool:
            if any(run(prog, raw, j * 8 * len(raw)) == (not verdict)
                   for raw, verdict in examples):
                errors += 1
            else:
                assert all(run(prog, raw, j * 8 * len(raw)) is None for raw, _ in corners)
                timeouts += len(corners)
        for _, new_seed in block[0]:
            if sat(new_seed):
                assert seed < new_seed
                seed = new_seed
                break
        else:
            raise AssertionError('no positive corner')
        chosen = encode(seed)
        next_program = recognizer(chosen, True)
        assert run(next_program, chosen, 8 * len(chosen)) is True
        pool.append(next_program)
        vertices += len(corners)
    # A degree-four unsatisfiable anchor: eight clauses on one triple have
    # degree eight, so first convert them into an actual degree-four core.
    blocks = verify_block({clause(1, 2, 3)}, (unsat_core, unsat_core), 1)
    negative_seed = blocks[0][0][1]
    assert not sat(negative_seed)
    negative = verify_block(negative_seed, (sat_core, unsat_core), 2)
    assert all(not sat(rows) for group in negative for _, rows in group)
    print(f'{vertices} serialized corners in three nested stages; {errors} witnessed wrong halts')
    print(f'{timeouts} certified native timeouts; {sum(map(len, negative))} negative extensions')


if __name__ == '__main__':
    main()
