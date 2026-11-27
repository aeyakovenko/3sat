"""Write proper 3-CNFs and check the exact multiplicity of the subset-column construction."""

from argparse import ArgumentParser
from itertools import combinations, product
from math import comb
from subprocess import run


def forbidden(bits, variables):
    return tuple(-v if bit else v for v, bit in zip(variables, bits))


def compile_file(variable_count, source, mode_count):
    next_id = variable_count + 1
    pads = tuple(range(next_id, next_id + 3))
    next_id += 3
    rows = list(source)
    rows.extend(forbidden(bits, pads) for bits in product((0, 1), repeat=3) if any(bits))
    rows.extend((i, -pads[0], pads[1]) for i in range(1, variable_count + 1))
    modes = list(range(next_id, next_id + mode_count - 1))
    next_id += len(modes)
    rows.extend((-u, -v, pads[0]) for u, v in combinations(modes, 2))
    reference = 1 if variable_count else pads[0]

    signals = {}
    outputs = {}
    for mask in range(1, 1 << len(modes)):
        j = mask.bit_length() - 1
        rest = mask ^ (1 << j)
        if rest:
            u, v, z = signals[rest], modes[j], next_id
            next_id += 1
            rows.extend([(-u, z, pads[0]), (-v, z, pads[0]), (u, v, -z)])
            signals[mask] = z
        else:
            signals[mask] = modes[j]
        out = next_id
        next_id += 1
        outputs[mask] = out
        rows.extend(forbidden((a, b, 1 ^ a ^ b), (signals[mask], reference, out))
                    for a, b in product((0, 1), repeat=2))
    return next_id - 1, rows, pads, modes, signals, outputs


def rows_hold(rows, assignment):
    return all(any(bool(assignment[abs(lit)]) == (lit > 0) for lit in row) for row in rows)


def as_dimacs(variables, rows):
    lines = [f'p cnf {variables} {len(rows)}', *(' '.join(map(str, row)) + ' 0' for row in rows)]
    return ('\n'.join(lines) + '\n').encode('ascii')


def parse_proper(data):
    head, *lines = data.decode('ascii').splitlines()
    p, cnf, count, total = head.split()
    assert (p, cnf, len(lines)) == ('p', 'cnf', int(total))
    rows = []
    for line in lines:
        a, b, c, stop = map(int, line.split())
        assert stop == 0 and all(0 < abs(x) <= int(count) for x in (a, b, c))
        assert len({abs(a), abs(b), abs(c)}) == 3
        rows.append((a, b, c))
    return int(count), rows


def check_connected(count, rows):
    neighbors = [set() for _ in range(count + 1)]
    for row in rows:
        for u, v in combinations(map(abs, row), 2):
            neighbors[u].add(v)
            neighbors[v].add(u)
    seen = {1}
    queue = [1]
    while queue:
        for v in neighbors[queue.pop()] - seen:
            seen.add(v)
            queue.append(v)
    assert len(seen) == count


def audit_file(variable_count, source, mode_count, solver):
    count, rows, pads, modes, signals, outputs = compile_file(variable_count, source, mode_count)
    raw = as_dimacs(count, rows)
    count, rows = parse_proper(raw)
    check_connected(count, rows)
    blocked = []
    source_models = 0
    for x in product((0, 1), repeat=variable_count):
        if not rows_hold(source, (0, *x)):
            continue
        source_models += 1
        projected = set()
        for mode in range(mode_count):
            v = [None] * (count + 1)
            v[1:1 + variable_count] = x
            for pad in pads:
                v[pad] = 0
            for j, var in enumerate(modes):
                v[var] = int(j == mode)
            for mask, var in signals.items():
                v[var] = (mask >> mode) & 1
                v[outputs[mask]] = v[var] ^ (x[0] if x else 0)
            assert all(bit is not None for bit in v[1:]) and rows_hold(rows, v)
            projected.add(tuple(v[out] for out in outputs.values()))
            blocked.append(forbidden(v[1:], range(1, count + 1)))
        assert len(projected) == mode_count
        distances = {sum(j != k for j, k in zip(a, b)) for a, b in combinations(projected, 2)}
        assert distances == {1 << (mode_count - 2)}
    if solver:
        result = run([solver], input=as_dimacs(count, rows + blocked), capture_output=True, check=False)
        assert result.returncode == 20, 'An assignment remains after blocking all predicted full models.'
    return source_models, len(blocked), len(raw), count


def cuts(s, size):
    # Partition the s mode labels according to agreement on all selected columns.
    # For a fixed partition into p parts, counting column sets injective on those parts
    # subtracts those constant on a coarser partition.
    partitions = {(0, 0): 1}
    for n in range(1, s + 1):
        for p in range(1, n + 1):
            partitions[n, p] = partitions.get((n - 1, p - 1), 0) + p * partitions.get((n - 1, p), 0)
    separating = {}
    for p in range(1, s + 1):
        count = comb((1 << (p - 1)) - 1, size)
        separating[p] = count - sum(partitions[p, r] * separating[r] for r in range(1, p))
    return {r: partitions[s, r] * separating[r] for r in range(1, s + 1) if separating[r]}


def main(solver):
    unique = [forbidden(x, (1, 2, 3)) for x in product((0, 1), repeat=3) if any(x)]
    unsatisfiable = [*unique, (1, 2, 3)]
    examples = [(0, [], 1), (3, unique, 1), (3, [(1, 2, 3)], 7), (3, unsatisfiable, 0),
                (6, [(1, 2, 3), (4, 5, 6)], 49)]
    for modes in (3, 6, 7):
        total_models = 0
        for variables, source, expected in examples:
            before, after, _, _ = audit_file(variables, source, modes, solver)
            assert before == expected and after == before * modes
            total_models += after
        print(f'{modes} modes: {len(examples)} proper files, {total_models} full assignments verified')
    assert cuts(6, 2) == {3: 270, 4: 195}
    assert cuts(6, 8) == {5: 96525, 6: 7792200}
    print('Six-mode cut counts:', cuts(6, 2), cuts(6, 8))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--solver', help='check completeness with a DIMACS solver on standard input (UNSAT exit 20)')
    main(parser.parse_args().solver)
