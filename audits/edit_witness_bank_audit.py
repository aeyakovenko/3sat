"""Enumerate small witness covers and audit single-bit cardinality edits in ordinary DIMACS."""

import argparse
from itertools import combinations

from sheet_guard_deletions_audit import serialize_dimacs, solve_dimacs


def triple_masks(n):
    return [sum(1 << j for j in edge) for edge in combinations(range(n), 3)]


def colorings(n, triples):
    all_vertices = (1 << n) - 1
    return [
        mask for mask in range(1 << n)
        if all((mask & edge) != edge and ((all_vertices ^ mask) & edge) != edge for edge in triples)
    ]


def linear_census(n):
    triples = triple_masks(n)
    universe = (1 << n) - 1
    all_partitions = (1 << (1 << n)) - 1
    permitted = [sum(1 << mask for mask in range(1 << n)
                     if edge & mask != edge and edge & (universe ^ mask) != edge) for edge in triples]
    after = [sum(1 << j for j in range(i + 1, len(triples))
                 if (edge & triples[j]).bit_count() <= 1) for i, edge in enumerate(triples)]
    total, unsat_sizes = 0, {}

    def visit(remaining, viable, size):
        nonlocal total
        total += 1
        if not viable:
            unsat_sizes[size] = unsat_sizes.get(size, 0) + 1
        while remaining:
            bit = remaining & -remaining
            i = bit.bit_length() - 1
            remaining ^= bit
            visit(remaining & after[i], viable & permitted[i], size + 1)

    visit((1 << len(triples)) - 1, all_partitions, 0)
    return total, unsat_sizes


def false_calibrators():
    return [tuple(-j if row >> (j - 1) & 1 else j for j in (1, 2, 3)) for row in range(1, 8)]


def pin(i, active):
    # Positive names ending in '3' and '2' differ in one literal ASCII bit.
    return 10 * (i + 1) + (2 if active else 3)


def registers(k, i, j):
    return 10 * ((k + 2) * (i + 1) + j) + 4


def counter_file(b, k, edits):
    rows = false_calibrators() + [(-registers(k, 0, k + 1), 1, 2)]
    for i in range(b):
        x, truth = pin(i, True), pin(i, False)
        rows.extend([(truth, 1, 2), (pin(i, bool(edits >> i & 1)), 1, 2)])
        for j in range(1, k + 2):
            rows.append((-registers(k, i, j), registers(k, i + 1, j), 1))
        rows.append((-x, registers(k, i + 1, 1), 1))
        for j in range(1, k + 1):
            rows.append((-x, -registers(k, i, j), registers(k, i + 1, j + 1)))
        rows.append((-registers(k, i + 1, k + 1), 1, 2))
    return rows


def hypergraph_file(n, triples, marked):
    rows = false_calibrators()
    for edge in triples:
        rows.append(tuple(-pin(i, True) for i in range(n) if edge >> i & 1))
    for i in range(n):
        rows.extend([(pin(i, False), 1, 2), (pin(i, bool(marked >> i & 1)), 1, 2)])
    return rows


def file_data(rows):
    assert all(len({abs(lit) for lit in row}) == 3 for row in rows)
    return serialize_dimacs(max(abs(lit) for row in rows for lit in row), rows)


def model_for_pins(n, support):
    return {pin(i, True) for i in range(n) if support >> i & 1} | {pin(i, False) for i in range(n)}


def fits(rows, model):
    return all(any((abs(lit) in model) == (lit > 0) for lit in row) for row in rows)


def audit(solver):
    tested = 0
    for n in range(1, 8):
        total, bad = linear_census(n)
        assert bad == ({7: 30} if n == 7 else {})
        print(f'{n} vertices: {total} labeled linear triple systems, obstructions by size {bad}')
    for n in (3, 4, 5):
        edges = triple_masks(n)
        impossible = []
        for chosen in range(1 << len(edges)):
            triples = [edge for i, edge in enumerate(edges) if chosen >> i & 1]
            if not colorings(n, triples):
                impossible.append(chosen)
        assert impossible == ([(1 << len(edges)) - 1] if n == 5 else [])
    fano = [sum(1 << j for j in e) for e in
            ((0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5))]
    for n, edges in ((5, triple_masks(5)), (7, fano)):
        base = file_data(hypergraph_file(n, edges, 0))
        for marked in range(1 << n):
            rows = hypergraph_file(n, edges, marked)
            data = file_data(rows)
            assert len(data) == len(base)
            assert sum((x ^ y).bit_count() for x, y in zip(data, base)) == marked.bit_count()
            want = all(edge & marked != edge for edge in edges)
            for support in range(1 << n):
                expected = marked & support == marked and all(edge & support != edge for edge in edges)
                assert fits(rows, model_for_pins(n, support)) == expected
            if solver:
                assert solve_dimacs(solver, data) == want
            tested += 1
    for k in (1, 2, 3):
        for b in range(1, 8):
            base = file_data(counter_file(b, k, 0))
            for active in range(1 << b):
                rows = counter_file(b, k, active)
                assert counter_file(b + 1, k, active)[:len(rows)] == rows
                model = model_for_pins(b, active)
                for i in range(b + 1):
                    for j in range(1, k + 2):
                        if (active % (1 << i)).bit_count() >= j:
                            model.add(registers(k, i, j))
                expected = active.bit_count() <= k
                assert fits(rows, model) == expected
                data = file_data(rows)
                assert len(data) == len(base)
                assert sum((x ^ y).bit_count() for x, y in zip(base, data)) == active.bit_count()
                if solver:
                    assert solve_dimacs(solver, data) == expected
                tested += 1
    print(f'{tested} complete edit settings verified' + (' with CaDiCaL' if solver else ''))


if __name__ == '__main__':
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument('--solver', help='also solve every serialized file using an external DIMACS solver')
    audit(args.parse_args().solver)
