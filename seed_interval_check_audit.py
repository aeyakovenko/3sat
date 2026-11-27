"""Finite checks for the seed-row interval check and the pinned DIMACS files.

Run with Python 3 from the directory that holds this script. It uses CaDiCaL from
PATH or from an elan toolchain, and falls back to a slower built-in solver."""
from collections import Counter
from itertools import combinations, permutations, product
from pathlib import Path
from random import Random
from shutil import which
from subprocess import run

from quadratic_read_repair_audit import Circuit, parsed, solver, upper_and_truth


def sat_checker():
    executable = which("cadical")
    if not executable:
        candidates = sorted((Path.home() / ".elan/toolchains").glob("*/bin/cadical"))
        executable = candidates[0] if candidates else None
    if executable:
        def check(data):
            parsed(data)  # check proper literal rows independently
            result = run([executable, "-q"], input=data, capture_output=True)
            assert result.returncode in (10, 20), result.stderr
            return result.returncode == 10
        print("DIMACS checker:", executable)
        return check
    solve = solver()
    print("DIMACS checker: Round 3 libz3/DPLL routine")
    def check(data):
        count, clauses = parsed(data)
        return solve(clauses, count)
    return check


def poly_bit(poly, seed):
    return sum(seed & mask == mask for mask in poly) % 2


def poly_gate(circuit, poly, wires):
    return circuit.xor(circuit.all(wire for j, wire in enumerate(wires) if mask >> j & 1)
                       for mask in poly)


def put_bit(word, index, value):
    return (word & ~(1 << index)) | (value << index)


def native_block(old, new, seed, direct):
    # Old state is one address register and three mutable one-bit cells.
    control, *memory = [poly_bit(poly, seed) for poly in old]
    reply = memory[control]
    aux = None
    updated_seed = seed
    if reply:
        memory[1 - control] = control
        if direct:
            updated_seed = put_bit(seed, 1 - control, control)
        else:
            aux = seed >> (2 + control) & 1
            updated_seed = put_bit(seed, 4 + control, aux ^ control)
    actual = [control] + memory
    desired = [poly_bit(poly, updated_seed) for poly in new]
    return (control, reply, aux), [a ^ b for a, b in zip(actual, desired)]


def defect_gate(old, new, variables, direct):
    circuit = Circuit(variables)
    pins = list(range(4, 4 + variables))
    control, m0, m1, watch = [poly_gate(circuit, poly, pins) for poly in old]
    def mux(select, on, off):
        return circuit.any([circuit.all([select, on]), circuit.all([-select, off])])
    reply = mux(control, m1, m0)
    changed_if_zero = circuit.all([reply, -control])
    changed_if_one = circuit.all([reply, control])
    actual = [control, mux(changed_if_one, -1, m0), mux(changed_if_zero, 1, m1), watch]
    updated = pins.copy()
    if direct:
        updated[0], updated[1] = (mux(changed_if_one, -1, pins[0]),
                                  mux(changed_if_zero, 1, pins[1]))
    else:
        updated[4], updated[5] = (mux(changed_if_zero, pins[2], pins[4]),
                                  mux(changed_if_one, -pins[3], pins[5]))
    desired = [poly_gate(circuit, poly, updated) for poly in new]
    return circuit, circuit.any(circuit.xor([a, b]) for a, b in zip(actual, desired))


def check_intervals(check):
    rng = Random(202609)
    variables = 8
    lanes = 1 << variables
    columns = [sum(((seed >> i) & 1) << seed for seed in range(lanes))
               for i in range(variables)]
    counts = Counter()
    for degree in (1, 2, 3):
        pool = [mask for mask in range(lanes) if mask.bit_count() <= degree]
        def random_poly():
            return set(rng.sample(pool, rng.randrange(min(len(pool), 7) + 1)))
        for trial in range(48):
            direct = trial % 3 == 0
            if direct:
                # Two systematic data bits and a possibly nonlinear untouched one.
                # The control and last cell use only unmodified seed coordinates.
                old = [{m for m in random_poly() if not m & 3}, {1}, {2},
                       {m for m in random_poly() if not m & 3}]
            else:
                old = [random_poly() for _ in range(4)]
            new = [poly.copy() for poly in old] if trial % 2 == 0 else [random_poly() for _ in old]
            circuit, output = defect_gate(old, new, variables, direct)
            truth = circuit.packed(output, columns, lanes)
            minima = {}
            for seed in range(lanes):
                path, failures = native_block(old, new, seed, direct)
                assert any(failures) == bool(truth >> seed & 1)
                for index, failure in enumerate(failures):
                    if failure:
                        key = path, index
                        minima[key] = min(seed.bit_count(), minima.get(key, variables))
            for ((control, _, aux), index), weight in minima.items():
                observed = [old[0], old[1 + control]]
                # Account for the actual degrees, constants included at cost zero.
                freeze = sum(max((m.bit_count() for m in p), default=0) for p in observed)
                residual = max((m.bit_count() for m in old[index] | new[index]), default=0)
                bound = freeze + (aux is not None) + residual
                assert weight <= bound
                counts["nonvacuous path-coordinate checks"] += bound < variables
                counts["failing path-coordinate groups"] += 1
            assert check(circuit.dimacs(output)) == bool(truth)
            counts["SAT defect files" if truth else "UNSAT defect files"] += 1
            counts["pointwise circuit comparisons"] += lanes
    print("Intervals:", dict(counts))


def check_sharpness():
    cases = seeds = largest = 0
    for d, reads, aux_reads in product((1, 2, 3), range(4), range(3)):
        total = d * (reads + 1) + aux_reads
        blocks = [((1 << d) - 1) << (d * j) for j in range(reads + 1)]
        side = ((1 << aux_reads) - 1) << (d * len(blocks))
        first_failure = None
        for seed in range(1 << total):
            guest = [poly_bit({mask}, seed) for mask in blocks]
            new = seed
            if all(guest[:-1]) and seed & side == side:
                new = put_bit(seed, d * reads, 0)
            bad = guest != [poly_bit({mask}, new) for mask in blocks]
            if bad:
                assert first_failure is None
                first_failure = seed
        assert first_failure == (1 << total) - 1
        cases += 1
        seeds += 1 << total
        largest = max(largest, total)
    print("Sharp instances / seeds / largest necessary weight:", cases, seeds, largest)


def pinned_file(mapping):
    m = len(mapping)
    x = lambda j: 4 + j
    v = m + 3
    digits = len(str(v))
    clauses = [tuple(-j if bits >> (j - 1) & 1 else j for j in (1, 2, 3))
               for bits in range(1, 8)]
    clauses.extend((-1, x(j), 2) for j in range(m))
    clauses.extend((x(value) if i < m // 2 else -x(value), 1, 2)
                   for i, value in enumerate(mapping))
    lines = [f"p cnf {v} {len(clauses)}\n"]
    lines.extend(" ".join(f"{lit:>{digits + 1}}" for lit in clause) + " 0\n"
                 for clause in clauses)
    data = "".join(lines).encode("ascii")
    count = 2 * m + 7
    assert len(data) == 8 + digits + len(str(count)) + count * (3 * digits + 8)
    return data


def check_inverse(check, selector_truth):
    counts = Counter()
    for m in (2, 4):
        for mapping in product(range(m), repeat=m):
            data = pinned_file(mapping)
            fields = [int(line.split()[0]) for line in data.splitlines()[-m:]]
            f = [abs(field) - 4 for field in fields]
            assert tuple(f) == mapping
            assert all((field > 0) == (i < m // 2) for i, field in enumerate(fields))
            scratch = [0] * m
            repeated = False
            for i, value in enumerate(f):
                last = scratch[value] - 1
                if last >= 0 and (last < m // 2) == (i < m // 2):
                    repeated = True
                scratch[value] = i + 1
            halves = (set(f[:m // 2]), set(f[m // 2:]))
            disjoint = halves[0].isdisjoint(halves[1])
            assert repeated == any(len(half) < m // 2 for half in halves)
            interval_verdict = all(pos and f[pos - 1] == y for y, pos in enumerate(scratch))
            if not repeated:
                assert disjoint == interval_verdict
            assert check(data) == disjoint
            counts["SAT" if disjoint else "UNSAT"] += 1
            p, neg = (sum(1 << value for value in half) for half in halves)
            assert bool(selector_truth[(p << 12) | (neg << 4)]) == disjoint
            if len(set(f)) == m:
                for cut in range(m + 1):
                    for bank in product(range(m + 2), repeat=m):
                        finish = all(1 <= bank[y] <= m and f[bank[y] - 1] == y
                                     for y in range(cut, m))
                        assert finish == (bank[cut:] == tuple(scratch[cut:]))
                        counts["counterfactual suffixes"] += 1
    print("Ordinary files:", dict(counts))
    for m in (4, 256, 4096):
        print("m / physical bits:", m, 8 * len(pinned_file(range(m))))

    fibers = Counter()
    for f in permutations(range(8)):
        pos, neg = (sum(1 << value for value in half) for half in (f[:4], f[4:]))
        code = ((pos & 15) << 12) | ((pos >> 4) << 8) | ((neg & 15) << 4) | (neg >> 4)
        assert selector_truth[code]
        fibers[code] += 1
    assert set(fibers.values()) == {576} and len(fibers) == 70
    print("Eight-name permutations / selector files / preimages:", sum(fibers.values()),
          len(fibers), min(fibers.values()))


def check_sampling():
    # Verify the adaptive exposure law used in the advice count.
    from math import comb, factorial
    m = 7
    cases = 0
    for length, targets in product(range(1, 6), range(1, 4)):
        hits = 0
        for pi in permutations(range(m)):
            remaining = list(range(m))
            start = 1
            images = set()
            for _ in range(length):
                value = pi[remaining.pop(start % len(remaining))]
                images.add(value)
                start = 2 * start + value + 1
            hits += all(y in images for y in range(targets))
        assert hits * comb(m, targets) == factorial(m) * comb(length, targets)
        cases += 1
    print("Adaptive sampling identities at m=7:", cases)


if __name__ == "__main__":
    checker = sat_checker()
    check_intervals(checker)
    check_sharpness()
    check_inverse(checker, upper_and_truth())
    check_sampling()
