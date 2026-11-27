"""Audit the dense decimal projection from list duplicates to exact 3-CNF.

Install pycosat (PicoSAT's Python interface) to run the SAT checks.
"""

from functools import lru_cache
from itertools import product
from random import Random

import pycosat


def bank_name(bank, suffix, digits):
    return int(str(bank) + format(suffix, f"0{digits}b"))


@lru_cache(maxsize=None)
def fixed_layout(w):
    rows = 1 << w
    digits = (w+3)//4
    bank_limit = 9 * 10**digits - 1
    maximum = bank_limit

    def fresh():
        nonlocal maximum
        maximum += 1
        return maximum

    pad, other_pad, guard, passive = [fresh() for _ in range(4)]
    selected = [fresh() for _ in range(rows)]
    core = []
    for bank in range(1, 9):
        prior = fresh()
        core.append((-prior,))
        for field in range(1 << digits):
            flag = bank_name(bank, field, digits)
            current = fresh()
            core.extend([(-flag, current), (-prior, current), (-flag, -prior)])
            prior = current

    def gate(a, b, use_and):
        c = fresh()
        if use_and:
            core.extend([(a, -c), (b, -c), (-a, -b, c)])
        else:
            core.extend([(-a, c), (-b, c), (a, b, -c)])
        return c

    seen, two = fresh(), fresh()
    core.extend([(-seen,), (-two,)])
    for s in selected:
        two = gate(two, gate(seen, s, True), False)
        seen = gate(seen, s, False)
    core.append((two,))

    strict = []
    for clause in core:
        if len(clause) == 1:
            strict.extend(clause + (p, q) for p, q in product((pad, -pad), (other_pad, -other_pad)))
        elif len(clause) == 2:
            strict.extend(clause + (p,) for p in (pad, -pad))
        else:
            strict.append(clause)
    # A fresh true guard can satisfy all clauses covering the unused bank IDs.
    strict.extend((guard, v, passive) for v in range(1, bank_limit+1))
    count = len(strict) + 16*rows
    header = f"p cnf {maximum} {count}\n".encode("ascii")
    suffix = "".join(f"{a} {b} {c} 0\n" for a, b, c in strict).encode("ascii")
    return header, suffix, tuple(selected), pad, digits


def encode(w, values):
    header, tail, selected, pad, digits = fixed_layout(w)
    assert len(values) == len(selected) and all(0 <= v < 1 << (2*w) for v in values)
    variable_lines = []
    for choice, value in zip(selected, values):
        for chunk in range(8):
            field = (value >> (digits*chunk)) % (1 << digits)
            flag = bank_name(chunk+1, field, digits)
            variable_lines.extend(f"{-choice} {flag} {p} 0\n" for p in (pad, -pad))
    return header + "".join(variable_lines).encode("ascii") + tail


def sat_from_bytes(file):
    header, *lines = file.decode("ascii").splitlines()
    p, cnf, variables, count = header.split()
    assert (p, cnf) == ("p", "cnf") and int(count) == len(lines)
    clauses = []
    names = set()
    for line in lines:
        a, b, c, end = map(int, line.split())
        terms = [a, b, c]
        assert end == 0 and len({abs(t) for t in terms}) == 3
        names.update(map(abs, terms))
        clauses.append(terms)
    assert names == set(range(1, int(variables)+1))
    verdict = pycosat.solve(clauses)
    assert verdict != "UNKNOWN"
    return verdict != "UNSAT"


def check_columns(w, rng):
    rows = 1 << w
    width = 2*w
    zeros = (0,) * rows
    baseline = encode(w, zeros)
    offsets = []
    touched = set()
    for row in range(rows):
        for bit in range(width):
            input_words = list(zeros)
            input_words[row] = 1 << bit
            variant = encode(w, input_words)
            assert len(variant) == len(baseline)
            changed = [i for i, (a, b) in enumerate(zip(baseline, variant)) if a != b]
            assert len(changed) == 2 and touched.isdisjoint(changed)
            assert all((baseline[i], variant[i]) == (ord('0'), ord('1')) for i in changed)
            touched.update(changed)
            offsets.append(changed)
    for _ in range(8):
        sample = [rng.randrange(1 << width) for _ in range(rows)]
        expected = bytearray(baseline)
        for i, copies in enumerate(offsets):
            bit = (sample[i//width] >> (i%width)) & 1
            for j in copies:
                expected[j] += bit
        assert expected == encode(w, sample)
    return len(offsets)


def main():
    rng = Random(1124)
    solved = projected = 0
    for w in (1, 2, 3, 5):
        rows = 1 << w
        width = 2*w
        inputs = list(product(range(1 << width), repeat=rows)) if w == 1 else []
        for i in range(12):
            distinct = rng.sample(range(1 << width), rows)
            inputs.append(tuple(distinct))
            duplicate = distinct.copy()
            duplicate[(i+1)%rows] = duplicate[i%rows]
            inputs.append(tuple(duplicate))
        for values in inputs:
            assert sat_from_bytes(encode(w, values)) == (len(set(values)) < rows)
            solved += 1
        projected += check_columns(w, rng)
    lengths = []
    for w in range(1, 11):
        rows = 1 << w
        size = len(encode(w, (0,) * rows))
        assert rows*w <= size <= 2500*rows*w
        lengths.append(size)
    print(f"PicoSAT checked {solved} serialized formulas; {projected} single-bit columns checked")
    print("Byte lengths for w=1..10:", *lengths)


if __name__ == "__main__":
    main()
