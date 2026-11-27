"""Audit canonical metadata for long DIMACS names, including equal and prefix cases."""

import re
from argparse import ArgumentParser
from dataclasses import dataclass, replace
from itertools import pairwise, permutations, product
from subprocess import run


@dataclass(frozen=True)
class Occurrence:
    start: int
    end: int
    name: bytes
    negative: bool


@dataclass(frozen=True)
class Index:
    slots: tuple
    permutation: tuple
    lcp: tuple
    first: tuple


def file_of(rows):
    names = [int(name.lstrip("-")) for row in rows for name in row]
    header = f"c signs and names follow\np cnf {max(names)} {len(rows)}\n"
    return (header + "".join("\t".join(row) + " 0\n" for row in rows)).encode("ascii")


def parse(raw):
    header = re.search(rb"^p cnf (\d+) (\d+)\n", raw, re.MULTILINE)
    assert header is not None
    rows, current = [], []
    for token in re.finditer(rb"-?\d+", raw[header.end() :]):
        txt = token.group()
        if txt == b"0":
            assert len(current) == 3 and len({o.name for o in current}) == 3
            rows.append(tuple(current))
            current = []
        else:
            neg = txt.startswith(b"-")
            start = header.end() + token.start() + int(neg)
            end = header.end() + token.end()
            current.append(Occurrence(start, end, raw[start:end], neg))
    assert not current and len(rows) == int(header.group(2))
    return rows


def common(u, v):
    return next(
        (i for i, (a, b) in enumerate(zip(u, v)) if a != b), min(len(u), len(v))
    )


def canonical(raw, rows, h, b):
    occurrences = [o for row in rows for o in row]
    slots = [None] * ((len(raw) + b - 1) // b)
    first = [None] * 10**h
    for o in occurrences:
        if len(o.name) <= h:
            key = int(o.name)
            if first[key] is None:
                first[key] = o.start
        if len(o.name) > b:
            slot = o.start // b
            assert slots[slot] is None
            slots[slot] = (o.start, o.end)

    def key(i):
        if slots[i] is None:
            return 0, b"", i
        start, end = slots[i]
        return 1, raw[start:end], start

    order = tuple(sorted(range(len(slots)), key=key))
    prefix = []
    for i, j in pairwise(order):
        prefix.append(
            0
            if slots[i] is None or slots[j] is None
            else common(raw[slice(*slots[i])], raw[slice(*slots[j])])
        )
    return Index(tuple(slots), order, tuple(prefix), tuple(first))


def checks(raw, rows, h, b, index, short, bits):
    occurrences = [o for row in rows for o in row]
    by_start = {o.start: o for o in occurrences}
    for key, pointer in enumerate(index.first):
        if pointer is None:
            if short[key]:
                return False
        elif pointer not in by_start or by_start[pointer].name != str(key).encode():
            return False
    for o in occurrences:
        if len(o.name) <= h:
            ptr = index.first[int(o.name)]
            if ptr is None or ptr > o.start:
                return False
    occupied = {o.start // h for o in occurrences if len(o.name) > h}
    if any(val and slot not in occupied for slot, val in enumerate(bits)):
        return False
    for u in occurrences:
        for v in occurrences:
            if (
                h < len(u.name) <= b
                and u.name == v.name
                and bits[u.start // h] != bits[v.start // h]
            ):
                return False
    for i, slot in enumerate(index.slots):
        required = [o for o in occurrences if o.start // b == i and len(o.name) > b]
        if not required:
            if slot is not None:
                return False
        elif slot != (required[0].start, required[0].end):
            return False
    order = index.permutation
    if sorted(order) != list(range(len(index.slots))):
        return False
    for k, (i, j) in enumerate(pairwise(order)):
        p, q, l = index.slots[i], index.slots[j], index.lcp[k]
        if p is None or q is None:
            if l != 0 or (p is not None) or (q is None and i >= j):
                return False
            continue
        u, v = raw[slice(*p)], raw[slice(*q)]
        if not 0 <= l <= min(len(u), len(v)) or any(u[n] != v[n] for n in range(l)):
            return False
        if l < len(u):
            if l >= len(v) or u[l] >= v[l]:
                return False
        elif l == len(v) and (p[0] >= q[0] or bits[p[0] // h] != bits[q[0] // h]):
            return False

    def value(o):
        return short[int(o.name)] if len(o.name) <= h else bits[o.start // h]

    return all(any(bool(value(o)) != o.negative for o in row) for row in rows)


def bits_for(raw, rows, h, assignment):
    short = [False] * 10**h
    bits = [False] * ((len(raw) + h - 1) // h)
    for row in rows:
        for o in row:
            if len(o.name) <= h:
                short[int(o.name)] = assignment[o.name]
            else:
                bits[o.start // h] = assignment[o.name]
    return short, bits


def main(solver):
    h, b = 1, 4
    sources = [
        [("1", "12", "12345"), ("-12", "123456", "12345"), ("-12345", "123456", "9")],
        [("12345", "12346", "-123456"), ("123456", "-12345", "12346")],
        [("1", "2", "3")]
        + [
            tuple(("-" if sign else "") + str(i + 1) for i, sign in enumerate(p))
            for p in product((False, True), repeat=3)
            if not all(p)
        ],
        [("-1", "-12", "12340"), ("1", "-12340", "-12341"), ("12341", "125", "123401")],
    ]
    # Eight sign patterns give an unsatisfiable proper source.
    sources.append(
        [
            tuple(("-" if s else "") + str(j + 1) for j, s in enumerate(signs))
            for signs in product((False, True), repeat=3)
        ]
    )
    tested = tampered = 0
    counts = []
    for source in sources:
        raw = file_of(source)
        rows = parse(raw)
        index = canonical(raw, rows, h, b)
        names = sorted({o.name for row in rows for o in row})
        models = 0
        for vals in product((False, True), repeat=len(names)):
            assignment = dict(zip(names, vals))
            short, bits = bits_for(raw, rows, h, assignment)
            want = all(any(assignment[o.name] != o.negative for o in r) for r in rows)
            assert checks(raw, rows, h, b, index, short, bits) == want
            tested += 1
            models += want
            if not want or models > 1:
                continue
            for i, old in enumerate(index.lcp):
                for new in (old - 1, old + 1):
                    changed = index.lcp[:i] + (new,) + index.lcp[i + 1 :]
                    assert not checks(
                        raw, rows, h, b, replace(index, lcp=changed), short, bits
                    )
                    tampered += 1
            order = index.permutation
            for i in range(len(order) - 1):
                perm = order[:i] + (order[i + 1], order[i]) + order[i + 2 :]
                assert not checks(
                    raw, rows, h, b, replace(index, permutation=perm), short, bits
                )
                tampered += 1
            occupied = [s for s in order if index.slots[s] is not None]
            if 1 < len(occupied) <= 7:
                inactive = order[: len(order) - len(occupied)]
                for perm in permutations(occupied):
                    plo = inactive + perm
                    lcp = tuple(
                        0
                        if index.slots[i] is None or index.slots[j] is None
                        else common(
                            raw[slice(*index.slots[i])], raw[slice(*index.slots[j])]
                        )
                        for i, j in pairwise(plo)
                    )
                    assert checks(
                        raw,
                        rows,
                        h,
                        b,
                        replace(index, permutation=plo, lcp=lcp),
                        short,
                        bits,
                    ) == (plo == order)
                    tampered += 1
        counts.append(models)
        if solver:
            result = run([solver, "-q"], input=raw, capture_output=True, check=False)
            assert result.returncode == (10 if models else 20)
    print(
        f"{tested} truth assignments on {len(sources)} physical files, model counts {counts}"
    )
    print(
        f"{tampered} prefix-length, order and fully re-certified permutation tests passed"
    )


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--solver")
    main(parser.parse_args().solver)
