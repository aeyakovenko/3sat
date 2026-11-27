"""Finite checks for the canonical clause count and its elapsed-time application."""
from collections import Counter, defaultdict
from functools import cache
from itertools import combinations, product
from math import comb


def literal_key(x):
    return 2 * abs(x) + int(x < 0)


def canonical(rows):
    names = sorted({abs(x) for row in rows for x in row})
    rank = {name: i + 1 for i, name in enumerate(names)}
    distinct = set()
    for row in rows:
        dense = [rank[abs(x)] if x > 0 else -rank[abs(x)] for x in row]
        distinct.add(tuple(sorted(dense, key=literal_key)))
    return tuple(sorted(distinct, key=lambda r: tuple(map(literal_key, r))))


def header(v, c):
    return f"p cnf {v} {c}\n".encode()


def serialize(rows, final_lf=True):
    v = max(abs(x) for row in rows for x in row)
    body = [" ".join(map(str, row)) + " 0" for row in rows]
    return header(v, len(rows)) + ("\n".join(body) + ("\n" if final_lf else "")).encode()


def parse(blob):
    head, body = blob.split(b"\n", 1)
    tag, fmt, bound, size = head.split()
    assert (tag, fmt) == (b"p", b"cnf")
    data = list(map(int, body.split()))
    assert len(data) == 4 * int(size)
    rows = []
    for i in range(0, len(data), 4):
        row = tuple(data[i:i + 3])
        assert data[i + 3] == 0 and len({abs(x) for x in row}) == 3
        assert all(1 <= abs(x) <= int(bound) for x in row)
        rows.append(row)
    return rows


@cache
def clause_models(v, row):
    # One set bit per satisfying assignment in the complete assignment table.
    table = bytearray(((1 << v) + 7) // 8)
    for assignment in range(1 << v):
        if any(bool((assignment >> (abs(x) - 1)) & 1) == (x > 0) for x in row):
            table[assignment // 8] |= 1 << (assignment % 8)
    return int.from_bytes(table, "little")


def models(v, rows):
    survivors = (1 << (1 << v)) - 1
    for row in rows:
        survivors &= clause_models(v, row)
    return survivors


def anchor():
    return [tuple(s * i for i, s in enumerate(signs, 1))
            for signs in product((1, -1), repeat=3) if min(signs) < 0]


def paired_rows(v, extra, tag):
    return [(1, 2, tag)] + anchor() + [(-1, 2, i) for i in range(4, v + 1)] + list(extra)


def check_pairs(catalog):
    v = 14
    candidates = list(combinations(range(10, v + 1), 3))
    all_true = (1 << v) - 1
    by_size = defaultdict(set)
    tag_words = defaultdict(set)
    for subset in range(1 << len(candidates)):
        extra = [r for i, r in enumerate(candidates) if (subset >> i) & 1]
        pair = []
        for tag in (3, 7):
            blob = serialize(paired_rows(v, extra, tag))
            rows = parse(blob)
            assignment_set = models(v, rows)
            assert bool(assignment_set) == (tag == 7)
            if tag == 7:
                for i, triple in enumerate(candidates):
                    trial = all_true ^ (7 | sum(1 << (x - 1) for x in triple))
                    assert ((assignment_set >> trial) & 1) == 1 - ((subset >> i) & 1)
            core = canonical(rows)
            assert len(core) == len(rows)
            assert core == canonical(parse(serialize(core, final_lf=False)))
            padded = serialize(list(reversed(rows)) + [rows[-1]]) + b" " * 47
            assert core == canonical(parse(padded))
            catalog[core] = bool(assignment_set)
            tag_offset = len(header(v, len(rows))) + 4
            assert blob[tag_offset] == ord(str(tag))
            for coefficient in (1, 4, 32):
                log_ceiling = ((8*len(blob) + 2)**coefficient - 1).bit_length()
                word_bytes = 2 * ((log_ceiling + 15) // 16)
                start = tag_offset // word_bytes * word_bytes
                loaded = int.from_bytes(blob[start:start + word_bytes], "little")
                tag_words[len(extra), coefficient, tag].add(loaded)
            pair.append(blob)
        assert len(pair[0]) == len(pair[1])
        by_size[len(extra)].add(len(pair[0]))
        assert sum((a ^ b).bit_count() for a, b in zip(*pair)) == 1
    assert all(len(lengths) == 1 for lengths in by_size.values())
    assert all(len(values) == 1 for values in tag_words.values())
    assert all(tag_words[size, coef, 3] != tag_words[size, coef, 7]
               for size in by_size for coef in (1, 4, 32))
    print(f"one-bit pairs {1 << len(candidates)}, three-name challenges "
          f"{len(candidates) * (1 << len(candidates))}, distinct cardinality slices {len(by_size)}")


def check_small_counts(catalog):
    # Compare literal subset enumeration with inclusion-exclusion on used names
    # and a generating polynomial for the number of minus signs.
    for v, max_clauses in ((3, 8), (4, 3)):
        pool = [tuple(s * x for x, s in zip(r, signs))
                for r in combinations(range(1, v + 1), 3)
                for signs in product((1, -1), repeat=3)]
        observed = Counter()
        for c in range(1, max_clauses + 1):
            for rows in combinations(pool, c):
                if len({abs(x) for r in rows for x in r}) != v:
                    continue
                core = canonical(rows)
                size = len(serialize(core, final_lf=False))
                observed[c, size] += 1
                catalog[core] = bool(models(v, rows))
        expected = Counter()
        for used in range(v + 1):
            coefficients = Counter({(0, 0): 1})
            for neg in range(4):
                many = comb(used, 3) * comb(3, neg)
                updated = Counter()
                for (c, cost), value in coefficients.items():
                    for k in range(min(many, max_clauses - c) + 1):
                        updated[c + k, cost + neg*k] += value * comb(many, k)
                coefficients = updated
            inclusion = (-1)**(v - used) * comb(v, used)
            for (c, neg), count in coefficients.items():
                if c:
                    size = len(header(v, c)) + 8*c + neg - 1
                    expected[c, size] += inclusion * count
        assert observed == +expected
        print(f"exact core histogram v={v}, {sum(observed.values())} cores, "
              f"{len(observed)} nonempty (clause count, byte length) bins")


def alphabetic_splits(counts):
    # A node is (threshold, left, right); each integer leaf is a legal next word.
    total = sum(counts.values())
    codes = []
    left_mass = 0
    for key, count in sorted(counts.items()):
        depth = 1 + ((total - 1) // count).bit_length()
        cells = 1 << depth
        cell = (2 * left_mass + count) * cells // (2 * total)
        assert left_mass * cells <= cell * total
        assert (cell + 1) * total <= (left_mass + count) * cells
        codes.append((key, format(cell, f"0{depth}b")))
        left_mass += count

    def construct(group, level):
        if len(group) == 1:
            return group[0][0]
        lower = [(key, code) for key, code in group if code[level] == "0"]
        upper = [(key, code) for key, code in group if code[level] == "1"]
        if not lower or not upper:
            return construct(group, level + 1)
        return (upper[0][0], construct(lower, level + 1), construct(upper, level + 1))
    return construct(codes, 0)


def compile_trie(entries, pos):
    if pos == len(entries[0][0]):
        assert len(entries) == 1
        return entries[0][1]
    groups = defaultdict(list)
    for words, label in entries:
        groups[words[pos]].append((words, label))
    selector = alphabetic_splits({key: len(group) for key, group in groups.items()})
    return selector, {key: compile_trie(group, pos + 1) for key, group in groups.items()}


def check_compiler(catalog):
    slices = defaultdict(list)
    for core, label in catalog.items():
        size = len(serialize(core, final_lf=False))
        words = tuple(literal_key(x) for row in core for x in row)
        slices[size, len(core)].append((words, label))
    comparisons, tests, positive = 0, 0, 0
    for entries in slices.values():
        program = compile_trie(entries, 0)
        for words, label in entries:
            state = program
            charged = 0
            for word in words:
                select, children = state
                while isinstance(select, tuple):
                    threshold, left, right = select
                    select = left if word < threshold else right
                    charged += 1
                assert select == word
                state = children[select]
            assert state == label
            assert 2**charged <= len(entries) * 2**(2 * len(words))
            comparisons += charged
            positive += int(label)
            tests += 1
    print(f"threshold replay {tests} cores ({positive} SAT), {len(slices)} slices, "
          f"{comparisons} actual binary comparisons")


def physical_bit_length(d, m):
    v = 10**d - 1
    digits = sum(9 * j * 10**(j - 1) for j in range(1, d + 1))
    return 8 * (8 + d + len(str(m + v + 5)) + 76
                + 8*(v - 3) + digits - 3 + m*(3*d + 5))


def check_rates():
    v = 99
    for m in (0, 1, 98, 198):
        candidates = list(combinations(range(10, 30), 3))[:m]
        for tag in (3, 7):
            assert 8 * len(serialize(paired_rows(v, candidates, tag))) == physical_bit_length(2, m)
    for d in (2, 5, 10, 30, 100, 1000):
        q = 9 * 10**(d - 1)
        m = (10**d - 1) * d
        universe = comb(q, 3)
        bits = physical_bit_length(d, m)
        guaranteed = m * ((universe // m).bit_length() - 1)
        print(f"d={d}, certified log2(count)/physical bits >= "
              f"{(10**6 * guaranteed // bits) / 10**6:.6f}")


def check_absolute():
    cases = 0
    for m in (1, 2, 8, 9, 10, 92, 93, 100, 2000):
        base = serialize(anchor() + [(-1, 2, 3)] * m)
        n = 8 * len(base)
        assert n == 8 * (9*m + 77 + len(str(m + 7)))
        assert models(3, parse(base)) == 1
        first = len(header(3, m + 7)) + 68
        for i in {0, m // 2, m - 1}:
            at = first + 9*i
            assert base[at] == ord("-")
            assert models(3, parse(base[:at] + b" " + base[at + 1:])) == 0
        for d in (1, 2, 7, 16):
            log_ceiling = ((n + 2)**d - 1).bit_length()
            w = 16 * ((log_ceiling + 15) // 16)
            hits = Counter(8*(first + 9*i)//w for i in range(m))
            assert max(hits.values()) <= (w + 71) // 72
            cases += 1
    print(f"absolute scan {cases} physical length/width cases")


def check_census():
    accepted = 0
    shortcut = 0
    worst = 0
    for p, q, m, n in product(range(16), repeat=4):
        pos, neg = p | (q << 4), m | (n << 4)
        truth = pos & neg == 0 and neg != 255
        cells = (p, q, m, n) + (0,) * 12
        seven = m == 8 and cells[q & n] == 4
        if seven:
            assert truth
            shortcut += 1
        # Count one LOAD/branch or ALU per instruction in the published nine-step tree.
        if m == 15:
            if n == 15:
                steps, result = 4, False
            elif p != 0:
                steps, result = 6, False
            else:
                steps, result = 9, q & n == 0
        elif p & m:
            steps, result = 5, False
        else:
            steps, result = 9, q & n == 0
        assert result == truth
        accepted += int(result)
        worst = max(worst, steps)
    assert (accepted, worst) == (6560, 9)
    print(f"16-bit paths 65536 files, {accepted} SAT, {shortcut} accept on the "
          f"4488 shortcut, shared-tree maximum {worst}")


if __name__ == "__main__":
    catalog = {}
    check_small_counts(catalog)
    check_pairs(catalog)
    check_compiler(catalog)
    check_rates()
    check_absolute()
    check_census()
