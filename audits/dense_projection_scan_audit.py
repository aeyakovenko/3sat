"""Finite semantic audit of the scan-time recognizer for the dense SAT projection.

Install pycosat, as for dense_ascii_chunk_circuit_audit.py. Python runtimes are
not operation counts for the word RAM. All stored clauses retain multiplicity.
"""
from functools import lru_cache
from itertools import product
from random import Random

import pycosat
from dense_ascii_chunk_circuit_audit import encode


def public_names(k):
    count = 1 << k
    digits = (k + 3) // 4
    identifiers = 9 * 10 ** digits - 1
    bound = identifiers + 14 + 4 * count + 8 * (1 << digits)
    return count, digits, identifiers, bound


@lru_cache(maxsize=None)
def template(k):
    count, digits, identifiers, bound = public_names(k)
    pad, other, guard, passive = range(identifiers + 1, identifiers + 5)
    selector = identifiers + 5
    flags = {}
    radix = 1 << digits
    decimal = [0] * radix
    for value in range(1, radix):
        decimal[value] = 10 * decimal[value // 2] + value % 2

    fixed = []

    def clause(*terms):
        if len(terms) == 3:
            fixed.append(terms)
        elif len(terms) == 2:
            fixed.extend(terms + (p,) for p in (pad, -pad))
        else:
            fixed.extend(terms + (p, q) for p in (pad, -pad) for q in (other, -other))

    def gate(a, b, output, conjunction):
        if conjunction:
            clause(a, -output)
            clause(b, -output)
            clause(-a, -b, output)
        else:
            clause(-a, output)
            clause(-b, output)
            clause(a, b, -output)

    bank_start = selector + count
    for bank in range(8):
        previous = bank_start + bank * (1 + radix)
        clause(-previous)
        for value in range(radix):
            flag = (bank + 1) * 10 ** digits + decimal[value]
            flags[flag] = bank, value
            current = previous + 1
            clause(-flag, current)
            clause(-previous, current)
            clause(-flag, -previous)
            previous = current

    seen = bank_start + 8 * (1 + radix)
    two = seen + 1
    clause(-seen)
    clause(-two)
    next_id = two + 1
    for row in range(count):
        selected = selector + row
        gate(seen, selected, next_id, True)
        gate(two, next_id, next_id + 1, False)
        gate(seen, selected, next_id + 2, False)
        two, seen = next_id + 1, next_id + 2
        next_id += 3
    assert seen == bound
    clause(two)
    fixed.extend((guard, v, passive) for v in range(1, identifiers + 1))
    return fixed, flags, pad, selector


@lru_cache(maxsize=None)
def block_tokens(block):
    """A block is reduced to short signed decimal fragments and separators."""
    events = []
    i = 0
    while i < len(block):
        if block[i] in b" \t\n\r":
            while i < len(block) and block[i] in b" \t\n\r":
                i += 1
            events.append(None)
            continue
        first = i
        while i < len(block) and block[i] not in b" \t\n\r":
            i += 1
        raw = block[first:i]
        minus = raw.startswith(b"-")
        digits = raw[int(minus):]
        if digits and not digits.isdigit():
            raise ValueError("invalid numeric fragment")
        events.append((minus, 10 ** len(digits), int(digits or b"0"), bool(digits)))
    return events


def read_body(body, block_size, bound):
    fields = []
    pending = negative = digit_seen = False
    current = 0
    for offset in range(0, len(body), block_size):
        for event in block_tokens(body[offset:offset + block_size]):
            if event is None:
                if pending:
                    if not digit_seen:
                        raise ValueError("missing digits")
                    fields.append(-current if negative else current)
                pending = negative = digit_seen = False
                current = 0
                continue
            minus, scale, value, nonempty = event
            if minus and pending:
                raise ValueError("interior minus")
            pending = True
            negative |= minus
            digit_seen |= nonempty
            current = current * scale + value
            if current > bound:
                raise ValueError("identifier outside header")
    if pending:
        if not digit_seen:
            raise ValueError("missing digits")
        fields.append(-current if negative else current)
    if len(fields) % 4 or any(fields[3::4]):
        raise ValueError("clause count or terminator")
    clauses = [tuple(fields[j:j+3]) for j in range(0, len(fields), 4)]
    if any(0 in c or len(set(map(abs, c))) != 3 for c in clauses):
        raise ValueError("improper clause")
    return clauses


def radix_clauses(clauses, bound):
    ordered = [tuple(sorted(c)) for c in clauses]
    for column in (2, 1, 0):
        buckets = [[] for _ in range(2 * bound + 1)]
        for c in ordered:
            buckets[c[column] + bound].append(c)
        ordered = [c for bucket in buckets for c in bucket]
    return ordered


def recognize(raw, block_size):
    header, body = raw.split(b"\n", 1)
    p, cnf, top, size = header.split()
    assert (p, cnf) == (b"p", b"cnf")
    bound, size = int(top), int(size)
    k = 1
    while public_names(k)[3] < bound:
        k += 1
    count, digits, _, expected_bound = public_names(k)
    if expected_bound != bound:
        return None
    clauses = read_body(body, block_size, bound)
    fixed, flags, pad, selector = template(k)
    if len(clauses) != size or size != len(fixed) + 16 * count:
        return None
    pieces = [[None] * 8 for _ in range(count)]
    names = {piece: flag for flag, piece in flags.items()}
    for c in clauses:
        if pad not in c:
            continue
        row = next((-lit - selector for lit in c if selector <= -lit < selector + count), None)
        tagged = next((flags[lit] for lit in c if lit in flags), None)
        if row is None or tagged is None:
            continue
        bank, value = tagged
        if pieces[row][bank] is not None:
            return None
        pieces[row][bank] = value
    expected = list(fixed)
    data = []
    for row, chunks in enumerate(pieces):
        if None in chunks:
            return None
        value = sum(chunk << (digits * bank) for bank, chunk in enumerate(chunks))
        if value >= 1 << (2 * k):
            return None
        data.append(value)
        for bank, chunk in enumerate(chunks):
            flag = names[bank, chunk]
            expected.extend((-(selector + row), flag, p) for p in (pad, -pad))
    if radix_clauses(clauses, bound) != radix_clauses(expected, bound):
        return None
    order = list(range(count))
    for shift in (0, k):
        buckets = [[] for _ in range(count)]
        for i in order:
            buckets[(data[i] >> shift) % count].append(i)
        order = [i for bucket in buckets for i in bucket]
    return any(data[a] == data[b] for a, b in zip(order, order[1:]))


def permute(raw, rng):
    head, *lines = raw.splitlines()
    clauses = [line.split()[:3] for line in lines]
    for c in clauses:
        rng.shuffle(c)
    rng.shuffle(clauses)
    return head + b"\n" + b"\t \n".join(b" \t".join(c + [b"0"]) for c in clauses) + b" " * 57 + b"\n"


def check_edit_overlap():
    alternatives = split_checks = 0
    for k in range(2, 7):
        count = 1 << k
        digits = (k + 3) // 4
        # Finite widths cannot yet supply sixteen independent bits. Give
        # each of the k coordinates a separate available bank where possible.
        chosen = list(range(0, 2 * k, digits))[:k]
        chosen.extend(bit for bit in range(2 * k) if bit not in chosen)
        chosen = chosen[:k]
        original = [sum(((i >> j) % 2) << bit for j, bit in enumerate(chosen))
                    for i in range(count)]
        base = encode(k, original)
        n = 8 * len(base)
        word_bytes = 2 * (((n + 1).bit_length() + 15) // 16)
        seen_words = set()
        for i in range(count):
            for j in range(k):
                edit = original.copy()
                edit[i] = original[i ^ (1 << j)]
                rival = encode(k, edit)
                assert len(rival) == len(base)
                changed = [t for t, (a, b) in enumerate(zip(base, rival)) if a != b]
                assert len(changed) == 2
                pair = {t // word_bytes for t in changed}
                assert len(pair) == 2 and pair.isdisjoint(seen_words)
                seen_words.update(pair)
                if k <= 4 and i == 0:
                    for t in changed:
                        split = bytearray(base)
                        split[t] = rival[t]
                        head, body = split.split(b"\n", 1)
                        clauses = read_body(bytes(body), 7, int(head.split()[2]))
                        assert isinstance(pycosat.solve(clauses), list)
                        split_checks += 1
                alternatives += 1
    return alternatives, split_checks


def main():
    rng = Random(19)
    accepted = rejected = independent = 0
    for k in (1, 2, 3, 5, 9):
        count = 1 << k
        if k == 1:
            cases = list(product(range(4), repeat=2))
        else:
            distinct = rng.sample(range(1 << (2 * k)), count)
            cases = [distinct, [distinct[1]] + distinct[1:]]
        for ids in cases:
            raw = encode(k, ids)
            truth = len(set(ids)) < count
            for version in (raw, permute(raw, rng)):
                for width in ((1, 3, 7) if k <= 2 else (7,)):
                    assert recognize(version, width) == truth
                    accepted += 1
            head, *lines = raw.splitlines()
            damaged = list(lines)
            damaged[0] = damaged[1]
            corrupt = head + b"\n" + b"\n".join(damaged) + b"\n"
            assert recognize(corrupt, 5) is None
            damaged = list(lines)
            damaged[-1] = damaged[-2]
            corrupt_fixed = head + b"\n" + b"\n".join(damaged) + b"\n"
            assert recognize(corrupt_fixed, 5) is None
            rejected += 2
            if k <= 5:
                multiset = read_body(raw.split(b"\n", 1)[1], 7, public_names(k)[3])
                solution = pycosat.solve(multiset)
                assert solution != "UNKNOWN" and (solution != "UNSAT") == truth
                independent += 1
    alternatives, split_checks = check_edit_overlap()
    print(f"{alternatives} duplicate-producing two-word edits with disjoint supports, "
          f"{split_checks} satisfiable single-copy corruptions checked by PicoSAT")
    print(f"{accepted} canonical/reordered recognitions, {rejected} corrupted templates rejected, "
          f"{independent} independent PicoSAT verdicts")


if __name__ == "__main__":
    main()
