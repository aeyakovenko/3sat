"""Finite checks for the three-phase SAT revisit argument. No external solver."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from random import Random

from hamming_verdict_projection_audit import dpll
from eight_step_guard_portfolios import replay, TARGETS, pair


def make_layers(n, lanes, seed):
    rng = Random(seed)
    layers = []
    for _ in range(lanes):
        order = list(range(n))
        rng.shuffle(order)
        layers.append([tuple(order[j:j + 3]) for j in range(0, n, 3)])
    return layers


def literal_line(row):
    return " ".join(map(str, (*row, 0)))


def physical_file(symbols, layers):
    n, lanes = len(symbols), len(layers)
    alphabet = 1 << lanes
    def tag(v, s):
        return 4 + v * alphabet + s

    def data_bit(v, j):
        return 4 + n * alphabet + v * lanes + j

    rows = [tuple(-(j + 1) if mask >> j & 1 else j + 1 for j in range(3))
            for mask in range(1, 8)]
    rows.extend((tag(v, s), 1, 2) for v, s in enumerate(symbols))
    for v, s, j in product(range(n), range(alphabet), range(lanes)):
        literal = data_bit(v, j) * (1 if s >> j & 1 else -1)
        rows.append((-tag(v, s), literal, 1))

    largest = data_bit(n - 1, lanes - 1)
    parity = 1  # The first false anchor.
    for j, layer in enumerate(layers):
        for triple in layer:
            x, y, z = (data_bit(v, j) for v in triple)
            ab, abc, next_parity = largest + 1, largest + 2, largest + 3
            largest += 3
            for u, v, out in ((x, y, ab), (ab, z, abc)):
                rows.extend([(-out, u, 1), (-out, v, 1), (out, -u, -v)])
            rows.extend([(parity, abc, -next_parity), (-parity, -abc, -next_parity),
                         (parity, -abc, next_parity), (-parity, abc, next_parity)])
            parity = next_parity
    rows.append((parity, 1, 2))
    lines = [f"c {n}", f"p cnf {largest} {len(rows)}", *map(literal_line, rows)]
    d = 10 + n * (1 + lanes * alphabet) + 10 * lanes * n // 3
    assert len(lines) == d
    h = 1
    while (1 << h) < 32 * h * d + 2:
        h += 1
    raw = b"".join(line.encode().ljust(4 * h - 1) + b"\n" for line in lines)
    assert len(raw) * 8 == d * 32 * h and (8 * len(raw) + 1).bit_length() == h
    return raw


def packed_symbols(values, lanes, width):
    per_word = width // lanes
    assert per_word >= 1
    bank, current = [], 0
    for v, s in enumerate(values):
        current |= s << (lanes * (v % per_word))
        if v % per_word == per_word - 1:
            bank.append(current)
            current = 0
    if len(values) % per_word:
        bank.append(current)
    assert all(0 <= word < 1 << width for word in bank)
    return [bank[v // per_word] >> (lanes * (v % per_word)) & ((1 << lanes) - 1)
            for v in range(len(values))]


def propagate_after_packing(clauses, n, lanes, width):
    # Scalar check of the fast path's logic. Rebuild only the private clauses
    # from their stored symbol fields. DPLL separately checks the unmodified file.
    assert len(set(clauses[:7])) == 7
    assert all({abs(x) for x in r} == {1, 2, 3} and any(x < 0 for x in r)
               for r in clauses[:7])
    alphabet = 1 << lanes
    symbols = []
    for v, row in enumerate(clauses[7:7+n]):
        tag, first, second = row
        s = tag - 4 - v * alphabet
        assert (first, second) == (1, 2) and 0 <= s < alphabet
        symbols.append(s)
    clauses = list(clauses)
    for v, s in enumerate(packed_symbols(symbols, lanes, width)):
        clauses[7+v] = (4 + v * alphabet + s, 1, 2)
    clauses.extend([(-1,), (-2,), (-3,)])
    while clauses:
        units = {r[0] for r in clauses if len(r) == 1}
        assert units, "Recognized templates should finish by propagation"
        if any(-u in units for u in units):
            return False
        clauses = [tuple(x for x in row if -x not in units)
                   for row in clauses if not units.intersection(row)]
        if any(not row for row in clauses):
            return False
    return True


def audit_files():
    counts = Counter()
    lengths = set()
    poison_tests = 0
    rng = Random(173)
    for n, lanes in ((3, 1), (3, 2), (6, 1), (6, 2), (9, 3)):
        layers = make_layers(n, lanes, 27)
        alphabet = 1 << lanes
        inputs = (product(range(alphabet), repeat=n) if alphabet ** n <= 64
                  else [[rng.randrange(alphabet) for _ in range(n)] for _ in range(64)])
        base = None
        for symbols in inputs:
            raw = physical_file(symbols, layers)
            records = raw.splitlines()
            size = len(records[0])
            assert all(len(row) == size for row in records)
            if base is not None:
                assert all(u == v for k, (u, v) in enumerate(zip(records, base))
                           if not 9 <= k < 9 + n)
            base = records
            variables, declared = map(int, records[1].split()[2:])
            rows = [tuple(map(int, line.split())) for line in records[2:]]
            assert len(rows) == declared and all(len(r) == 4 and r[-1] == 0 for r in rows)
            clauses = [r[:-1] for r in rows]
            assert all(len(set(map(abs, r))) == 3 for r in clauses)
            assert {abs(x) for r in clauses for x in r} == set(range(1, variables + 1))
            bit = sum(all(sv >> j & 1 for sv in (symbols[x] for x in edge))
                      for j, layer in enumerate(layers) for edge in layer) % 2
            assert dpll(clauses) == bool(bit)
            assert propagate_after_packing(clauses, n, lanes, 8 * (size + 1)) == bool(bit)
            if bit:
                for slot in {7, 7 + n - 1, len(clauses) // 2, len(clauses) - 1}:
                    # Replace one physical clause word, keeping the length fixed.
                    actual = records.copy()
                    actual[slot + 2] = b"1 2 3 0".ljust(size)
                    assert len(b"\n".join(actual)) + 1 == len(raw)
                    changed = [tuple(map(int, line.split()[:-1])) for line in actual[2:]]
                    assert not dpll(changed)
                    poison_tests += 1
            counts[bit] += 1
            lengths.add((n, lanes, 8 * len(raw)))
    return counts, sorted(lengths), poison_tests


def audit_packing():
    rng = Random(8003)
    count = 0
    for width in (7, 16, 32, 64, 96, 224, 513, 8195):
        for lanes in (1, 2, 3, 5, 8, 13, 128, 4096):
            if lanes > width:
                continue
            batch = width // lanes
            for n in {1, batch, batch + 1, 3 * batch - 1, 3 * batch, 5 * batch + 2}:
                symbols = [rng.getrandbits(lanes) for _ in range(n)]
                assert packed_symbols(symbols, lanes, width) == symbols
                count += 1
    return count


def audit_cuts():
    n, a = 9, 4096
    multiplicity = Counter(tuple(sorted(edge)) for layer in make_layers(n, a, 63217)
                           for edge in layer)
    all_vertices = set(range(n))
    histogram = Counter()
    for first in combinations(range(n), n // 3):
        remaining = all_vertices.difference(first)
        for second in combinations(sorted(remaining), n // 3):
            third = remaining.difference(second)
            rainbow = sum(multiplicity[tuple(sorted((x, y, z)))]
                          for x, y, z in product(first, second, third))
            histogram[rainbow] += 1
    assert sum(histogram.values()) == 1680 and min(histogram) >= 48 * n
    assert sum(k * v for k, v in histogram.items()) == 1680 * 4096 * 3 * 27 // 84
    exponent = (Fraction(2 * a, 27) - 48) ** 2 / (8 * a)
    assert exponent > Fraction(3, 2) and 1 + Fraction(3, 2) + Fraction(9, 8) > 3
    tail = 12 * Fraction(3, 4) ** 12
    assert tail < Fraction(2, 5)
    return min(histogram), max(histogram), exponent, tail


def audit_mixed_widths():
    total = avoided = 0
    for n, a in ((15, 4), (42, 7), (99, 9)):
        alphabet = 1 << a
        digits = len(str(alphabet))
        rows = 10 + n * (1 + a * alphabet) + 10 * a * n // 3
        h = 1
        while (1 << h) < 256 * h * rows + 2:
            h += 1
        slot = 256 * h
        assert (slot * rows + 1).bit_length() == h
        widths = (5*h + 1, 8*h, 11*h + 3, 16*h)
        previous = [-1] * len(widths)
        for v in range(n):
            origin = (9 + v) * slot
            where = (origin + slot // 3 + 7) // 8
            first = where
            while any(8*where // w != (8*(where+digits)-1) // w for w in widths):
                where += 1
            assert 8*(where+digits) <= origin + 2*slot//3
            avoided += first != where
            local_start = where - origin // 8
            name_prefix = str(v + 10).encode()
            all_other = None
            for s in range(alphabet):
                token = str((v + 10) * 10**digits + s).encode()
                before = b"1 " + b" " * (local_start - len(name_prefix) - 2)
                raw = (before + token + b" 2 0").ljust(slot//8-1) + b"\n"
                assert len(raw) == slot//8
                assert tuple(map(int, raw.split())) == (1, (v+10)*10**digits+s, 2, 0)
                frozen = raw[:local_start] + raw[local_start+digits:]
                assert all_other is None or frozen == all_other
                all_other = frozen
            for j, w in enumerate(widths):
                carrier = 8*where // w
                assert carrier > previous[j] and carrier == (8*(where+digits)-1) // w
                previous[j] = carrier
            total += alphabet
    return total, avoided


# A three-phase computation on one writable memory. A store can overwrite an
# original input word. A phase's numerical branches depend on actual load replies.
def phase(p, read, write):
    x = read(p)
    if p == 0:
        write(3 + x, x + 1)
        write(6, 1 + (x & 1))
        if x == 2:
            write(1, 0)
    elif p == 1:
        u = read(3 + x)
        if x != 1:
            write(6, 0)
        write(3 + u % 3, x ^ u)
        read(3 + u % 3)
    else:
        u = read(3 + x)
        v = read(6)
        y = read(u % 2)
        return (x + u + v + y) % 2


def honest(triple):
    memory = dict(enumerate(triple))
    last_writer = {}
    marks = set()
    old_inputs = set()
    final_writes = []
    for p in range(3):
        writes = {}
        def write(key, value):
            memory[key] = writes[key] = value
            last_writer[key] = p

        def read(key):
            writer = last_writer.get(key)
            if writer is not None and writer != p:
                marks.add(key)
            if writer is None and key < 3 and key != p:
                old_inputs.add(key)
            return memory.get(key, 0)
        result = phase(p, read, write)
        final_writes.append(writes)
    carry = tuple((key, final_writes[0].get(key), final_writes[1].get(key))
                  for key in sorted(marks))
    old = tuple((key, triple[key]) for key in sorted(old_inputs))
    return result, carry, old


def local(p, symbol, carry, old):
    writes, defaults = {}, set()
    if p in old and old[p] != symbol:
        return None

    def read(key):
        if key in writes:
            return writes[key]
        if key in carry:
            for previous in reversed(carry[key][:p]):
                if previous is not None:
                    return previous
        else:
            defaults.add(key)
        if key == p:
            return symbol
        if key < 3:
            return old[key]  # Refuse an unlisted off-side original word.
        return 0
    try:
        result = phase(p, read, writes.__setitem__)
    except KeyError:
        return None
    if p < 2 and any(writes.get(key) != fields[p] for key, fields in carry.items()):
        return None
    return writes, defaults, result


def audit_headers():
    triples = list(product(range(3), repeat=3))
    truth = {t: honest(t) for t in triples}
    headers = set(truth.values())
    for bit, carry, old in list(headers):
        for i, (key, u, v) in enumerate(carry):
            headers.add((bit, carry[:i] + carry[i + 1:], old))
            for replacement in (None, 0, 1, 2, 3):
                for fields in ((key, replacement, v), (key, u, replacement)):
                    headers.add((bit, carry[:i] + (fields,) + carry[i + 1:], old))
        for i, (key, val) in enumerate(old):
            headers.add((bit, carry, old[:i] + old[i + 1:]))
            headers.add((bit, carry, old[:i] + ((key, (val + 1) % 3),) + old[i + 1:]))
    headers.update((1 - bit, carry, old) for bit, carry, old in list(headers))
    valid = false_if_unchecked = 0
    for header in headers:
        bit, records, stated = header
        carry, old = {k: (u, v) for k, u, v in records}, dict(stated)
        fragments = {(p, x): local(p, x, carry, old) for p in range(3) for x in range(3)}
        for triple in triples:
            pieces = [fragments[p, x] for p, x in enumerate(triple)]
            local_ok = all(part is not None for part in pieces) and pieces[2][2] == bit
            pair_ok = local_ok and all(
                pieces[j][1].isdisjoint(pieces[i][0]) for i, j in combinations(range(3), 2))
            if header == truth[triple]:
                assert pair_ok
            if pair_ok:
                assert bit == truth[triple][0]
                valid += 1
            if local_ok and bit != truth[triple][0]:
                false_if_unchecked += 1
    assert false_if_unchecked > 0
    return len(headers), len(headers) * len(triples), valid, false_if_unchecked


def audit_cylinders():
    # Enumerate all products of three pair predicates on one ternary AND term.
    capacities = [0, 0]
    for xy, yz, zx in product(range(16), repeat=3):
        signs = Counter()
        for x, y, z in product(range(2), repeat=3):
            if (xy >> (2*x+y)) & (yz >> (2*y+z)) & (zx >> (2*z+x)) & 1:
                signs[x*y*z] += 1
        for bit in (0, 1):
            if signs[1-bit] == 0:
                capacities[bit] = max(capacities[bit], signs[bit])
    assert capacities == [6, 1]
    return capacities


def audit_discovery_cuts():
    # The next address is data-dependent. A phase boundary is immediately
    # after a fresh load, before using its reply in the following computation.
    # The machine may halt before either cut. Its state fits in fixed registers.
    n = 6
    def step(state, read):
        pending, mask, index, accumulator = state
        if pending:
            if accumulator == 15 or mask == 0:
                return ("halt", accumulator & 1)
            remaining = [k for k in range(n) if mask >> k & 1]
            return (False, mask, remaining[accumulator % len(remaining)], accumulator)
        value = read(index)
        return (True, mask ^ (1 << index), index, ((accumulator << 1) ^ value) & 15)

    boot = (False, 63, 0, 7)
    partitions, halted_after = set(), Counter()
    for symbols in product(range(4), repeat=n):
        state = boot
        order, trace = [], [boot]
        while state[0] != "halt":
            if state[0] is False:
                order.append(state[2])
            state = step(state, symbols.__getitem__)
            trace.append(state)
        verdict = state
        halted_after[len(order)] += 1
        order.extend(sorted(set(range(n)).difference(order)))
        groups = [frozenset(order[k:k+2]) for k in (0, 2, 4)]
        partitions.add(tuple(groups))
        state, replay_trace = boot, [boot]
        for j, group in enumerate(groups):
            observed = set()
            while state[0] != "halt":
                def read(index):
                    assert index in group
                    observed.add(index)
                    return symbols[index]
                state = step(state, read)
                replay_trace.append(state)
                if j < 2 and len(observed) == 2:
                    break
        assert state == verdict and replay_trace == trace
    return len(partitions), dict(sorted(halted_after.items()))


if __name__ == "__main__":
    print("Physical files by verdict, lengths:", audit_files())
    print("Packed symbol round trips:", audit_packing())
    print("Rainbow range, Azuma exponent, per-vertex union factor:", audit_cuts())
    print("Mixed-width packet spellings, shifted fields:", audit_mixed_widths())
    print("Headers, header/file pairs, passing, false without pair checks:", audit_headers())
    print("One-term monochromatic cylinder capacities out of eight:", audit_cylinders())
    print("Adaptive partitions and halt histogram by discoveries:", audit_discovery_cuts())
    print("Finite fast path sizes (one 3-row tree and four paired trees):", replay())
    print("Cohort covered by the four paired trees:",
          sum(any(pair(f, a) for a in (4, 6, 8, 10)) for f in TARGETS))
