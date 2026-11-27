"""Round 8. Native paired writes, conflict-indexed repairs, and hidden-slot decoding."""
from collections import Counter
from functools import lru_cache
from itertools import product
from math import comb
from random import Random

from quadratic_read_repair_audit import Circuit, columns, evaluate, interval_gate, parsed, random_poly, solver
from nine_step_native_referee_audit import upper_and_truth


def layout(rows, slots):
    words = rows * slots + 10
    h = 1
    while 2**h < 32 * h * words + 2:
        h += 1
    bits = 32 * h * words
    assert (bits + 1).bit_length() == h
    return bits, 32 * h


def record(line, width):
    raw = line.encode('ascii')
    assert len(raw) < width // 8
    return raw.ljust(width // 8 - 1) + b'\n'


def serialize(slots, marks):
    bits, width = layout(len(marks), slots)
    anchors = [' '.join(str(-i if a & (1 << (i-1)) else i) for i in (1, 2, 3)) + ' 0'
               for a in range(1, 8)]
    public = [f'p cnf 5 {9 + slots * len(marks)}', *anchors, '4 1 2 0', '5 1 2 0']
    data = [f'{5 if y == mark else 4} 1 2 0' for mark in marks for y in range(slots)]
    file = b''.join(record(line, width) for line in public + data)
    assert len(file) * 8 == bits
    return file, width


def sat(file):
    v, clauses = parsed(file)
    return any(all(any(bool(a >> (abs(i)-1) & 1) == (i > 0) for i in c) for c in clauses)
               for a in range(1 << v))


# Register-indirect work stores at dst = 0 (dummy) or 1 (real).
# A public setup precedes ROW. Relative instruction clocks start at ROW.
ROW, LOOP = 0, 2
CODE = [
    ('store', 1, 1), ('add', 'y', 0, 0),
    ('input', 'word', 'p'), ('eq', 'dst', 'word', 'one'),
    ('eq', 'ok', 'word', 'zero'), ('or', 'ok', 'dst', 'ok'),
    ('bne', 'ok', 1, 'fallback'), ('store', 'dst', 0), ('store', 'dst', 1),
    ('add', 'p', 'p', 1), ('add', 'y', 'y', 1), ('blt', 'y', 'slots', LOOP),
    ('load', 'reply', 1), ('bne', 'reply', 1, 'fallback'),
    ('add', 'x', 'x', 1), ('blt', 'x', 'rows', ROW),
]


def execute(file, width, rows, slots):
    word_bytes = width // 8
    mask = (1 << width) - 1
    reg = dict(p=10, x=0, slots=slots, rows=rows,
               one=int.from_bytes(record('5 1 2 0', width), 'little'),
               zero=int.from_bytes(record('4 1 2 0', width), 'little'))
    def get(a):
        return a if isinstance(a, int) else reg[a]
    memory = [0, 1]  # global instruction zero stores 1 to real before the public setup
    time = pc = 0
    log = []
    while pc != len(CODE):
        op, dst, *args = CODE[pc]
        pc += 1
        if op in ('bne', 'blt'):
            a, target = args
            if (get(dst) != get(a) if op == 'bne' else get(dst) < get(a)):
                if target == 'fallback':
                    return False, time + 1, log
                pc = target
        elif op == 'input':
            addr = get(args[0]) * word_bytes
            assert addr + word_bytes <= len(file)
            reg[dst] = int.from_bytes(file[addr:addr + word_bytes], 'little')
        elif op == 'store':
            addr, value = get(dst), get(args[0])
            memory[addr] = value
            log.append((time, 'store', addr, value))
        elif op == 'load':
            addr = get(args[0])
            reg[dst] = memory[addr]
            log.append((time, 'read', addr, reg[dst]))
        else:
            a, b = map(get, args)
            if op == 'eq':
                value = int(a == b)
            elif op == 'or':
                value = a | b
            else:
                assert op == 'add'
                value = a + b
            reg[dst] = value & mask
        time += 1
    return True, time, log


def square_entry(file):
    """Semantic check of the uniform prefix recognizer, before the timed sweep."""
    bits = 8 * len(file)
    width = 32 * (bits+1).bit_length()
    if bits % width:
        return False
    side = 1
    while width*(side*side + 10) < bits:
        side *= 2
    if width*(side*side + 10) != bits:
        return False
    lines = [f'p cnf 5 {side*side+9}']
    for i in range(1, 8):
        clause = [(-j if (i >> (j-1)) & 1 else j) for j in (1, 2, 3)]
        lines.append(' '.join(map(str, [*clause, 0])))
    lines += ['4 1 2 0', '5 1 2 0']
    prefix = b''.join(record(line, width) for line in lines)
    if not file.startswith(prefix):
        return False
    return execute(file, width, side, side)[0]


def check_native():
    rng = Random(8008)
    counts = Counter()
    for rows, slots in [(2, 2), (3, 4), (4, 4), (8, 8)]:
        layouts = (product(range(slots), repeat=rows) if rows <= 4 else
                   (tuple(rng.randrange(slots) for _ in range(rows)) for _ in range(20)))
        for marks in layouts:
            file, width = serialize(slots, marks)
            assert sat(file)
            accepted, time, log = execute(file, width, rows, slots)
            assert accepted and time == rows * (6 + 10 * slots)
            if rows == slots:
                assert square_entry(file)
                forged = file.replace(b'4 1 2 0', b'3 1 2 0', 1)
                assert not square_entry(forged) and not sat(forged)
                counts['square entry and forged prefix pairs'] += 1
            counts['positive files'] += 1
            counts['native sweep instructions'] += time
            by_time = {t: (op, addr, b) for t, op, addr, b in log}
            for x, mark in enumerate(marks):
                start = x * (6 + 10 * slots)
                c = start + 2 + 10 * slots
                assert by_time[c] == ('read', 1, 1)
                conflicts = [t for t in by_time if t < c and by_time[t] == ('store', 1, 0)]
                assert all(t + 1 < c and by_time[t+1] == ('store', 1, 1) for t in conflicts)
                last_conflict = max(conflicts)
                assert last_conflict == start + 7 + 10 * mark
                real = {t for t in by_time if t < c and by_time[t] == ('store', 1, 1)}
                assert {t for t in real if last_conflict < t} == {last_conflict + 1}
                # The minimal and maximal legal offers have identical suffix cuts.
                for offers in [{last_conflict + 1}, real]:
                    for y in range(slots):
                        lo = start + 7 + 10 * y
                        assert any(lo < u < c for u in offers) == (mark >= y)
                        counts['suffix tests'] += 1
                counts['true row reads'] += 1
            edits = range(rows * slots) if rows <= 3 else [rng.randrange(rows * slots)]
            for edit in edits:
                wbytes = width // 8
                start = (10 + edit) * wbytes
                bad = file[:start] + record('3 1 2 0', width) + file[start + wbytes:]
                fast, _, _ = execute(bad, width, rows, slots)
                assert not fast and not sat(bad)
                counts['negative word edits'] += 1
    print('Native and DIMACS:', dict(counts))


def truth_defect(stores, claim, response):
    for j, row in enumerate([('initial', 1, 0)] + stores, -1):
        op, addr, b = row
        if op not in ('initial', 'store') or addr != 1 or b == claim:
            continue
        u = response[j + 1]
        if not j < u < len(stores) or stores[u] != ('store', 1, claim):
            return True
    return False


def memory_query(stores, claim, response):
    # Only the conflict index is existential. A malicious response can point
    # out of bounds, to the wrong address, or to an actual non-store.
    nbits = len(stores).bit_length()
    circ = Circuit(nbits)
    sels = [circ.all(4+k if code >> k & 1 else -(4+k) for k in range(nbits))
            for code in range(len(stores)+1)]
    bad = []
    # Build the row lookup for the proposed time symbolically from the selected j.
    # Encode times u by u+1, reserving zero for the initializer.
    u_bits = (len(stores)+1).bit_length()
    times = [circ.any(s for s, t in zip(sels, response) if (t+1) >> k & 1)
             for k in range(u_bits)]
    is_time = [circ.all(a if (u+1) >> k & 1 else -a for k, a in enumerate(times))
               for u in range(len(stores))]
    good_store = circ.any(wire for wire, row in zip(is_time, stores)
                          if row == ('store', 1, claim))
    for code, sel in enumerate(sels):
        j = code - 1
        is_conflict = (claim != 0 if j < 0 else stores[j] == ('store', 1, 1-claim))
        if is_conflict:
            later = circ.any(is_time[j+1:])
            bad.append(circ.all([sel, -circ.all([later, good_store])]))
    out = circ.any(bad)
    file = circ.dimacs(out)
    g = len(circ.gates) + 1
    variables = 3 + nbits + g
    clauses = 8 * g + 8
    digits = len(str(variables))
    assert len(file) == 8 + digits + len(str(clauses)) + clauses*(3*digits+8)
    return file


def check_bad_histories():
    events = [('idle', 0, 0)] + [('store', a, b) for a, b in product(range(2), repeat=2)]
    n = 3
    counts = Counter()
    rng = Random(808)
    solve = solver()
    sizes = []
    for stores in product(events, repeat=n):
        actual = next((b for op, a, b in reversed(stores) if op == 'store' and a == 1), 0)
        for claim in (0, 1):
            found = False
            for response in product(range(-1, n+1), repeat=n+1):
                defect = truth_defect(list(stores), claim, response)
                found |= not defect
                if not defect:
                    assert claim == actual
                counts['challenge maps'] += 1
            assert found == (claim == actual)
            # Include genuine witnesses, forged in-range and out-of-range replies.
            last = max((i for i, row in enumerate(stores) if row == ('store', 1, claim)), default=-1)
            for response in [(last,)*(n+1), tuple(rng.randrange(-1, n+1) for _ in range(n+1))]:
                file = memory_query(stores, claim, response)
                v, clauses = parsed(file)
                answer = solve(clauses, v)
                assert answer == truth_defect(list(stores), claim, response)
                counts['DIMACS defects SAT' if answer else 'DIMACS defects UNSAT'] += 1
                sizes.append(8*len(file))
    print('Adversarial histories:', dict(counts), 'physical bit range', min(sizes), max(sizes))


@lru_cache(None)
def optimal_coverage(remaining, budget):
    # Each leaf can correctly output one full placement. An arbitrary probe
    # splits one unresolved row into one fixed choice vs b-1 residual choices.
    if not budget or not remaining:
        return 1
    best = 1
    for i, choices in enumerate(remaining):
        siblings = remaining[:i] + remaining[i+1:]
        no = tuple(sorted(siblings + ((choices-1,) if choices > 2 else ())))
        best = max(best, optimal_coverage(siblings, budget-1) +
                   optimal_coverage(no, budget-1))
    return best


def rank_volume(rows, slots, budget):
    """Number of tuples of misses in [0, slots-1] with sum at most budget."""
    return sum((-1)**k * comb(rows, k) * comb(budget-k*slots + rows, rows)
               for k in range(min(rows, budget//slots)+1))


def rank_replay(marks, slots):
    # A completing probe order that depends on earlier replies across rows.
    # Count misses before each first hit, even when a different row intervenes.
    rows = len(marks)
    unseen = [list(range(slots)) for _ in range(rows)]
    misses = [0] * rows
    hit = [False] * rows
    state = 17
    while not all(hit):
        active = [x for x in range(rows) if not hit[x]]
        x = active[state % len(active)]
        y = unseen[x].pop((state // 3) % len(unseen[x]))
        hit[x] = (y == marks[x])
        misses[x] += int(not hit[x])
        state = (3*state + 7*x + 11*y + hit[x]) % 997
    return tuple(misses)


def check_counts():
    tests = 0
    for rows, slots in product(range(1, 6), range(2, 8)):
        for cap in range(rows*(slots-1)+1):
            value = optimal_coverage((slots,)*rows, cap)
            assert value <= min(slots**rows, comb(cap+rows, rows))
            assert value <= sum(comb(cap,k) for k in range(min(cap, rows)+1))
            assert value <= rank_volume(rows, slots, cap)
            if cap == rows*(slots-1):
                assert value == slots**rows
            tests += 1
    print('Optimal adaptive-decision-tree checks:', tests)
    print('Three rows, four slots, Q=0..9:',
          [optimal_coverage((4,4,4), q) for q in range(10)])
    for rows, slots in [(3, 4), (4, 5), (4, 8)]:
        ranks = set()
        worst = 0
        for marks in product(range(slots), repeat=rows):
            ranks.add(rank_replay(marks, slots))
            forward = sum(min(slots-1, y+1) for y in marks)
            reverse = sum(min(slots-1, slots-y) for y in marks)
            worst = max(worst, min(forward, reverse))
        assert len(ranks) == slots**rows
        assert worst <= rows*(slots+1)//2
        print('Rank bijection and one-advice-bit scan:', rows, slots, len(ranks), worst)
    rows = slots = 256
    q = 3
    cap = rows * q
    transcript_count = sum(comb(cap, k) for k in range(rows+1))
    min_advice = (slots**rows - 1).bit_length() - (transcript_count.bit_length()-1)
    assert (1 << (min_advice - 1))*transcript_count < slots**rows <= (1 << min_advice)*transcript_count
    bits, width = layout(rows, slots)
    rng = Random(8256)
    marks = [rng.randrange(slots) for _ in range(rows)]
    file, native_width = serialize(slots, marks)
    assert native_width == width and len(file)*8 == bits and sat(file)
    ok, elapsed, log = execute(file, width, rows, slots)
    stride = 6+10*slots
    assert ok and elapsed == rows*stride
    assert [t for t, op, a, b in log if (op, a, b) == ('store', 1, 0)] == [
        row*stride + 7 + 10*mark for row, mark in enumerate(marks)]
    assert sum(op == 'read' for _, op, _, _ in log) == rows
    print('256-square, q=3: advice lower', min_advice, 'upper', 6*rows,
          'file bits', len(file)*8, 'word bits', width, 'sweep', elapsed)


def check_packed_contrast():
    truth = upper_and_truth()
    chosen = 0
    for p, q, m, n in product((1, 2, 4, 8), repeat=4):
        code = p << 12 | q << 8 | m << 4 | n
        assert bool(truth[code]) == (p != m and q != n)
        chosen += bool(truth[code])
    assert chosen == 144
    print('Selector census with four one-hot nibbles:', chosen, 'SAT / 256')


def check_latest_circuit():
    # Compose the actual round-7 interval gates to extract a single latest offer.
    # Each piece is (quadratic coordinate polynomials, affine domain equations).
    rng = Random(8007)
    small = [{m for m in range(4) if a >> m & 1} for a in range(16)]
    maps = [(2, [([p, q], [])]) for p, q in product(small, repeat=2)]
    for _ in range(32):
        maps.append((3, [([random_poly(rng, 3), random_poly(rng, 3)],
                          [random_poly(rng, 3, True)]) for _ in range(2)]))
    tests = nonempty = 0
    for n, pieces in maps:
        circ = Circuit(n+2)
        addr = [4, 5]
        cutoff = list(range(6, 6+n))
        def hit(lower):
            return circ.any(interval_gate(circ, n, coords, domain, addr, lower, cutoff)
                            for coords, domain in pieces)
        exists = hit(None)
        bits = [1]*n  # wire 1 is the pinned constant false
        for k in reversed(range(n)):
            lower = [-1]*k + [1] + bits[k+1:]  # candidate - 1
            bits[k] = hit(lower)
        lanes = 1 << (n+2)
        values = [circ.packed(wire, columns(n+2), lanes) for wire in [exists, *bits]]
        for x in range(lanes):
            rhs, c = x & 3, x >> 2
            offers = [u for u in range(c) if any(
                not any(evaluate(row, u) for row in domain) and
                sum(evaluate(row, u) << k for k, row in enumerate(coords)) == rhs
                for coords, domain in pieces)]
            assert ((values[0] >> x) & 1) == bool(offers)
            latest = sum(((value >> x) & 1) << k for k, value in enumerate(values[1:]))
            assert latest == max(offers, default=0)
            tests += 1
            nonempty += bool(offers)
    print('Latest-offer circuit compositions:', len(maps), 'maps,', tests,
          'queries,', nonempty, 'nonempty')


if __name__ == '__main__':
    check_native()
    check_bad_histories()
    check_counts()
    check_latest_circuit()
    check_packed_contrast()
