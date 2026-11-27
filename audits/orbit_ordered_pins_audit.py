"""Check a proper DIMACS equality layout and crossed writes on arbitrary cycles."""

from itertools import combinations, permutations, product
from math import comb, factorial, isqrt
from random import Random


def make_file(k, width, occurrences):
    """An occurrence is (zero-based private variable number, Boolean sign)."""
    assert len(occurrences) == 2 * k and width >= 3
    bits = (k + 3).bit_length()

    def suffix(number):
        return ''.join('0' * (width - 1) + bit for bit in f'{number:0{bits}b}')

    def literal(number, positive):
        sign = ' ' if positive else '-'
        return ' ' * (width - 2) + sign + '1' + suffix(number)

    # Exclude each nonzero assignment to the three dummies by one clause.
    dummies = (k + 1, k + 2, k + 3)
    fixed_clauses = [
        tuple((name, not (forbidden >> j & 1)) for j, name in enumerate(dummies))
        for forbidden in range(1, 8)
    ]
    largest_name = '1' + suffix(2**bits - 1)
    header = f'p cnf {largest_name} {7 + 2*k}\n'
    data = [header + ' ' * (-len(header) % width)]
    word_index = len(data[0]) // width
    sign_positions = []
    clauses = fixed_clauses + [
        ((number + 1, sign), (dummies[0], True), (dummies[1], True))
        for number, sign in occurrences
    ]
    for i, clause in enumerate(clauses):
        if i >= len(fixed_clauses):
            sign_positions.append(word_index)
        row = ''.join(literal(name, sign) for name, sign in clause) + ' 0\n'
        row += ' ' * (-len(row) % width)
        data.append(row)
        word_index += len(row) // width
    result = ''.join(data)
    # Keep the aligned sign slots and terminate the physical file with a newline.
    return result + ' ' * (width - 1) + '\n', sign_positions


def satisfying_assignment_count(file):
    """Parse the ASCII independently and evaluate every assignment in parallel."""
    fields = file.split()
    assert fields[:2] == ['p', 'cnf']
    limit, count = map(int, fields[2:4])
    assert len(fields) == 4 + 4 * count
    clauses = []
    for offset in range(4, len(fields), 4):
        a, b, c, zero = map(int, fields[offset:offset + 4])
        assert zero == 0 and len({abs(a), abs(b), abs(c)}) == 3
        assert all(1 <= abs(lit) <= limit for lit in (a, b, c))
        clauses.append((a, b, c))
    names = sorted({abs(lit) for clause in clauses for lit in clause})
    assignments = range(1 << len(names))
    full = (1 << len(assignments)) - 1
    truth = {}
    for bit, name in enumerate(names):
        positive = sum(1 << value for value in assignments if value >> bit & 1)
        truth[name], truth[-name] = positive, full ^ positive
    result = full
    for a, b, c in clauses:
        result &= truth[a] | truth[b] | truth[c]
    return result.bit_count()


def packed(file, width):
    assert len(file) % width == 0
    return [int.from_bytes(file[i:i + width].encode(), 'little')
            for i in range(0, len(file), width)]


def check_layout(k, width, sign_order, cases):
    template, positions = make_file(k, width, [(0, True)] * (2 * k))
    reference = packed(template, width)
    maximum_alphabet = 0
    for alice, bob in cases:
        occurrences = [None] * (2 * k)
        for bit, (left, right) in enumerate(zip(sign_order[:k], sign_order[k:])):
            occurrences[left] = bit, bool(alice >> bit & 1)
            occurrences[right] = bit, bool(bob >> bit & 1)
        file, aligned = make_file(k, width, occurrences)
        assert positions == aligned
        assert satisfying_assignment_count(file) == int(alice == bob)
        words = packed(file, width)
        maximum_alphabet = max(maximum_alphabet, len(set(words) | {0}))
        # Changing a sign, with the public pairing fixed, affects only its owner's
        # first-literal sign word. This checks party-local initialization.
        for position, (_, sign) in zip(aligned, occurrences):
            assert (words[position] == reference[position]) == sign
        public, _ = make_file(k, width, [(number, True) for number, _ in occurrences])
        public_words = packed(public, width)
        changed = {i for i, (a, b) in enumerate(zip(words, public_words)) if a != b}
        assert changed == {i for i, (_, sign) in zip(positions, occurrences) if not sign}
    return maximum_alphabet


def crossed_read(memory, address, state, turn, orbit, radius):
    value = memory.get(address, 0)
    state = (19 * state + value + address + turn) % 257
    offset = state % (radius + 2) - 1
    payload = None if offset < 0 else orbit[(turn + offset) % len(orbit)]
    return state, value, payload


def check_missing(k, width, rng):
    order = list(range(2*k))
    rng.shuffle(order)
    base_occurrences = [(0, True)] * (2*k)
    for bit in range(k):
        base_occurrences[order[bit]] = base_occurrences[order[k + bit]] = bit, True
    base, positions = make_file(k, width, base_occurrences)
    baseline = packed(base, width)
    assert satisfying_assignment_count(base) == 1
    for hole, (number, _) in enumerate(base_occurrences):
        edited = base_occurrences[:]
        edited[hole] = number, False
        other, same = make_file(k, width, edited)
        assert same == positions and satisfying_assignment_count(other) == 0
        altered = packed(other, width)
        assert [i for i in range(len(altered)) if baseline[i] != altered[i]] == [same[hole]]
        orbit = [i for i in range(len(altered)) if i != same[hole]]
        rng.shuffle(orbit)
        memories = [dict(enumerate(words)) for words in (baseline, altered)]
        state = 0
        for turn in range(2 * len(orbit)):
            address = orbit[turn % len(orbit)]
            left, right = [crossed_read(mem, address, state, turn, orbit, 3) for mem in memories]
            assert left == right
            state, target, payload = left
            if payload is not None:
                for mem in memories:
                    mem[target] = payload
    return len(positions)


def check_batched_cycle(initial, orbit, cut, turns, radius):
    """Compare a central run with two local memories and last-write batching."""
    alice = set(orbit[:cut])
    banks = [{i: x for i, x in enumerate(initial) if (i in alice) == own}
             for own in (False, True)]
    central = dict(enumerate(initial))
    state = verifier = 7
    pending = {}
    transmissions = 0
    events = 0
    who = orbit[0] in alice
    for turn in range(turns):
        address = orbit[turn % len(orbit)]
        new_owner = address in alice
        if new_owner != who:
            banks[new_owner].update(pending)
            transmissions += len(pending)
            pending.clear()
            who = new_owner
        verifier, actual, written = crossed_read(central, address, verifier, turn, orbit, radius)
        state, target, payload = crossed_read(banks[who], address, state, turn, orbit, radius)
        assert (verifier, actual, written) == (state, target, payload)
        if written is not None:
            central[actual] = written
            if (target in alice) == who:
                banks[who][target] = payload
            else:
                pending[target] = payload
                events += 1
    transmissions += len(pending)
    banks[not who].update(pending)
    assert all(banks[address in alice][address] == value for address, value in central.items())
    passes = (turns + len(orbit) - 1) // len(orbit)
    halo = radius * passes
    envelope = (halo + 1) * len(set(initial))
    assert transmissions <= (2 * passes + 1) * (4 * (halo + 1) + envelope) + passes * envelope
    return transmissions, events


def matchings(vertices):
    if not vertices:
        yield ()
        return
    first, rest = vertices[0], vertices[1:]
    for index, mate in enumerate(rest):
        edge = (1 << first) | (1 << mate)
        for remaining in matchings(rest[:index] + rest[index + 1:]):
            yield (edge,) + remaining


def crossing_histogram(k):
    # Fix k labeled pairs and choose a balanced side of the cut uniformly.
    # j split edges, then (k-j)/2 whole edges on this side, then j orientations.
    return [comb(k, j) * comb(k-j, (k-j)//2) * 2**j if (k-j) % 2 == 0 else 0
            for j in range(k + 1)]


def check_matching_menus():
    cuts_checked = menus_checked = 0
    rng = Random(462253)
    for k in range(1, 6):
        pairing = list(matchings(tuple(range(2 * k))))
        count = factorial(2*k) // (2**k * factorial(k))
        assert len(set(pairing)) == count
        expected = crossing_histogram(k)
        total_cuts = comb(2 * k, k)
        assert sum(expected) == total_cuts
        poor_by_cut = []
        for left in combinations(range(2*k), k):
            if left[0] != 0:  # complementary cuts have the same crossings
                continue
            mask = sum(1 << vertex for vertex in left)
            observed = [0] * (k + 1)
            poor = set()
            for index, matching in enumerate(pairing):
                cross = sum((mask & edge).bit_count() == 1 for edge in matching)
                observed[cross] += 1
                if 4 * cross < k:
                    poor.add(index)
            assert all(observed[j] * total_cuts == expected[j] * count for j in range(k + 1))
            poor_by_cut.append(poor)
            cuts_checked += 1
        order = list(range(len(poor_by_cut)))
        for _ in range(24):
            rng.shuffle(order)
            bad = set()
            for size, index in enumerate(order, 1):
                bad.update(poor_by_cut[index])
                promised_good = count - size * len(poor_by_cut[index])
                if promised_good > 0:
                    assert count - len(bad) >= promised_good
                    menus_checked += 1
    for k in range(1, 129):
        counts = crossing_histogram(k)
        threshold = (k - 1) // 4
        tail = sum(counts[:threshold + 1])
        binomial_tail = sum(comb(k, j) for j in range(threshold + 1))
        assert sum(counts) == comb(2*k, k)
        assert tail <= 2**k * binomial_tail
        # The entropy bound used here can be tested without rounding a logarithm:
        # sum_{j<=k/4} C(k,j) <= (4 / 3^(3/4))^k.
        assert binomial_tail**4 * 3**(3*k) <= 4**(4*k)
    return cuts_checked, menus_checked


def check_dense_guards():
    # Dummy 1 is true, 2 and 3 false. Changing ' 1' into '-1' in any
    # repeated guard kills the same sole satisfying assignment.
    required = (True, False, False)
    exclusions = []
    for forbidden in product((False, True), repeat=3):
        if forbidden != required:
            fields = [str(-j if bit else j) for j, bit in enumerate(forbidden, 1)]
            exclusions.append(' '.join(fields) + ' 0\n')
    forcing = ''.join(exclusions)
    guard = ' 1 2 3 0\n'
    tested = 0
    for budget in (256, 1024, 3072):
        def body(count):
            return f'p cnf 3 {count+7}\n' + forcing + guard * count

        count = (budget - len(body(0))) // len(guard)
        while len(body(count)) > budget:
            count -= 1
        assert len(body(count + 1)) > budget
        base = body(count)
        base += (' ' * (budget-len(base)-1) + '\n') if len(base) < budget else ''
        assert len(base) == budget and satisfying_assignment_count(base) == 1
        first = len(body(count)) - len(guard) * count
        for width in (4, 8, 16, 32):
            sensitive = {}
            for address in range(first, first + count * len(guard), len(guard)):
                sensitive[address // width] = address
            if width >= len(guard):
                interior = range((first + width - 1) // width,
                                 (first + count * len(guard)) // width)
                assert all(word in sensitive for word in interior)
            for word, offset in sensitive.items():
                edit = base[:offset] + '-' + base[offset+1:]
                assert satisfying_assignment_count(edit) == 0
                before, after = packed(base, width), packed(edit, width)
                assert [i for i, (a,b) in enumerate(zip(before, after)) if a != b] == [word]
                tested += 1
    return tested


def parity_codeword(vertices, edges, vertex_bits):
    """Bits 0..v-1 pin vertices, the remaining bits pin edge differences."""
    word = vertex_bits
    for j, (u, v) in enumerate(edges):
        difference = ((vertex_bits >> u) ^ (vertex_bits >> v)) & 1
        word |= difference << (vertices + j)
    return word


def boundary_syndrome(edge_rows, word):
    return sum(((word & row).bit_count() % 2) << j for j, row in enumerate(edge_rows))


def max_cut_matching(edges):
    if not edges:
        return 0
    (u, v), *rest = edges
    disjoint = [e for e in rest if u not in e and v not in e]
    return max(1 + max_cut_matching(disjoint), max_cut_matching(rest))


def check_parity_rectangles():
    # A single graph is fixed while both the vertex cut and the ownership
    # of every edge pin change. Equal syndromes permit exactly the same
    # mixed accepting pairs, giving the maximal accepting rectangles.
    graphs = [
        (4, list(combinations(range(4), 2))),
        (6, [(i, (i + 1) % 6) for i in range(6)]),
    ]
    total, mixed = 0, 0
    for vertices, edges in graphs:
        words = [parity_codeword(vertices, edges, assignment) for assignment in range(2**vertices)]
        assert len(set(words)) == len(words)
        valid = set(words)
        rows = [(1 << u) | (1 << v) | (1 << (vertices + j)) for j, (u, v) in enumerate(edges)]
        assert all(boundary_syndrome(rows, word) == 0 for word in words)
        for side in combinations(range(vertices), vertices//2):
            vertex_mask = sum(1 << i for i in side)
            crossing = [(a, b) for a, b in edges if (a in side) != (b in side)]
            matching = max_cut_matching(crossing)
            for edge_mask in range(2**len(edges)):
                mask = vertex_mask | (edge_mask << vertices)
                groups = {}
                for code in words:
                    tag = boundary_syndrome(rows, code & mask)
                    groups.setdefault(tag, set()).add(code)
                assert len(groups) >= 2**matching
                # The linear map gives equally sized fibers. Each accepting
                # rectangle is contained in one fiber, which itself is a rectangle.
                assert all(len(group) * len(groups) == len(words) for group in groups.values())
                assert all(len({word & mask for word in group}) *
                           len({word & ~mask for word in group}) == len(group)
                           for group in groups.values())
                for group in groups.values():
                    representative = next(iter(group))
                    for code in words:
                        crossed = (representative & mask) | (code & ~mask)
                        assert (crossed in valid) == (code in group)
                        mixed += 1
                total += 1
    return total, mixed


def check_parity_dimacs():
    vertices, edges = 3, [(0, 1), (0, 2), (1, 2)]
    count = vertices + len(edges)
    dummies = (count + 1, count + 2, count + 3)
    public = []
    for forbidden in range(1, 8):
        public.append([(-v if forbidden >> i & 1 else v) for i, v in enumerate(dummies)])
    for j, (u, v) in enumerate(edges):
        triple = (u + 1, v + 1, vertices + j + 1)
        for forbidden in range(8):
            if forbidden.bit_count() % 2:
                public.append([(-v if forbidden >> i & 1 else v) for i, v in enumerate(triple)])
    valid = {parity_codeword(vertices, edges, assignment) for assignment in range(2**vertices)}
    for word in range(2**count):
        pins = [[i+1 if word >> i & 1 else -(i+1), dummies[0], dummies[1]] for i in range(count)]
        clauses = public + pins
        file = f'p cnf {dummies[-1]} {len(clauses)}\n' + ''.join(
            ' '.join(map(str, row)) + ' 0\n' for row in clauses)
        assert satisfying_assignment_count(file) == int(word in valid)
    return 2**count


def check_travel_trace(rng, arc_mode, bit_payload):
    domain = 1 << rng.randrange(3, 7)
    period = domain if bit_payload else rng.randrange(4, domain + 1)
    orbit = list(range(domain)) if bit_payload else rng.sample(range(domain), period)
    rank = {address: i for i, address in enumerate(orbit)}
    palette = rng.sample(range(domain), rng.randrange(1, min(6, domain)))
    initial = [rng.choice(palette) for _ in range(domain)]
    radius = 1 if bit_payload else rng.randrange(4)
    marked_count = 2 * rng.randrange(1, period // 2 + 1)
    marks = sorted(rng.sample(range(period), marked_count))
    cuts = []
    for j, start in enumerate(marks):
        end = marks[(j + marked_count // 2) % marked_count]
        length = (end - start) % period
        cuts.append({orbit[(start + i) % period] for i in range(length)})

    def distance(a, b):
        if a not in rank or b not in rank:
            return float('inf')
        diff = abs(rank[a] - rank[b])
        return min(diff, period - diff)

    def neighbor(a, d):
        return orbit[(rank[a] + d) % period] if a in rank else a

    memory = initial[:]
    events = []
    head = rng.randrange(period)
    direction = rng.choice((-1, 1))
    arcs = 1
    read_count = rng.randrange(1, 4 * period)
    for turn in range(read_count):
        p = orbit[head]
        x = memory[p]
        delta = rng.randrange(-radius, radius + 1)
        y = (p ^ (x & 1)) if bit_payload else neighbor(p, delta)
        written = y if (x + turn) % 5 else None
        if written is not None:
            memory[x] = written
        events.append((p, x, written))
        if turn + 1 == read_count:
            break
        if arc_mode and rng.randrange(7):
            head = (head + direction) % period
        else:
            head = (p + 13*x + rng.randrange(period)) % period
            direction = -direction
            arcs += 1
    travel = sum(distance(a[0], b[0]) for a, b in zip(events, events[1:]))
    threshold = max(1, isqrt(travel))
    span = radius * (1 + travel // threshold)
    wide = threshold + radius + 2 * radius * (travel // threshold)
    roots = {neighbor(h, d) for h in set(initial) for d in range(-span, span + 1)}
    bit_roots = {u for h in set(initial) for u in (h,h ^ 1)}
    if arc_mode:
        blocks = arcs + (2 * len(events) + period - 1) // period
        arc_roots = {neighbor(h, d) for h in set(initial)
                     for d in range(-radius * blocks, radius * blocks + 1)}
    for p, x, _ in events:
        assert p in roots or x in roots or distance(p, x) <= wide
        if arc_mode:
            assert p in arc_roots or x in arc_roots or distance(p, x) <= 2*radius*(blocks+1)
        if bit_payload:
            assert p in bit_roots or x in bit_roots
    switches = 0
    for left in cuts:
        turns = 0
        bank = events[0][0] in left
        destinations = set()

        def finish_phase():
            assert len(destinations) <= 2*len(roots) + 4*(wide+1) + 4*(radius+1)
            if bit_payload:
                assert len(destinations) <= 2*len(bit_roots) + 8

        for p, x, written in events:
            if (p in left) != bank:
                finish_phase()
                turns += 1
                destinations.clear()
                bank = not bank
            if written is not None and (x in left) != bank:
                destinations.add(x)
        finish_phase()
        switches += turns
    assert switches <= 2*travel


def main():
    rng = Random(19370419)
    files = holes = maximum = orders = 0
    for k in range(1, 5):
        width = 4 if k % 2 else 6
        size = 2*k
        schedules = (permutations(range(size)) if k <= 2 else
                     [rng.sample(range(size), size) for _ in range(8)])
        for order in schedules:
            cases = list(product(range(2**k), repeat=2))
            maximum = max(maximum, check_layout(k, width, order, cases))
            orders += 1
            files += len(cases)
        holes += check_missing(k, width, rng)
    assert maximum <= 15
    records = events = 0
    for _ in range(1000):
        domain = 1 << rng.randrange(3, 7)
        period = rng.randrange(2, domain + 1)
        orbit = rng.sample(range(domain), period)
        palette = rng.sample(range(domain), rng.randrange(1, min(6, domain)))
        initial = [rng.choice(palette) for _ in range(domain)]
        count, writes = check_batched_cycle(initial, orbit, rng.randrange(1, period),
                                            rng.randrange(1, 8 * period), rng.randrange(6))
        records += count
        events += writes
    assert 0 < records < events
    cuts, menus = check_matching_menus()
    guards = check_dense_guards()
    owner_splits, mixed = check_parity_rectangles()
    parity_files = check_parity_dimacs()
    for arc_mode, bit_payload in product((False, True), repeat=2):
        for _ in range(300):
            check_travel_trace(rng, arc_mode, bit_payload)
    print(f'{files} DIMACS equality files, {orders} sign orders, {holes} omitted-sign pairs')
    print(f'Largest input alphabet including zero: {maximum} word values')
    print(f'1000 arbitrary orbits: {events} remote writes batched into {records} records')
    print(f'Crossing law verified on {cuts} balanced cuts; {menus} finite-menu bounds checked')
    print(f'{guards} single-word DIMACS guard edits, each changing SAT to UNSAT')
    print(f'{owner_splits} graph-code owner splits, {mixed} mixed pairs checked')
    print(f'{parity_files} proper DIMACS pinned parity files checked')
    print('1200 adaptive traces checked for travel, arc ancestry and ownership charges')


if __name__ == '__main__':
    main()
