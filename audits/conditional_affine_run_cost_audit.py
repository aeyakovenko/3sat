"""Finite checks for the positive-run affine partition bound. Run from any directory."""
from collections import Counter
from itertools import combinations, product
from math import comb
import hamming_verdict_projection_audit as journal
from nine_step_native_referee_audit import upper_and_truth


def span(basis):
    points = [0]
    for v in basis:
        points += [p ^ v for p in points]
    return points


def parameterization(words):
    """Ascending independent generators; coefficient bit i multiplies generator i."""
    points = [0]
    seen = {0}
    for word in sorted(words):
        if word not in seen:
            extra = [p ^ word for p in points]
            points.extend(extra)
            seen.update(extra)
    assert seen == set(words)
    return points


def quadratic_ok(parameters, dimension):
    pairs = (dimension - 1) // 2
    mask = (1 << pairs) - 1
    x = parameters & mask
    y = (parameters >> pairs) & mask
    z = (parameters >> (2 * pairs)) & 1
    return (x & y).bit_count() % 2 == z


def linear_ok(parameters, dimension):
    return not (parameters >> (2 * ((dimension - 1) // 2)) & 1)


def flats(dimension):
    """Every binary affine flat, once, via reduced row echelon form and a coset leader."""
    for rank in range(dimension + 1):
        for pivots in combinations(range(dimension), rank):
            free = [i for i in range(dimension) if i not in pivots]
            options = [[(1 << pivot) | tail for tail in span([1 << i for i in free if i > pivot])]
                       for pivot in pivots]
            offsets = span([1 << i for i in free])
            for rows in product(*options):
                linear = span(rows)
                for offset in offsets:
                    yield sum(1 << (offset ^ x) for x in linear)


def largest_flat(points):
    def through_zero(allowed, space, previous):
        best = len(space)
        for v in allowed:
            if v.bit_length() <= previous:
                continue
            coset = [v ^ x for x in space]
            if min(coset) == v and all(x in allowed for x in coset):
                best = max(best, through_zero(allowed, space + coset, v.bit_length()))
        return best

    return max(through_zero({x ^ base for x in points}, [0], 0) for base in points)


def code_checks():
    for t in range(4, 14):
        greedy = journal.greedy_words(t)
        parametrized = parameterization(greedy)
        assert sorted(parametrized) == greedy
    for t in (7, 14):
        allowed = journal.accepted_table('H', t)
        assert len(parameterization(allowed)) == 16 ** (t // 7)

    for t, copies in [(7, 1), (9, 1), (7, 2)]:
        code = parameterization(journal.greedy_words(t))
        r = len(code).bit_length() - 1
        accept = sum(1 << p for p in range(1 << (r * copies))
                     if all(quadratic_ok(p >> (i * r), r) for i in range(copies)))
        assert accept.bit_count() == 1 << ((r - 1) * copies)
        if copies == 1:
            domains = list(flats(r))
            largest = max(h.bit_count() for h in domains if not h & ~accept)
            parities = [mask_where(1 << r, lambda x: ((x & a).bit_count() ^ b) & 1)
                        for a, b in product(range(1 << r), range(2))]
            output_flats = [h for h in domains if any(not h & (accept ^ p) for p in parities)]
            optimal = 1 << (r - (r - 1) // 2)
            assert max(h.bit_count() for h in output_flats) == optimal
            assert all(any(h.bit_count() == optimal and (h >> base) & 1 for h in output_flats)
                       for base in range(1 << r))
        else:
            largest = largest_flat({i for i in range(1 << (r * copies)) if accept >> i & 1})
        predicted = 1 << (copies * (r - (r - 1) // 2 - 1))
        assert largest == predicted
        print(f't={t}, k={copies}, outer dimension={r}, positives={accept.bit_count()}, '
              f'largest accepting flat={largest}')


def make_layout(k, mode):
    # These shortened fixtures fix t=7 so both physical tables can be materialized.
    template = journal.layout('H', k)
    points = parameterization(journal.greedy_words(7))
    check = quadratic_ok if mode == 'Q' else linear_ok
    good = {s for i, s in enumerate(points) if check(i, 4)}
    lines = template.prefix.splitlines(keepends=True)
    lines[0] = lines[0].replace(b' H ', b' ' + mode.encode() + b' ')
    for s, flag in enumerate(template.flags):
        lines[10 + s] = journal.clause(flag if s in good else -flag, 1, 2)
    return journal.Layout(mode, k, 7, 3, b''.join(lines), template.flags, good), points


def packed_scan(raw, layout):
    if not raw.startswith(layout.prefix):
        raise ValueError('unrecognized prefix')
    stream = raw[len(layout.prefix):]
    stride = layout.digits + 8
    assert len(stream) == stride * layout.k
    dictionary = {journal.clause(flag, 1, 2): (s in layout.good)
                  for s, flag in enumerate(layout.flags)}
    return all(dictionary[stream[i:i + stride]] for i in range(0, len(stream), stride))


def file_checks():
    checked = positive = 0
    for k in (1, 2):
        sizes = set()
        for mode in ('L', 'Q'):
            layout, outer = make_layout(k, mode)
            last = layout.flags[-1]
            head = layout.prefix.splitlines(keepends=True)[:2]
            prefix_len = (sum(map(len, head)) + 80 - len(layout.good)
                          + sum(8 + len(str(v)) for v in range(5, last + 1)))
            assert prefix_len == len(layout.prefix)
            for entries in product(range(128) if k == 1 else outer, repeat=k):
                raw = layout.encode(entries)
                sizes.add(len(raw))
                assert len(raw) == prefix_len + k * (layout.digits + 8)
                spec = all(s in layout.good for s in entries)
                assert packed_scan(raw, layout) == spec
                assert journal.dpll(journal.parse(raw)) == spec
                positive += spec
                checked += 1
        assert len(sizes) == 1
        print(f'Both physical fixtures k={k}: prefix={prefix_len} bytes, N={sizes.pop() * 8} bits')
    print(f'{checked} serialized DIMACS cases matched DPLL and the record lookup, {positive} positive')


def syndrome_checks():
    # Mimic the table-free path on actual packed ASCII. Every field operand
    # is masked by a fixed binary parity check, then folded by literal shifts.
    for t in (7, 9, 12):
        words = parameterization(journal.greedy_words(t))
        r = len(words).bit_length() - 1
        lin = [s for i, s in enumerate(words) if linear_ok(i, r)]
        generator_words = parameterization(lin)
        basis = [generator_words[1 << i] for i in range(r - 1)]
        dual = [v for v in range(1 << t) if all((v & b).bit_count() % 2 == 0 for b in basis)]
        dual_words = parameterization(dual)
        checks = [dual_words[1 << i] for i in range(t-r+1)]
        def byte_mask(v):
            return sum(((v >> i) & 1) << (8 * (i // 3) + i % 3) for i in range(t))
        masks = [byte_mask(v) for v in checks]
        allowed = set(lin)
        for s in range(1 << t):
            raw = int.from_bytes(format(s, f'0{(t+2)//3}o').encode(), 'big')
            passed = True
            for mask in masks:
                acc = raw & mask
                shift = 1
                while shift < 8 * ((t + 2) // 3):
                    acc ^= acc >> shift
                    shift *= 2
                passed &= acc & 1 == 0
            assert passed == (s in allowed)
        print(f't={t}: {len(masks)} fixed ASCII syndrome masks verified on all {1<<t} records')


def large_length_check():
    t = 800
    k = (1 << (16 * t)) - 1
    assert journal.record_width('G', k) == t
    u = (t + 2) // 3
    high = int('1' + format((1 << t) - 1, f'0{u}o'))
    head = f'c cutcode Q {k} {t}\np cnf {high} {k+high+4}\n'.encode()
    prefix_upper = len(head) + 80 + (high - 4) * (8 + len(str(high)))
    assert 8 * prefix_upper < k
    assert 8 * (u + 8) == 2200
    distance = journal.greedy_distance(t)
    volume = sum(comb(t, i) for i in range(distance))
    r_lower = t - (volume.bit_length() - 1)
    loss = (r_lower + 1) // 2
    assert (distance, r_lower, loss) == (8, 745, 373)
    # With 2^s=17/16, M(s)=17/15. The exact integer comparison gives
    # uniform-positive probability at most 2^(-k) at W <= 338k.
    assert 4 * 17**169 * 16**loss < 15**169 * 17**loss
    assert 153 * 2201 < 1000 * 338
    print(f't=800: covering volume={volume}, r>={r_lower}, R/k>={loss}, '
          '2200k<N<2201k, positive lower-tail threshold 338k checked')


def first_stop(h, stop_masks):
    """Disjoint affine fibers, with the number of independent splits at each leaf."""
    cost = 0
    for index, mask in enumerate(stop_masks):
        stop = h & mask
        more = h & ~mask
        cost += bool(stop and more)
        if stop:
            yield stop, cost, index
        if not more:
            return
        h = more
    yield h, cost, len(stop_masks)


def mask_where(size, predicate):
    return sum(1 << i for i in range(size) if predicate(i))


def rank_tail(weight_by_cost, size):
    rest = size
    for j in range(1, max(weight_by_cost, default=0) + 1):
        rest -= weight_by_cost[j - 1]
        # P[J >= j] <= 2**(1-j), without floating point.
        assert rest * (1 << (j - 1)) <= size


def signed(word, width):
    return word - (1 << width) if word & (1 << (width - 1)) else word


def division_checks():
    checked = 0
    for w in range(3, 13):
        mask = (1 << w) - 1
        for j in range(w - 1):
            divisor = 1 << j  # positive and representable in both word interpretations
            for x in range(1 << w):
                a = signed(x, w)
                q = (abs(a) // divisor) * (-1 if a < 0 else 1)
                rem = x & (divisor - 1)
                rounded = a < 0 and rem != 0
                adjusted = a >> j
                if rounded:
                    # Implement +1 by finding the first zero in the shifted word.
                    end = 0
                    while end < w - 1 and adjusted & (1 << end):
                        end += 1
                    adjusted ^= (1 << (end + 1)) - 1
                assert adjusted & mask == q & mask
                assert (rem - divisor if rounded else rem) == a - divisor * q
                assert (x >> j, rem) == divmod(x, divisor)
                checked += 1
    print(f'{checked} signed and unsigned power-of-two division/remainder cases')


def primitive_checks():
    w = 3
    n = 2 * w
    size = 1 << n
    wm = (1 << w) - 1
    full = (1 << size) - 1
    left = [x & wm for x in range(size)]
    right = [x >> w for x in range(size)]
    bits = [mask_where(size, lambda x: left[x] >> j & 1) for j in range(w)]
    right_bits = [mask_where(size, lambda x: right[x] >> j & 1) for j in range(w)]
    diff = [a ^ b for a, b in zip(bits, right_bits)]
    eq = mask_where(size, lambda x: left[x] == right[x])
    uless = mask_where(size, lambda x: left[x] < right[x])
    sless = mask_where(size, lambda x: signed(left[x], w) < signed(right[x], w))
    powers = []
    for j, sign in product(range(w), (1, -1)):
        ends = [full ^ bits[i] if sign == 1 else bits[i] for i in range(j, w - 1)]
        delta = [((a + sign * (1 << j)) & wm) ^ a for a in left]
        classes = {value: mask_where(size, lambda x: delta[x] == value) for value in set(delta)}
        powers.append((ends, delta, classes))
    # Known lower propagate bits make all sum (difference) bits affine.
    # Test that on each slice the true result is affine using the parallelogram law.
    for sign in (-1, 1):
        for p in range(1 << (w - 1)):
            domain = [x for x in range(size) if ((left[x] ^ right[x]) & (wm >> 1)) == p]
            f = lambda x: (left[x] + sign * right[x]) & wm
            for a, b in product(domain, repeat=2):
                assert f(a) ^ f(b) ^ f(domain[0]) == f(a ^ b ^ domain[0])

    flat_count = pieces = 0
    for h in flats(n):
        flat_count += 1
        hist = Counter()
        for leaf, cost, index in first_stop(h, diff[::-1]):
            hist[cost] += leaf.bit_count()
            pieces += 1
            if index == w:
                assert not leaf & ~eq and not leaf & (uless | sless)
            else:
                pos = w - 1 - index
                result = right_bits[pos]
                assert leaf & (uless ^ result) == 0
                assert leaf & (sless ^ result ^ (full if pos == w - 1 else 0)) == 0
                assert leaf & eq == 0
        assert sum(hist.values()) == h.bit_count()
        rank_tail(hist, h.bit_count())
        for ends, delta, classes in powers:
            hist.clear()
            for leaf, cost, _ in first_stop(h, ends):
                hist[cost] += leaf.bit_count()
                pieces += 1
                rep = (leaf & -leaf).bit_length() - 1
                assert leaf & ~classes[delta[rep]] == 0
            rank_tail(hist, h.bit_count())
    print(f'{flat_count} distinct flats in six bits, {pieces} first-stop leaves '
          'for word order and signed power increments')


def memory_checks():
    # Compare conditioning addresses one bit at a time against destructive
    # scalar execution with two stores, an intervening load and a signed branch.
    w = 4
    size = 4096
    full = (1 << size) - 1
    xv = [x & 15 for x in range(size)]
    yv = [(x >> 4) & 15 for x in range(size)]
    zv = [x >> 8 for x in range(size)]
    fields = [tuple(mask_where(size, lambda x: data[x] >> j & 1) for j in range(w))
              for data in (xv, yv, zv)]
    fixed = lambda a: tuple(full if a >> j & 1 else 0 for j in range(w))
    init = {0: fields[0], 1: fields[1], 2: fields[2]}
    def address_fibers(h, fields):
        parts = [(h, 0, 0)]
        for j, mask in enumerate(fields):
            children = []
            for domain, address, cost in parts:
                lo, hi = domain & ~mask, domain & mask
                nxt = cost + bool(hi and lo)
                if lo:
                    children.append((lo, address, nxt))
                if hi:
                    children.append((hi, address | (1 << j), nxt))
            parts = children
        assert max(c for _, _, c in parts) <= w
        return parts
    accepted = covered = 0
    leaves = alias = 0
    for h, a, _ in address_fibers(full, fields[0]):
        db = {**init, a: fields[2]}
        moving = tuple(x ^ y for x, y in zip(fields[0], fields[1]))
        for g, b, _ in address_fibers(h, moving):
            reply = db.get(b, fixed(0))
            latest = {**db, b: fields[0]}
            for f, c, _ in address_fibers(g, reply):
                last = latest.get(c, fixed(0))
                for part, _, i in first_stop(f, [x ^ y for x, y in zip(last[::-1], fields[2][::-1])]):
                    if i < w:
                        result = fields[2][w - 1 - i] ^ (full if i == 0 else 0)
                        accepted |= part & result
                    assert not covered & part
                    covered |= part
                    leaves += 1
                if a == b or c == b:
                    alias += f.bit_count()
    def scalar(i):
        x, y, z = xv[i], yv[i], zv[i]
        memory = {0: x, 1: y, 2: z}
        memory[x] = z
        b = x ^ y
        v = memory.get(b, 0)
        memory[b] = x
        return signed(memory.get(v, 0), w) < signed(z, w)
    assert covered == full and accepted == mask_where(size, scalar)
    print(f'Two-store trace on {size} inputs: {accepted.bit_count()} true, {leaves} leaves, '
          f'{alias} with coincident stores or a final read at the second store')


def selector_checks():
    sat = upper_and_truth()
    yes = {i for i, bit in enumerate(sat) if bit}
    covered = set()
    passed = 0
    # A maximal-dimensional flat in eight independent disjointness pairs
    # is a product of lines. The digits denote an omitted point in the triangle.
    for omitted in product(range(3), repeat=8):
        if 2 not in omitted:  # omitting the negative-unit point fixes its mask bit to zero
            continue
        choices = [[v for v in range(3) if v != skip] for skip in omitted]
        packed = [0]
        for i, vals in enumerate(choices):
            shift = (12 if i < 4 else 8) + (i % 4)
            mshift = (4 if i < 4 else 0) + (i % 4)
            packed = [p | ((v == 1) << shift) | ((v == 2) << mshift)
                      for p in packed for v in vals]
        assert len(packed) == 256 and all(p in yes for p in packed)
        passed += 1
        covered.update(packed)
    assert passed == 6305 and covered == yes
    print(f'{passed} full-dimensional accepting products cover exactly the {len(covered)} positives')


if __name__ == '__main__':
    code_checks()
    file_checks()
    syndrome_checks()
    large_length_check()
    primitive_checks()
    division_checks()
    memory_checks()
    selector_checks()
