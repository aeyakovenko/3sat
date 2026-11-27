"""Check integer-shift grammars, sorted sumset gaps and succinct SAT mark queries."""
from itertools import product
from math import comb
from random import Random


class Grammar:
    """A leaf holds one address; a concatenation translates each child by an offset."""

    def __init__(self):
        self.rules = []

    def leaf(self, address):
        self.rules.append(address)
        return len(self.rules) - 1

    def join(self, left, right):
        self.rules.append((left, right))
        return len(self.rules) - 1

    def fold(self, entries):
        entries = list(entries)
        if not entries:
            raise ValueError("empty concatenation")
        while len(entries) > 1:
            nxt = [(self.join(entries[i], entries[i + 1]), 0)
                   for i in range(0, len(entries) - 1, 2)]
            if len(entries) % 2:
                nxt.append(entries[-1])
            entries = nxt
        return entries[0]

    def values(self, root, modulus=None):
        """Independent, literal expansion, including offset on the root."""
        stack = [root]
        while stack:
            i, shift = stack.pop()
            rule = self.rules[i]
            if isinstance(rule, int):
                value = rule + shift
                yield value if modulus is None else value % modulus
            else:
                for j, delta in reversed(rule):
                    stack.append((j, shift + delta))

    def fourier(self, root, z, p):
        table = []
        for rule in self.rules:
            if isinstance(rule, int):
                table.append(pow(z, rule, p))
            else:
                table.append(sum(table[j] * pow(z, shift, p) for j, shift in rule) % p)
        node, offset = root
        return table[node] * pow(z, offset, p) % p


def lists_for(q, k):
    base = 2 * q
    sep = 2 * q ** (k + 1)
    total = sum(base ** j for j in range(k - 1))
    lists = []
    for j in range(k):
        row = []
        for i in range(q):
            high = (q - 1 - i) * total if j == 0 else i * base ** (j - 1)
            low = q ** j * (i * (i + 1) // 2)
            row.append(sep * high + low)
        lists.append(row)
    return lists, sep


def chronological(lists):
    g = Grammar()
    root = (g.leaf(0), 0)
    for values in lists:
        j, delta = root
        root = g.fold((j, delta + v) for v in values)
    return g, root


def recover(q, k, z):
    sep = 2 * q ** (k + 1)
    p, residue = divmod(z, sep)
    offsets = [0]
    for _ in range(k - 1):
        p, digit = divmod(p, 2 * q)
        offsets.append(digit - q + 1)
    if p:
        return None
    lo = max(-d for d in offsets)
    end = min(q - d for d in offsets)
    if lo >= end:
        return None

    def value(t):
        return sum(q ** j * ((t + d) * (t + d + 1) // 2) for j, d in enumerate(offsets))

    hi = end
    while lo < hi:
        mid = (lo + hi) // 2
        if value(mid) < residue:
            lo = mid + 1
        else:
            hi = mid
    if lo < end and value(lo) == residue:
        return tuple(lo + d for d in offsets)
    return None


def gap_check():
    rng = Random(7817)
    for k, q in ((2, 3), (3, 3), (2, 64), (3, 20), (4, 8)):
        lists, sep = lists_for(q, k)
        g, root = chronological(lists)
        direct = {sum(row) for row in product(*lists)}
        sorted_marks = sorted(g.values(root))
        assert len(direct) == q ** k and sorted_marks == sorted(direct)
        gaps = {b - a for a, b in zip(sorted_marks, sorted_marks[1:])}
        expected = {sum(q ** j * (x + 1) for j, x in enumerate(coords))
                    for coords in product(range(q - 1), repeat=k)}
        assert len(expected) == (q - 1) ** k and expected <= gaps
        assert len(g.rules) == 1 + k * (q - 1)
        assert all(recover(q, k, z) is not None for z in direct)
        tests = range(sorted_marks[-1] + 2) if q == 3 else [rng.randrange(sorted_marks[-1] + sep) for _ in range(5000)]
        assert all((recover(q, k, z) is not None) == (z in direct) for z in tests)
        print(f"{k} lists of {q}: {q ** k} stores, {len(g.rules)} chronological rules, "
              f"{len(gaps)} distinct sorted gaps, including all {len(expected)} predicted gaps")


def masked_check():
    rng = Random(427)
    cases = 0
    for k, q in ((2, 3), (3, 3), (2, 16), (3, 11)):
        lists, sep = lists_for(q, k)
        masks = product(range(1 << q), repeat=k) if q == 3 else (
            [rng.getrandbits(q) for _ in range(k)] for _ in range(50))
        for mask in masks:
            indices = [[i for i in range(q) if m >> i & 1] for m in mask]
            marked = {sum(row[i] for row, i in zip(lists, xs)): xs
                      for xs in product(*indices)}
            if marked:
                chosen = [[row[i] for i in ids] for row, ids in zip(lists, indices)]
                g, root = chronological(chosen)
                ordered = sorted(g.values(root))
                assert ordered == sorted(marked)
                assert len(g.rules) == 1 + sum(len(ids) - 1 for ids in indices)
                observed = {b-a for a, b in zip(ordered, ordered[1:])}
                consecutive = [[i for i in ids if i+1 in ids] for ids in indices]
                predicted = {sum(q**j * (i+1) for j, i in enumerate(xs))
                             for xs in product(*consecutive)}
                assert predicted <= observed
                assert all(len(pairs) >= q - 1 - 2*(q-len(ids))
                           for pairs, ids in zip(consecutive, indices))
            # Check marked and unmarked targets, including ineligible tuples' sums.
            samples = [sum(row[rng.randrange(q)] for row in lists) for _ in range(30)]
            for z in list(marked) + samples + [sep*q**k]:
                candidate = recover(q, k, z)
                if candidate is not None and all(i in ids for i, ids in zip(candidate, indices)):
                    assert marked[z] == candidate
                else:
                    assert z not in marked
            cases += 1
    print(f"{cases} mask families: grammar sizes, sorted gaps and direct tuple recovery agree")


def differences(word, order):
    for _ in range(order):
        word = [b - a for a, b in zip(word, word[1:])]
    return word


def polynomial_check():
    rng = Random(601)
    cases = 0
    for k, q in ((2, 12), (3, 9), (4, 8)):
        for s in range(1, 6):
            power_sum = sum(q**j for j in range(k))
            sep = 1 + comb(q-1+s, s+1)*power_sum
            mask = (1 << q) - 1
            masks = [[mask]*k]
            for _ in range(8):
                masks.append([mask ^ sum(1 << i for i in rng.sample(range(q), q//(2*(s+1))))
                              for _ in range(k)])
            for row in masks:
                allowed = [[i for i in range(q) if b >> i & 1] for b in row]
                def addr(xs):
                    high = sum((2*q)**(j-1) * (q-1-xs[0]+xs[j]) for j in range(1,k))
                    low = sum(q**j * comb(i+s,s+1) for j,i in enumerate(xs))
                    return high*sep + low
                table = sorted(addr(xs) for xs in product(*allowed))
                observed = set(differences(table, s))
                starts = [[i for i in ids if all(i+t in ids for t in range(s+1))]
                          for ids in allowed]
                predicted = {sum(q**j*(i+s) for j,i in enumerate(xs)) for xs in product(*starts)}
                assert predicted <= observed
                assert len(predicted) == len(list(product(*starts)))
                cases += 1

            # Test independently at a polynomial-decorated join, including wrap.
            modulus = 1 << 17
            left, right = [[rng.randrange(modulus) for _ in range(rng.randrange(2, 11))]
                           for _ in range(2)]
            decorated = []
            for child in (left, right):
                coeff = [rng.randrange(-300, 300) for _ in range(s)]
                decorated.extend((value + sum(a*comb(i, h) for h,a in enumerate(coeff))) % modulus
                                 for i, value in enumerate(child))
            observed = {d % modulus for d in differences(decorated, s)}
            previous = {d % modulus for child in (left,right) for d in differences(child, s)}
            assert len(observed - previous) <= s
    print(f"{cases} polynomial-offset tables: predicted sorted differences survive through fifth order")


def block_lane_check():
    rng = Random(2031)
    for k, lanes in ((2, 4), (3, 3), (3, 4), (2, 6)):
        blocks = 1 << lanes
        q = blocks * lanes
        digit_base = 2 * blocks**2
        separator = digit_base**k
        lists = []
        for j in range(k):
            row = []
            for i in range(q):
                b, r = divmod(i, lanes)
                if j == 0:
                    diffs = (lanes-1-r) * sum((2*lanes)**a for a in range(k-1))
                else:
                    diffs = r * (2*lanes)**(j-1)
                high = blocks**j * b + blocks**k * diffs
                low = digit_base**j * ((2*b+1) << r)
                row.append(high * separator + low)
            lists.append(row)
        # Leave exactly the first half fixed and the other outer lanes arbitrary.
        choices = [list(range(q)) for _ in range(k-1)]
        choices.append([i for i in range(q) if i < q//2 or rng.randrange(2)])
        marked = sorted(sum(row[i] for row,i in zip(lists, xs)) for xs in product(*choices))
        assert len(set(marked)) == len(marked)
        assert marked[-1].bit_length() <= 12 * (q+1).bit_length()
        for s in range(1, lanes//2+1):
            marks_and_read = sorted(marked + [rng.randrange(marked[-1]+1)])
            observed = set(differences(marks_and_read, s))
            good = [[i for i in ids if i % lanes < lanes-s and (j < k-1 or i < q//2)]
                    for j,ids in enumerate(choices)]
            predicted = {sum(row[i] % separator for row,i in zip(lists,xs))
                         for xs in product(*good)}
            assert len(predicted) == blocks**k * (lanes-s)**k // 2
            assert len(predicted - observed) <= s
        print(f"{k} lists with {blocks} blocks of {lanes} lanes: all simultaneous "
              f"sorted bounds through order {lanes//2} hold after the target read")


def sat_mark(variables, clauses):
    g = Grammar()
    root = (g.leaf(0), 0)
    for i in range(1, variables + 1):
        additions = [sum(sum(1 for lit in row if lit == sign * i) << (3 * j)
                         for j, row in enumerate(clauses)) for sign in (-1, 1)]
        root = g.fold((root[0], root[1] + d) for d in additions)
    for j in range(len(clauses)):
        root = g.fold((root[0], root[1] + (d << (3 * j))) for d in range(3))
    target = sum(3 << (3 * j) for j in range(len(clauses)))
    return sum(a == target for a in g.values(root))


def sat_check():
    rows = [tuple(sign * i for i, sign in enumerate(signs, 1))
            for signs in product((-1, 1), repeat=3)]
    cases = 0
    for mask in range(256):
        selected = [row for i, row in enumerate(rows) if mask >> i & 1]
        # More than seven distinct rows on three names gives a contradiction.
        if len(selected) > 4 and len(selected) != 8:
            continue
        expected = sum(all(any(bits[abs(lit)-1] == (lit > 0) for lit in row)
                           for row in selected) for bits in product((0, 1), repeat=3))
        assert sat_mark(3, selected) == expected
        cases += 1
    print(f"{cases} proper CNFs: generated writes to the final address equal exact model count")


def modular_check():
    # The order of 3 mod 17 is 16; every cyclic character is thus available.
    modulus, p = 16, 17
    rng = Random(963)
    for _ in range(100):
        g = Grammar()
        root = (g.leaf(rng.randrange(modulus)), 0)
        for _ in range(4):
            root = (g.join((root[0], rng.randrange(-20, 21)),
                           (rng.randrange(len(g.rules)), rng.randrange(-20, 21))), 0)
        values = list(g.values(root, modulus))
        assert len(values) <= 16
        f = [g.fourier(root, pow(3, j, p), p) for j in range(modulus)]
        for a in range(modulus):
            recovered = sum(v * pow(3, -j*a, p) for j, v in enumerate(f))
            assert recovered * pow(modulus, -1, p) % p == values.count(a)
    print("100 modular grammars: all multiplicities recovered from compositional character evaluations")


if __name__ == "__main__":
    gap_check()
    masked_check()
    polynomial_check()
    block_lane_check()
    sat_check()
    modular_check()
