"""Check equality-block impostors and close the two-magnitude tree test exactly."""

from collections import Counter
from itertools import combinations, product
from math import comb

from sparse_edit_clock_audit import layout, relations


def accepts(values, blocks):
    checked = set(range(len(values)))
    for block in blocks:
        checked.difference_update(block)
        first = values[block[0]]
        if any(values[i] != first for i in block[1:]):
            return False
    return all(values[i] == 0 for i in checked)


def check_single_supports():
    cases = 0
    for m in range(1, 8):
        for k in range(1, m+1):
            a, r = divmod(m, k+1)
            for j in range(1, r+1):
                # Relabelling the sites preserves all decisions and clocks.
                support = tuple(range(j))
                large = [tuple(range(j+i*(k+1), j+(i+1)*(k+1))) for i in range(a)]
                blocks = [support, *large]
                assert 2*m-len(blocks) == 2*m-a-1
                for values in product((0, 1, 2), repeat=m):
                    changed = tuple(i for i, x in enumerate(values) if x)
                    if len(changed) > k:
                        continue
                    wrong = bool(changed) and accepts(values, blocks)
                    assert wrong == (changed == support and len({values[i] for i in support}) == 1)
                    cases += 1
    return cases


def matchings(sites, k, b):
    """Unordered families of disjoint sets; recurse in lexicographic order."""
    sets = list(combinations(sites, k))

    def tail(start, remaining, chosen):
        if len(chosen) == b:
            yield tuple(chosen)
            return
        for pos in range(start, len(sets)):
            group = sets[pos]
            if all(i in remaining for i in group):
                yield from tail(pos+1, remaining.difference(group), [*chosen, group])

    yield from tail(0, set(sites), [])


def check_balanced():
    families = 0
    for m in range(2, 11):
        for k in range(1, m+1):
            q, r = m//(k+1)+1, m%(k+1)
            b = k+1-r
            if m > k:
                lo, hi = divmod(m, q)
                lengths = [lo+1]*hi + [lo]*(q-hi)
                assert len(lengths) >= 2 and sum(sorted(lengths)[:2]) > k
                assert min(lengths) <= k
            if b > q:
                continue
            counts = Counter()
            for small in matchings(range(m), k, b):
                remaining = sorted(set(range(m)).difference(*small))
                blocks = list(small) + [tuple(remaining[i:i+k+1])
                                        for i in range(0, len(remaining), k+1)]
                assert len(blocks) == q and all(len(g) == k+1 for g in blocks[b:])
                counts.update(small)
                families += 1
            assert len(counts) == comb(m,k) and len(set(counts.values())) == 1
            assert sum(counts.values()) % b == 0
    return families


def closure(rels):
    """A state gives root mask and anchored alternativity for each magnitude."""
    def join(left, right, mat):
        mask, anchored = left
        child, child_anchored = right
        result = sum((1 << i) for i in range(5) if mask & (1 << i) and mat[i] & child)
        different = anchored or child_anchored or bool(mat[2] & child & ~4)
        return result, different

    leaf = ((14, False), (21, False))  # center and +/-1; center and +/-2
    states = {leaf}
    while True:
        larger = set(states)
        for a, b, matrix in product(states, states, rels):
            new = tuple(join(left, right, matrix) for left, right in zip(a, b))
            assert any(anchored or (mask & ~4) for mask, anchored in new)
            larger.add(new)
        if larger == states:
            return len(states)
        states = larger


def classified(mat):
    def ok(a, b):
        return bool(mat[a+2] & (1 << (b+2)))

    deviations = range(-2, 3)
    if any(all(ok(e, sign*e) for e in deviations) for sign in (1, -1)):
        return True
    if all(ok(e, 0) for e in deviations) or all(ok(0, e) for e in deviations):
        return True
    return any(ok(e, 0) and ok(0, e) for e in (-1, 2))


def check_or_nor_program():
    """Compare real modular sums on enough patterns to cover every pair count."""
    trials = 0
    for width in (144, 240, 336, 432, 624):
        modulus = 1 << width
        size = width//8
        odd = width//(width & -width)
        rep = 0
        for length in range(1, odd+1):
            rep = 256*rep + 1
            if not rep % odd:
                break
        delta = rep << (8*(size-length))
        center = int.from_bytes(b'5'*size, 'little')
        up = center+2*delta
        assert length >= 3 and up | center == up
        assert (center-delta) | center == center
        for touched in range(256):
            # Vary which member changes; some touched pairs have both changed.
            pairs = [(up if i<touched and i%3 != 0 else center,
                      up if i<touched and i%3 != 1 else center) for i in range(255)]
            left = sum(x|y for x,y in pairs[:202])
            right = sum(~(x|y) for x,y in pairs[202:])
            assert (left-right) % modulus == (touched*2*delta) % modulus
            assert ((left-right) % modulus == 0) == (touched == 0)
            trials += 1
    return trials


def check_indirect_program():
    tests = 0
    mixed = 0
    low = {256 + 3*i for i in range(510)} | {2809}
    assert len(low) == 511
    for width in (144, 432, 1296):
        modulus = 1 << width
        root = 1 << (width//2)
        delta = (modulus-root)//255
        center = 53*((modulus-1)//255)
        words = modulus//(2*width)
        assert delta % width == 0 and delta*delta % modulus == 0
        assert (255*center)**2 % modulus == 2809
        assert (255*center+delta-delta)*(255*center) % modulus == 2809
        for digit in (-2, -1, 1, 2):
            for total in range(1, 511):
                l = min(255, total)
                r = total-l
                address = ((255*center+l*digit*delta) * (255*center+r*digit*delta)) % modulus
                assert address == (2809-53*digit*total*delta) % modulus
                assert address >= words or 3000 < address < words//2
                tests += 1
        for score in range(-1020, 1021):
            sign = -1 if score < 0 else 1
            changes = [2*sign]*(abs(score)//2)
            if abs(score) % 2:
                changes.append(sign)
            if score == 0:
                changes = [1, -1]
            changes.extend([0]*(510-len(changes)))
            left = 255*center + sum(changes[:255])*delta
            right = 255*center + sum(changes[255:])*delta
            address = left*right % modulus
            assert address == (2809-53*score*delta) % modulus
            if score:
                assert address >= words or 3000 < address < words//2
            else:
                assert address == 2809
            mixed += 1
    return tests, mixed


def check_pair_quota():
    instances = 0
    for v in range(3, 7):
        pairs = list(combinations(range(v), 2))
        for h in range(2, v+1):
            sought = [sum(1 << i for i,(a,b) in enumerate(pairs) if a in g and b in g)
                      for g in combinations(range(v), h)]
            r, extra = divmod(v, h-1)
            expected = (h-1-extra)*comb(r, 2) + extra*comb(r+1, 2)
            smallest = min(mask.bit_count() for mask in range(1 << len(pairs))
                           if all(mask & candidate for candidate in sought))
            assert smallest == expected
            instances += 1
    return instances


if __name__ == '__main__':
    print(f'{check_single_supports():,} labeled tests on isolated-support programs')
    print(f'{check_balanced():,} disjoint small-block families checked')
    print(f'{check_or_nor_program():,} modular OR/NOR counterexample patterns')
    ordinary, signed = check_indirect_program()
    print(f'{ordinary:,} four-digit indirect-LOAD cases; {signed:,} attainable signed sums; '
          f'{check_pair_quota()} exact small pair quotas')
    for w in (128, 240, 272, 336, 512, 768, 1024):
        _, _, vals = layout(w)
        rels = relations(w, vals)
        assert all(classified(r) for r in rels)
        print(f'width {w}: {len(rels)} opcode relations, {closure(rels)} two-magnitude tree states')
