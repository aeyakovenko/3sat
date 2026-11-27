"""Check finite constants, greedy resigning, and physical files for the support-query bound."""
from itertools import combinations, product
from math import comb
from random import Random


def cover_numbers(k, r):
    """For each possible large shattered size, count covers of that union by tight triples."""
    sizes = []
    s = k
    while comb(s, k) <= r:
        d = (s + k - 1) // k
        covers = sum((-1)**i * comb(s, i) * comb(comb(s - i, k), d) for i in range(s + 1))
        assert covers > 0
        sizes.append((s, d, covers, comb(r, d) // covers))
        s += 1
    return sizes


def budget(k, r):
    return sum(comb(k * r, j) for j in range(k)) + sum(a[-1] for a in cover_numbers(k, r))


def apply_budget(k, r):
    n = budget(k, r)
    for _ in range(r):
        n = n * ((1 << k) - 1) // (1 << k)
    return n


def point_pattern(point, support):
    return sum((point >> x & 1) << j for j, x in enumerate(support))


def exact_local_trial(v, k, count, rng, signs):
    supports = list(combinations(range(v), k))
    free = list(sorted(rng.sample(range(len(supports)), count)))
    vertices = sorted(set().union(*(supports[i] for i in free)))
    local_idx = {x:i for i,x in enumerate(vertices)}
    chosen = set(free)
    local = [(i, tuple(local_idx[x] for x in s)) for i,s in enumerate(supports)
             if all(x in local_idx for x in s)]
    fixed = [(i,s) for i,s in local if i not in chosen]
    live = [point for point in range(1 << len(vertices))
            if all(point_pattern(point,s) != signs[i] for i,s in fixed)]
    first_count = len(live)
    assert len(live) <= budget(k, count)
    resigned = list(signs)
    local_support = dict(local)
    for i in free:
        bins = [[] for _ in range(1 << k)]
        for point in live:
            bins[point_pattern(point, local_support[i])].append(point)
        best = max(range(len(bins)), key=lambda j: len(bins[j]))
        resigned[i] = best
        prev = len(live)
        live = [p for j,group in enumerate(bins) if j != best for p in group]
        assert len(live) <= prev * ((1 << k)-1) // (1 << k)
    assert not live
    assert all(resigned[i] == signs[i] for i,_ in fixed)
    differences = sum(a!=b for a,b in zip(resigned,signs))
    assert 0 <= differences <= count
    assert not any(all(point_pattern(x,s) != resigned[i] for i,s in local)
                   for x in range(1 << len(vertices)))
    return first_count, differences


def render(v, k, signs):
    """A minus or an ASCII space occupies the same sign byte for each literal."""
    supports = list(combinations(range(v), k))
    width = len(str(v))
    out = bytearray(f'p cnf {v} {len(signs)}\n'.encode())
    offsets = []
    for i,support in enumerate(supports):
        positions = []
        for j,x in enumerate(support):
            digits = str(x+1).encode()
            out.extend(b' '*(width-len(digits)))
            positions.append(len(out))
            out.extend(b'-' if signs[i] >> j & 1 else b' ')
            out.extend(digits+b' ')
        out.extend(b'0\n')
        offsets.append(positions)
    return out, offsets


def main():
    assert cover_numbers(3,63) == [(3,1,1,63),(4,2,6,325),(5,2,15,130),
                                     (6,2,10,195),(7,3,945,42),(8,3,840,47)]
    assert budget(3,63) == 18758 and apply_budget(3,63) == 0
    for k,r in [(2,16),(3,63),(4,262),(5,864)]:
        assert apply_budget(k,r) == 0
    for s,d,c,_ in cover_numbers(3,63):
        all_edges = list(combinations(range(s),3))
        actual = sum(len(set().union(*es)) == s for es in combinations(all_edges,d))
        assert c == actual
    rng = Random(63189)
    trials = maximum = positive = 0
    for v,k,holes in [(7,2,16),(8,2,16),(9,3,63),(10,3,63),(11,3,63)]:
        m = comb(v,k)
        for j in range(16):
            # Nonzero patterns plant all zero; the all-ones pattern maximizes many projected families.
            signs = [(1<<k)-1]*m if j%3==0 else [rng.randrange(1 if j%3==1 else 0,1<<k) for _ in range(m)]
            cnt,diff = exact_local_trial(v,k,holes,rng,signs)
            maximum=max(maximum,cnt)
            positive+=int(all(signs))
            assert (not all(signs)) or diff>0
            trials+=1
    for v in (9,10,37):
        k=3
        m=comb(v,k)
        signs=[rng.randrange(8) for _ in range(m)]
        out, offsets=render(v,k,signs)
        new=signs.copy()
        selected=rng.sample(range(m),63)
        for i in selected:new[i]^=7
        other, positions=render(v,k,new)
        assert positions==offsets and len(other)==len(out)
        actual=[i for i,(a,b) in enumerate(zip(out,other)) if a!=b]
        assert sorted(z for i in selected for z in offsets[i])==actual
        parsed=[tuple(map(int,row.split()))[:-1] for row in out.splitlines()[1:]]
        assert len(parsed)==m and all(len(row)==3 for row in parsed)
    print(f'63-edge bounds and six exact covering counts verified; {trials} local completions, '
          f'{positive} planted inputs, largest local candidate family {maximum}; '
          'all altered induced instances UNSAT, all physical layouts retained exact offsets.')


if __name__ == '__main__':
    main()
