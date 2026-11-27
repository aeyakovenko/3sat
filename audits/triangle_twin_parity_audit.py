"""Parity of both triangle verdicts, and adaptive bit/word cylinders. Requires pycosat."""

from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations_with_replacement, product
from math import comb, factorial, prod


def triangle_bank(a, b, c):
    return [((i*b+k), (a*b+k*c+j), (a*b+b*c+j*a+i))
            for i,k,j in product(range(a),range(b),range(c))]


@lru_cache(maxsize=None)
def graph_histogram(a, b):
    """Histogram of I(G) for labelled bipartite G on a by b vertices."""
    counts = Counter()
    for rows in combinations_with_replacement(range(1 << a), b):
        multiplicity = factorial(b)//prod(factorial(k) for k in Counter(rows).values())
        independent = sum(1 << sum(not (row & subset) for row in rows)
                          for subset in range(1 << a))
        counts[independent] += multiplicity
    assert sum(counts.values()) == 1 << (a*b)
    return counts


def verdict_counts(a, b, c):
    a,b,c = sorted((a,b,c))
    negative = sum(mult*(independent**c) for independent,mult in graph_histogram(a,b).items())
    return negative, (1 << (a*b+b*c+c*a))-negative


def count_audit():
    shapes = list(product(range(1,5), range(1,5), range(1,10)))
    for dims in shapes:
        no, yes = verdict_counts(*dims)
        assert no % 2 == yes % 2 == 1
        for prime in (2,3,5,7):
            reduced = tuple(1+(s-1)%(prime-1) for s in dims)
            reference = verdict_counts(*reduced)
            assert (no-reference[0])%prime == (yes-reference[1])%prime == 0
        a,b,c = dims
        if a == 1:
            assert no == sum(comb(b,u)*((1 << b)+(1 << (b-u)))**c for u in range(b+1))
    return len(shapes)


def get_physical():
    import pycosat
    from selected_triangle_audit import side_two_layout
    from table_probe_context_audit import parse

    source, offsets = side_two_layout(pin_selectors=False)
    data = bytearray(source)
    triangles = [sum(1 << e for e in edges) for edges in triangle_bank(2,2,2)]
    positives = 0
    top = 0
    for x in range(1 << len(offsets)):
        for i,pos in enumerate(offsets):
            data[pos] = 48 + ((x >> i) & 1)
        clauses, variables = parse(data)
        value = pycosat.solve(clauses, vars=variables) != 'UNSAT'
        assert value == any(x & t == t for t in triangles)
        positives += value
        top += value * (-1)**(len(offsets)-x.bit_count())
    assert positives == 2397 and top == -3
    return offsets, positives, top


def transcript_audit(dims, groups, greedy):
    edges = triangle_bank(*dims)
    masks = [sum(1 << e for e in triangle) for triangle in edges]
    n = sum(len(group) for group in groups)
    assert sorted(v for group in groups for v in group) == list(range(n))
    block_masks = [sum(1 << e for e in group) for group in groups]
    full = (1 << n)-1
    hit = [0,0]
    # One entry lists all final answers for the last covering read of that cell.
    completions = defaultdict(dict)

    def walk(path, seen, ones, last):
        live = [triangle for triangle in masks if not (triangle & (seen^ones))]
        verdict = None
        if any((tri & seen)==tri for tri in live):
            verdict = 1
        elif not live:
            verdict = 0
        if verdict is not None:
            leaf_size = 1 << (n-seen.bit_count())
            hit[verdict] += leaf_size
            if seen == full:
                completions[last][ones] = verdict
            return

        if greedy:
            block = max((idx for idx,mask in enumerate(block_masks) if not seen & mask),
                        key=lambda idx: sum((tri & block_masks[idx]).bit_count() for tri in live))
        else:
            bit = next(i for i in range(n) if (1<<i) & live[0] & ~seen)
            block = next(i for i,mask in enumerate(block_masks) if mask & (1 << bit))
        mask = block_masks[block]
        if mask | seen == full:
            last = (path, block)
        answer = mask
        while True:
            walk(path+((block,answer),),seen | mask,ones | answer,last)
            if not answer:
                break
            answer = (answer-1) & mask

    walk((),0,0,None)
    assert tuple(hit) == verdict_counts(*dims)
    full_counts = [sum(value==sign for cell in completions.values() for value in cell.values())
                   for sign in (0,1)]
    assert all(x%2 for x in full_counts)
    odd = 0
    for (_,block), results in completions.items():
        assert len(results) == 1 << len(groups[block])
        if sum(results.values()) % 2:
            odd += 1
            for e in groups[block]:
                changes = sum(value != results[x^(1<<e)] for x,value in results.items() if not x & (1<<e))
                assert changes % 2 == 1
    assert odd % 2 == 1
    return *full_counts, odd


def signed_or_audit(copies, groups, threshold=None):
    """Exhaust a deterministic grouped-probe DAG on an OR of independent side-two graphs.

    Coalescing states with the same remaining variables and residual triangles
    preserves multiplicity when totals are summed back up the DAG.
    """
    if threshold is None:
        width, base_signed = 12, -3
        bank = [sum(1<<e for e in t) for t in triangle_bank(2,2,2)]
    else:
        from itertools import combinations
        width,t = threshold
        bank = [sum(1<<e for e in indices) for indices in combinations(range(width),t)]
        base_signed = (-1)**(width-t)*comb(width-1,t-1)
    initial = tuple(sorted(t << (width*i) for i in range(copies) for t in bank))
    group_masks = [sum(1<<e for e in group) for group in groups]
    n = width*copies
    assert sorted(e for group in groups for e in group) == list(range(n))

    @lru_cache(maxsize=None)
    def walk(unseen, live):
        # Return top coefficient, full NO/YES, sum |signed cell weights|,
        # and number of disjoint bichromatic pairs obtainable by choosing
        # the least favorable single coordinate in each such cell.
        if not live or live[0]==0:
            return (0,0,0,0,0) if unseen else (bool(live),int(not live),int(bool(live)),0,0)
        relevant = 0
        for tri in live:
            relevant |= tri
        if any(mask & unseen and not mask & relevant for mask in group_masks):
            # This policy can never visit that whole word on any continuation.
            return 0,0,0,0,0
        block = next(mask for mask in group_masks if mask & live[0])
        assert block & unseen == block
        answers = []
        reply = block
        while True:
            residual = tuple(sorted({tri & ~block for tri in live if not tri & (block^reply)}))
            answers.append((reply,residual))
            if not reply:
                break
            reply = (reply-1) & block
        if unseen == block:
            values = {reply:bool(rest and rest[0]==0) for reply,rest in answers}
            yes = sum(values.values())
            signed = sum((-1)**((block^reply).bit_count())*out for reply,out in values.items())
            min_pairs = min(sum(out != values[reply^bit] for reply,out in values.items() if not reply & bit)
                            for bit in (1<<e for e in range(n) if block>>e&1))
            assert min_pairs >= abs(signed)
            return signed,len(values)-yes,yes,abs(signed),min_pairs
        result = [0]*5
        for reply,rest in answers:
            signed,no,yes,absolute,pairs = walk(unseen^block,rest)
            result[0] += (-1)**((block^reply).bit_count())*signed
            for j,x in enumerate((no,yes,absolute,pairs),start=1):
                result[j] += x
        return tuple(result)

    value,no,yes,absolute,pairs = walk((1<<n)-1,initial)
    assert value == (-1)**(copies+1) * base_signed**copies
    assert no%2 == yes%2 == (value%2)
    assert pairs >= absolute >= abs(value)
    return value, (no,yes), pairs, walk.cache_info().currsize


def signed_closed_form(a,b,c):
    # A fixed a-by-b bank G. An alternating sum over the neighbor set of
    # one vertex on the third side is the bipartite independence polynomial
    # I_G(-1). Summing over one class leaves just dominating subsets.
    signed = 0
    for rows in combinations_with_replacement(range(1<<a), b):
        multiplicity = factorial(b)//prod(factorial(k) for k in Counter(rows).values())
        signed_independent = sum((-1)**subset.bit_count() for subset in range(1<<a)
                                 if all(subset & row for row in rows))
        present = sum(row.bit_count() for row in rows)
        signed += multiplicity*(-1)**(a*b-present+(a+b)*c)*signed_independent**c
    return -signed  # The positive answer is the complement of the triangle-free one.


def three_by_three_columns():
    """All 512 fixed first banks, with optimal full-read cost on one six-bit column."""
    @lru_cache(maxsize=None)
    def minimum_pairs(unseen, live):
        if not live or live[0] == 0:
            return 0
        if unseen.bit_count() == 1:
            return 1
        bits = [1<<i for i in range(6) if unseen >> i & 1]
        if any(not any(bit & triangle for triangle in live) for bit in bits):
            return 0  # A correct policy can always omit this bit.
        costs = []
        for bit in bits:
            zero = tuple(tri for tri in live if not tri & bit)
            one = tuple(sorted({tri & ~bit for tri in live}))
            costs.append(minimum_pairs(unseen^bit, zero)+minimum_pairs(unseen^bit, one))
        return min(costs)

    ordinary, signed = Counter(), Counter()
    for rows in product(range(8), repeat=3):
        h = sum((-1)**s.bit_count() for s in range(8) if all(s & row for row in rows))
        edges = tuple(sorted((1<<i) | (1<<(j+3)) for i,j in product(range(3), repeat=2)
                             if rows[i] >> j & 1))
        assert minimum_pairs(63,edges) == abs(h)
        ordinary[h] += 1
        signed[h] += (-1)**(9-sum(row.bit_count() for row in rows))
    assert ordinary == {-1:7, 0:391, 1:108, 2:6}
    assert dict(signed) == {-1:7, 0:-19, 1:18, 2:-6}
    for c in (1,2,3,4,5,8,16,40,100):
        coefficient = 6*2**c-18-7*(-1)**c
        assert signed_closed_form(3,3,c) == coefficient
        upper = sum(count*abs(h)**c for h,count in ordinary.items())
        assert upper == 6*2**c+115 and abs(coefficient) <= upper <= abs(coefficient)+140
    return ordinary,signed


def chunks(n, width):
    return [list(range(start,min(start+width,n))) for start in range(0,n,width)]


if __name__ == '__main__':
    print(f'{count_audit()} rectangular dimensions checked modulo 2, 3, 5 and 7')
    for dims in [(1,1,1),(1,2,3),(2,2,2),(2,3,4),(3,3,3),(4,4,4)]:
        print(f'{dims}: negative, positive = {verdict_counts(*dims)}')
    offsets, positives, top = get_physical()
    print(f'{positives} positive physical files of 4096, full integer coefficient {top}')
    for dims in [(1,1,1),(1,2,3),(2,2,2),(2,2,3)]:
        a,b,c = dims
        n = a*b+b*c+c*a
        probes = [(f'packed-{width}', chunks(n,width)) for width in (1,2,4)]
        if dims == (2,2,2):
            physical = defaultdict(list)
            for e,offset in enumerate(offsets):
                physical[offset//32].append(e)
            probes.append(('physical-32-byte',list(physical.values())))
        for name,groups in probes:
            for greedy in (False,True):
                result = transcript_audit(dims,groups,greedy)
                print(f'{dims}, {name}, {"greedy" if greedy else "ordered"}: '
                      f'full NO, full YES, odd final cells = {result}')

    for copies in (1,2,3,5):
        for width in (1,2,4):
            print(f'OR of {copies} blocks, word {width}: signed, full (NO,YES), disjoint pairs, DAG states = '
                  f'{signed_or_audit(copies,chunks(12*copies,width))}')
    mixed = [[e,12+e] for e in range(12)]
    print(f'OR of 2 blocks, cross-block words: {signed_or_audit(2,mixed)}')

    for b,t,copies in ((3,2,2),(4,2,2),(4,3,3),(5,3,3)):
        groups = [[i*b+j for i in range(copies)] for j in range(b)]
        print(f'OR of {copies} threshold blocks ({b},{t}): signed, full (NO,YES), disjoint pairs, DAG states = '
              f'{signed_or_audit(copies,groups,(b,t))}')

    for b in range(1,9):
        for t in range(1,b+1):
            binomial = comb(b-1,t-1)
            _,full,pairs,_ = signed_or_audit(1,chunks(b,1),(b,t))
            assert full == (binomial,binomial) and pairs == binomial
    for k in (1,2,3,5):
        _,full,pairs,_ = signed_or_audit(k,chunks(12*k,1))
        assert full == (3**k,3**k) and pairs == 3**k
    assert [signed_closed_form(d,d,d) for d in range(1,4)] == [1,-3,37]
    print('All 36 one-block threshold cases b≤8 attain the exact bound; square top coefficients 1, −3, 37.')

    ordinary,signed = three_by_three_columns()
    print(f'All 512 three-by-three first banks: ordinary {dict(ordinary)}, signed {dict(signed)}; '
          'the six-bit optimum equals |I_G(−1)| in every case.')
