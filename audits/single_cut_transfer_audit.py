"""Finite checks for a single matching carrying pivotal bits across a SAT run."""

from itertools import permutations, product


def instance(pi, payloads, middle, answer, source_order=False):
    m = len(pi)
    clauses = []
    largest = 2 * m

    def new_variable():
        nonlocal largest
        largest += 1
        return largest

    def pin(variable, bit):
        signed = variable if bit else -variable
        clauses.append((signed,) * 3)

    def xor(left, right):
        out = new_variable()
        for a, b, c in product(range(2), repeat=3):
            if c != a ^ b:
                clauses.append(tuple(-v if value else v for v, value in
                                     zip((left, right, out), (a, b, c))))
        return out

    def lane(key, index):
        return 1 + 2 * key + index

    locations = range(m) if source_order else pi
    for key, word in zip(locations, payloads):
        for index in range(2):
            pin(lane(key, index), (word >> index) & 1)

    selected = []
    if source_order:
        selectors = [new_variable() for _ in range(m)]
        for j, var in enumerate(selectors):
            pin(var, j % 2)
        for i, key in enumerate(pi):
            chosen = new_variable()
            selector = selectors[key]
            x, y = lane(i, 0), lane(i, 1)
            clauses.extend(((selector, -x, chosen), (selector, x, -chosen),
                            (-selector, -y, chosen), (-selector, y, -chosen)))
            selected.append(chosen)
    else:
        selected = [lane(j, j % 2) for j in range(m)]

    acc = new_variable()
    pin(acc, 0)
    for bit in middle:
        var = new_variable()
        pin(var, bit)
        acc = xor(acc, var)
    for choice in selected:
        acc = xor(acc, choice)
    pin(acc, answer)
    return clauses, largest


def unit_models(cnf, variables):
    """These pinned equivalence chains propagate completely or conflict."""
    fixed = set()
    while True:
        old = len(fixed)
        for clause in cnf:
            if any(lit in fixed for lit in clause):
                continue
            available = {lit for lit in clause if -lit not in fixed}
            if not available:
                return 0
            if len(available) == 1:
                fixed.update(available)
        if len(fixed) == old:
            break
    assert len(fixed) == variables
    assert all(any(lit in fixed for lit in clause) for clause in cnf)
    return 1


def scan(pi, payloads, middle):
    table = [None] * len(pi)
    for j, v in zip(pi, payloads):
        table[j] = v
    if None in table:
        return None
    selected = sum((v >> (j % 2)) & 1 for j, v in enumerate(table))
    return (sum(middle) + selected) % 2


def check_formulas():
    checked = 0
    for m in (1, 2):
        for pi in permutations(range(m)):
            for data in product(range(4), repeat=m):
                for middle in product(range(2), repeat=2*m):
                    expected = scan(pi, data, middle)
                    for c in (0, 1):
                        assert unit_models(*instance(pi, data, middle, c)) == (c == expected)
                        checked += 1
                    for i, key in enumerate(pi):
                        changed = list(data)
                        changed[i] ^= 1 << (key % 2)
                        assert scan(pi, changed, middle) == 1 - expected
                    for i in range(2*m):
                        changed = list(middle)
                        changed[i] ^= 1
                        assert scan(pi, data, changed) == 1 - expected
    for m in (1, 2):
        for mapping in product(range(m), repeat=m):
            for data in product(range(4), repeat=m):
                for middle in product(range(2), repeat=2*m):
                    selected = sum((v >> (key % 2)) & 1 for key, v in zip(mapping, data))
                    fast_answer = (sum(middle) + selected) % 2
                    scattered = scan(mapping, data, middle)
                    assert scattered is None or scattered == fast_answer
                    for c in (0, 1):
                        assert unit_models(*instance(mapping, data, middle, c, True)) == (c == fast_answer)
                        checked += 1
    return checked


def intervals(mask):
    return (mask & ~(mask << 1)).bit_count()


def max_empty_intersection(pi, runs, erasures):
    """Largest min(side sizes) of an empty rectangle after erasures."""
    m = len(pi)
    masks = [v for v in range(1 << m) if intervals(v) <= runs]
    images = {u:sum(1 << pi[i] for i in range(m) if u & (1 << i))
              for u in masks}
    return max(min(u.bit_count(), v.bit_count()) for u in masks for v in masks
               if (images[u] & v).bit_count() <= erasures)


def check_cuts():
    """Enumerate balanced colored cuts and compare their cross rectangles."""
    tested = 0
    for m in (2, 3, 4):
        for pi in permutations(range(m)):
            emptiness = {(runs, lost):max_empty_intersection(pi, runs, lost)
                         for runs in (1, 2) for lost in range(m + 1)}
            # Each endpoint is red, blue or removed. Compress each color to
            # its masks on the two halves and count actual crossing edges.
            for color in product(range(3), repeat=2*m):
                if color.count(2) > m//4:
                    continue
                sizes = [color.count(bit) for bit in (0, 1)]
                if min(sizes)*3 < m:
                    continue
                masks = [[sum(1 << i for i in range(m) if color[k*m+i] == b)
                          for b in (0, 1)] for k in range(2)]
                runs = max(intervals(u) for row in masks for u in row)
                cross = sum(color[i] != color[m+pi[i]] and
                            color[i] != 2 and color[m+pi[i]] != 2
                            for i in range(m))
                rect = max(min(masks[0][b].bit_count(),
                               masks[1][1-b].bit_count()) for b in (0, 1))
                assert rect * 6 >= m
                assert emptiness[runs, cross] >= rect
                tested += 1
    return tested


def check_fresh_offers():
    """Check exact expected stake for adaptive lookups with past disclosures."""
    m = 4
    tested = 0
    for pi in permutations(range(m)):
        inv = {y:x for x, y in enumerate(pi)}
        for mode in range(8):
            total = 0
            for words in product(range(4), repeat=m):
                seen = set()
                history = mode
                stake = 1
                for y in range(m):
                    probe = (y + history + mode) % m
                    seen.add(probe)
                    guess = (words[probe] + history + mode) % 4
                    i = inv[y]
                    offer = (pi[probe] + history) % 3 != 0
                    if offer and i not in seen:
                        stake = 4 * stake if guess == words[i] else 0
                    history = (history + i + words[i]) % 7
                total += stake
                tested += 1
            assert total == 4 ** m
    return tested


if __name__ == '__main__':
    print(f'{check_formulas()} fully propagated 3-CNFs and their pin flips; '
          f'{check_cuts()} colored crossing cuts; '
          f'{check_fresh_offers()} adaptive offer trajectories')
