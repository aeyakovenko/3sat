"""Small exhaustive checks for the Hamming spheres around a neutral SAT batch."""

from functools import cache
from itertools import product
from math import comb


def query_tree_check():
    # Three independent components with word-probe depths 1, 1 and 2.
    def parts(x):
        return (x & 1, (x >> 1) & 1, ((x >> 2) & 3) == 3)

    @cache
    def profiles(points, available):
        """All depth vectors of trees pruned at constant-answer subdomains."""
        if len({any(parts(x)) for x in points}) == 1:
            return {(0,) * len(points)}
        result = set()
        for i in available:
            left = tuple(x for x in points if not x & (1 << i))
            right = tuple(x for x in points if x & (1 << i))
            rest = tuple(j for j in available if j != i)
            for lcost, rcost in product(profiles(left, rest), profiles(right, rest)):
                costs = dict(zip(left, lcost))
                costs.update(zip(right, rcost))
                result.add(tuple(costs[x] + 1 for x in points))
        return result

    all_profiles = profiles(tuple(range(16)), tuple(range(4)))
    # The neutral pair in the final AND can be 00, 01 or 10.
    boxes = [[(i & 3) | ((3 if i & 4 else neutral) << 2) for i in range(8)]
             for neutral in range(3)]
    predicted = (4, 7, 4, 1)
    minima = [float("inf")] * 4
    for costs in all_profiles:
        spectra = [[sum(costs[x] for i, x in enumerate(box) if i.bit_count() == s)
                    for s in range(4)] for box in boxes]
        assert any(all(got >= want for got, want in zip(spec, predicted)) for spec in spectra)
        for s in range(4):
            minima[s] = min(minima[s], max(spec[s] for spec in spectra))
    assert tuple(minima) == predicted
    print(f"{len(all_profiles)} reduced query-depth profiles; sphere optima {tuple(minima)}")


def chain_file(k, active):
    pads = (1, 4, 5)
    rows = [tuple(s * v for s, v in zip(signs, pads))
            for signs in product((-1, 1), repeat=3) if signs != (1, 1, 1)]
    rows.extend([(-2, 1, 4), (3, 1, 4), (6, 1, 4), (-(6 + k), 1, 4)])
    prefix = f"p cnf {6+k} {len(rows)+k}\n" + "".join(f"{a} {b} {c} 0\n" for a, b, c in rows)
    gap = " " * (8 * (k + 2).bit_length())
    body = "".join(f"{-(6+i)} {7+i} {2+((active >> i) & 1)} 0{gap}\n" for i in range(k))
    return (prefix + body).encode("ascii")


def model_exists(data):
    header, *clauses = data.splitlines()
    variables, count = map(int, header.split()[2:])
    assert len(clauses) == count
    masks = []
    for clause in clauses:
        a, b, c, end = map(int, clause.split())
        assert end == 0 and len({abs(a), abs(b), abs(c)}) == 3
        pos = sum(1 << (lit - 1) for lit in (a, b, c) if lit > 0)
        neg = sum(1 << (-lit - 1) for lit in (a, b, c) if lit < 0)
        masks.append((pos | neg, neg))
    return any(all((x & cols) != forbidden for cols, forbidden in masks)
               for x in range(1 << variables))


def physical_check():
    files = 0
    for k in range(1, 6):
        base = chain_file(k, 0)
        width = 16 * (((len(base) * 8 + 1).bit_length() + 15) // 16)
        changed_words = []
        for i in range(k):
            alt = chain_file(k, 1 << i)
            differences = [j for j, (a, b) in enumerate(zip(base, alt)) if a != b]
            assert len(base) == len(alt) and len(differences) == 1
            j = differences[0]
            assert (base[j] ^ alt[j]) == 1
            changed_words.append((8 * j) // width)
        assert len(set(changed_words)) == k
        time_by_sphere = [0] * (k + 1)
        for mask in range(1 << k):
            assert model_exists(chain_file(k, mask)) == bool(mask)
            # A sequential flag probe stops at its first positive block.
            charged = (mask & -mask).bit_length() if mask else k
            time_by_sphere[mask.bit_count()] += charged
            files += 1
        assert time_by_sphere == [k] + [comb(k + 1, s + 1) for s in range(1, k + 1)]
    print(f"{files} proper chain files; all source bits in separate native words")


if __name__ == "__main__":
    query_tree_check()
    physical_check()
