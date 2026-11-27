"""Enumerate complete Boolean CSPs by shared dyadic prefix checks."""

from itertools import combinations, pairwise, product
from math import comb
from random import Random


def group_keys(keys, radix):
    """Stable integer radix sort, unique keys, and scatter labels in input order."""
    if not keys:
        return [], []
    order = list(range(len(keys)))
    for field in reversed(range(len(keys[0]))):
        highest = max(key[field] for key in keys)
        scale = 1
        while scale <= highest:
            counts = [0] * radix
            for idx in order:
                counts[(keys[idx][field] // scale) % radix] += 1
            offset = 0
            for digit, count in enumerate(counts):
                counts[digit] = offset
                offset += count
            placed = [0] * len(order)
            for idx in order:
                digit = (keys[idx][field] // scale) % radix
                placed[counts[digit]] = idx
                counts[digit] += 1
            order = placed
            scale *= radix
    distinct, labels = [], [0] * len(order)
    for idx in order:
        key = keys[idx]
        if not distinct or distinct[-1] != key:
            distinct.append(key)
        labels[idx] = len(distinct) - 1
    return distinct, labels


class PrefixForest:
    """Patterns are canonical at each fixed dyadic location."""

    def __init__(self, n):
        self.span = 1 << (max(1, n) - 1).bit_length()
        self.radix = max(2, self.span)
        self.children = [None, None]
        self.zero_root = 0
        for _ in range(self.span.bit_length() - 1):
            self.children.append((self.zero_root, self.zero_root))
            self.zero_root = len(self.children) - 1

    def change_new_bit(self, roots, at):
        """All previous patterns have zero at 'at'; the changed roots get one."""
        if not roots:
            return []
        siblings = []
        current = roots
        mask = self.span >> 1
        while mask:
            side = int(bool(at & mask))
            pairs = [self.children[node] for node in current]
            siblings.append((side, [pair[1 - side] for pair in pairs]))
            current = [pair[side] for pair in pairs]
            mask >>= 1
        assert all(leaf == 0 for leaf in current)
        changed = [1] * len(roots)
        for side, others in reversed(siblings):
            if side:
                pairs = list(zip(others, changed, strict=True))
            else:
                pairs = list(zip(changed, others, strict=True))
            distinct, labels = group_keys(pairs, self.radix)
            first = len(self.children)
            self.children.extend(distinct)
            changed = [first + label for label in labels]
        return changed

    def decode(self, root, n):
        frontier = [root]
        for _ in range(self.span.bit_length() - 1):
            frontier = [child for node in frontier for child in self.children[node]]
        return tuple(frontier[:n])


class ConstraintTable:
    """For every sorted k-set, an integer mask marks all forbidden tuples."""

    def __init__(self, n, k, masks, *, allow_missing=False):
        self.n, self.k = n, k
        self.complete = True
        self.table = [0] * max(n**k, 1)
        self.subsets = list(combinations(range(n), k))
        for variables, mask in zip(self.subsets, masks, strict=True):
            assert 0 <= mask < 1 << (1 << k)
            if not mask:
                assert allow_missing
                self.complete = False
            self.table[self.index(variables)] = mask

    def index(self, variables):
        key = 0
        for i in variables:
            key = key * self.n + i
        return key

    def forbidden_extensions(self, coords, bits, stage):
        if coords[-1] >= stage or any(x >= y for x, y in pairwise(coords)):
            return 0
        assignment = 0
        for bit in bits:
            assignment = 2 * assignment + bit
        mask = self.table[self.index((*coords, stage))]
        return (mask >> (2 * assignment)) & 3

    def reference(self):
        solutions = []
        for bits in product((0, 1), repeat=self.n):
            for subset in self.subsets:
                pattern = 0
                for coordinate in subset:
                    pattern = 2 * pattern + bits[coordinate]
                if (self.table[self.index(subset)] >> pattern) & 1:
                    break
            else:
                solutions.append(bits)
        return solutions


def forbidden_per_root(table, forest, roots, stage):
    """Build the quotient of one (k-1)-dimensional dyadic traversal level by level."""
    dim, width = table.k - 1, forest.span
    directions = tuple(product((0, 1), repeat=dim))
    keys, root_labels = group_keys([(0,) * dim + (root,) * dim for root in roots], forest.radix)
    links = []
    total_keys = 0
    while True:
        total_keys += len(keys)
        sites = (forest.span // width) ** dim
        union_size = min(dim * width, table.n)
        sauer = sum(comb(union_size, j) for j in range(min(dim, union_size) + 1))
        assert not table.complete or len(keys) <= sites * sauer
        if width == 1:
            break
        expanded = []
        for key in keys:
            locations, nodes = key[:dim], key[dim:]
            pairs = [forest.children[node] for node in nodes]
            for direction in directions:
                places = tuple(2 * pos + side for pos, side in zip(locations, direction, strict=True))
                ids = tuple(pair[side] for pair, side in zip(pairs, direction, strict=True))
                expanded.append(places + ids)
        keys, labels = group_keys(expanded, forest.radix)
        links.append(labels)
        width //= 2
    verdicts = [table.forbidden_extensions(key[:dim], key[dim:], stage) for key in keys]
    for labels in reversed(links):
        parent = []
        for start in range(0, len(labels), len(directions)):
            flags = 0
            for child in labels[start:start + len(directions)]:
                flags |= verdicts[child]
            parent.append(flags)
        verdicts = parent
    return [verdicts[label] for label in root_labels], total_keys


def solve(table):
    forest = PrefixForest(table.n)
    roots = [forest.zero_root]
    visited = 0
    for i in range(table.n):
        flags, used = forbidden_per_root(table, forest, roots, i)
        visited += used
        zero = [root for root, mask in zip(roots, flags, strict=True) if not (mask & 1)]
        one = [root for root, mask in zip(roots, flags, strict=True) if not (mask & 2)]
        roots = zero + forest.change_new_bit(one, i)
        assert len(roots) == len(set(roots))
        if not roots:
            break
    return [forest.decode(root, table.n) for root in roots], visited


def solve_partial_triples(n, masks_by_triple, order=None):
    """Original-keyed forbidden masks, new-to-old variable order, missing is unconstrained."""
    order = tuple(range(n)) if order is None else tuple(order)
    if sorted(order) != list(range(n)):
        raise ValueError('expected a variable permutation')
    masks = []
    for new in combinations(range(n), 3):
        old = [order[i] for i in new]
        original = masks_by_triple.get(tuple(sorted(old)), 0)
        indices = sorted(range(3), key=old.__getitem__)
        mask = 0
        for code, bits in enumerate(product((0, 1), repeat=3)):
            recoded = 4 * bits[indices[0]] + 2 * bits[indices[1]] + bits[indices[2]]
            mask |= ((original >> recoded) & 1) << code
        masks.append(mask)
    found, visited = solve(ConstraintTable(n, 3, masks, allow_missing=True))
    inverse = [order.index(i) for i in range(n)]
    return [tuple(row[i] for i in inverse) for row in found], visited


def solve_complete_dimacs(data, k=3, *, enumerator=solve):
    """Read canonical decimal names in physical file order, including long names."""
    trie = [[-1] * 10]
    names_at = [-1]
    names = []
    maximum = None
    declared = 0
    rows = []
    pending = []

    def intern(raw):
        if not raw or raw[0] == ord('0') or not raw.isdigit():
            raise ValueError('invalid variable name')
        if len(raw) > len(maximum) or (len(raw) == len(maximum) and raw > maximum):
            raise ValueError('literal exceeds the header bound')
        node = 0
        for digit in raw:
            slot = digit - ord('0')
            following = trie[node][slot]
            if following == -1:
                following = len(trie)
                trie[node][slot] = following
                trie.append([-1] * 10)
                names_at.append(-1)
            node = following
        if names_at[node] == -1:
            names_at[node] = len(names)
            names.append(raw)
        return names_at[node]

    for physical_line in data.splitlines():
        line = physical_line.strip()
        if not line or line.startswith(b'c'):
            continue
        tokens = line.split()
        if tokens[0] == b'p':
            if maximum is not None or len(tokens) != 4 or tokens[:2] != [b'p', b'cnf']:
                raise ValueError('invalid or repeated header')
            for number in tokens[2:]:
                if not number.isdigit() or (len(number) > 1 and number.startswith(b'0')):
                    raise ValueError('invalid DIMACS header counter')
            maximum = tokens[2]
            for digit in tokens[3]:
                declared = min(len(data) + 1, 10 * declared + digit - ord('0'))
            continue
        if maximum is None:
            raise ValueError('missing DIMACS header')
        for token in tokens:
            if token == b'0':
                if len(pending) != k or len({var for var, _ in pending}) != k:
                    raise ValueError('clause must use k distinct variables')
                pending.sort()
                pattern = 0
                for _, negative in pending:
                    pattern = 2 * pattern + negative
                rows.append((tuple(var for var, _ in pending), 1 << pattern))
                pending = []
            else:
                if len(pending) == k:
                    raise ValueError('wrong clause width')
                negative = token.startswith(b'-')
                pending.append((intern(token[1:] if negative else token), int(negative)))
    if maximum is None or pending or declared != len(rows):
        raise ValueError('incomplete DIMACS input')
    n = len(names)
    if comb(n, k) != len(rows):
        raise ValueError('the variable support is incomplete')
    table = ConstraintTable(n, k, [1] * len(rows))
    table.table = [0] * max(n**k, 1)
    for coords, mask in rows:
        key = table.index(coords)
        if table.table[key]:
            raise ValueError('duplicate variable support')
        table.table[key] = mask
    solutions, used = enumerator(table)
    return names, solutions, used


def audit_dimacs():
    names = [b'37', b'9', b'8' * 90, b'887', b'9142', b'21']
    clauses = []
    for a, b, c in reversed(list(combinations(names, 3))):
        clauses.append(b'-' + b' -'.join([c, a, b]) + b' 0')
    data = (b'c complete triple masks\np cnf ' + b'9' * 90 + b' 20\n'
            + b'  '.join(clauses[:10]) + b'\nc midpoint\n' + b'\n'.join(clauses[10:]) + b'\n')
    ordering, found, _ = solve_complete_dimacs(data)
    assert sorted(ordering) == sorted(names)
    assert sorted(found) == sorted(bits for bits in product((0, 1), repeat=6) if sum(bits) <= 2)
    for invalid in (data.replace(b'20\n', b'19\n'), data.replace(clauses[0], clauses[3]),
                    data.replace(b' -21 ', b' -0 '), data.replace(b'p cnf', b'p cnz')):
        try:
            solve_complete_dimacs(invalid)
        except ValueError:
            continue
        raise AssertionError('invalid complete DIMACS accepted')
    print('physical DIMACS syntax, shuffled signed clauses, long names, and invalid supports passed')


def audit():
    rng = Random(20261127)
    count = states = solutions = unsatisfiable = 0

    def check(table):
        nonlocal count, states, solutions, unsatisfiable
        found, used = solve(table)
        assert sorted(found) == table.reference()
        count += 1
        states += used
        solutions += len(found)
        unsatisfiable += not found

    # Every choice of one clause on each triple of four variables.
    for masks in product(range(8), repeat=4):
        check(ConstraintTable(4, 3, [1 << val for val in masks]))
    # Every set of nontrivial binary relations on three variables.
    for masks in product(range(1, 16), repeat=3):
        check(ConstraintTable(3, 2, masks))
    for k in (2, 3, 4):
        for n in range(1, 10):
            m = comb(n, k)
            # All-ones blocker realizes the full Sauer bound.
            check(ConstraintTable(n, k, [1 << ((1 << k) - 1)] * m))
            for _ in range(4):
                check(ConstraintTable(n, k, [rng.randrange(1, 1 << (1 << k)) for _ in range(m)]))
            for _ in range(4):
                check(ConstraintTable(n, k, [1 << rng.randrange(1 << k) for _ in range(m)]))
    for n in (4, 5, 7):
        original = {s: rng.randrange(1, 256) for s in combinations(range(n), 3) if rng.randrange(2)}
        order = list(range(n))
        rng.shuffle(order)
        pairs, _ = solve_partial_triples(n, original, order)
        reference = ConstraintTable(n, 3, [original.get(s, 0) for s in combinations(range(n), 3)],
                                    allow_missing=True).reference()
        assert sorted(pairs) == reference
    print(f'{count} complete instances, {states} dyadic keys, {solutions} solutions, '
          f'{unsatisfiable} unsatisfiable instances; every final assignment agrees with brute force')


if __name__ == '__main__':
    audit_dimacs()
    audit()
