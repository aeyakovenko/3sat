"""Finite tests of the occurrence and lexical arguments for a parity face."""
from itertools import combinations, permutations, product


def compatible(triple, x):
    """Obligations on one positive witness, independently of the fixed clauses."""
    requirements = {}
    for b, pair in zip(x, triple):
        for val, needed in ((pair[b], True), (pair[1 - b], False)):
            name, sign = divmod(val, 2)
            bit = sign if needed else 1 - sign
            if name in requirements and requirements[name] != bit:
                return False
            requirements[name] = bit
    return True


def check_three_independent_tokens():
    # Signed literals on 4 possible variables. Try *all* injective signed
    # choices, also allowing a token to flip just the sign of its variable.
    bindings = list(permutations(range(8), 2))
    even = tuple(x for x in product(range(2), repeat=3) if sum(x) % 2 == 0)
    feasible = 0
    for triple in product(bindings, repeat=3):
        if all(compatible(triple, x) for x in even):
            domains = [{lit // 2 for lit in pair} for pair in triple]
            assert all(a.isdisjoint(b) for a, b in combinations(domains, 2))
            feasible += 1
    assert 0 < feasible < len(bindings) ** 3
    return len(bindings) ** 3, feasible


def runs(x):
    return sum(v and (i == 0 or not x[i - 1]) for i, v in enumerate(x))


def check_token_boundaries():
    # For every independent choice of byte whitespace statuses through length
    # nine, an invariant token count implies each optional endpoint has
    # one fixed nonwhite neighbor and one fixed white neighbor (sentinels legal).
    count = 0
    for n in range(1, 10):
        for pattern in product((0, 1, 2), repeat=n):
            choices = tuple(i for i, t in enumerate(pattern) if t == 2)
            if not choices:
                continue
            lo = list(pattern)
            for i in choices:
                lo[i] = 0
            # A vanishing discrete derivative is equivalent to constancy, and
            # we separately enumerate all corners before invoking the lemma.
            if any(runs(tuple(bits[choices.index(i)] if t == 2 else t
                              for i, t in enumerate(pattern))) != runs(lo)
                   for bits in product(range(2), repeat=len(choices))):
                continue
            edges = (0,) + pattern + (0,)
            for i in choices:
                assert {edges[i], edges[i + 2]} == {0, 1}
            count += 1
    return count


def canonical_files():
    # Full Hamming-one neighborhoods of all these canonical physical bodies.
    # Headers allow spare declared variables, so a change there can be valid
    # and irrelevant. Record names, separators, and signs are checked separately.
    variables = (1, 2, 3, 10)
    clauses = []
    for triple in combinations(variables, 3):
        for signs in product((1, -1), repeat=3):
            clauses.append(tuple(i * j for i, j in zip(triple, signs)))
    files = {}
    for one, two in product(clauses, repeat=2):
        body = b''
        digits = set()
        for c in (one, two):
            for lit in c:
                token = str(lit).encode()
                digits.update(range(len(body) + int(lit < 0), len(body) + len(token)))
                body += token + b' '
            body += b'0\n'
        files[body] = digits
    neighbors = 0
    for body, digits in files.items():
        for pos in range(len(body)):
            for bit in range(8):
                variant = body[:pos] + bytes([body[pos] ^ (1 << bit)]) + body[pos + 1:]
                if variant in files:
                    assert pos in digits and pos in files[variant]
                    neighbors += 1
    assert neighbors
    return len(files), neighbors


def main():
    maps, feasible = check_three_independent_tokens()
    patterns = check_token_boundaries()
    files, neighbors = canonical_files()
    print(f"{maps} signed choices, {feasible} satisfy every positive-witness test; "
          f"{patterns} nonconstant whitespace patterns of constant token count; "
          f"{files} canonical bodies and {neighbors} directed one-bit neighbors")


if __name__ == "__main__":
    main()
