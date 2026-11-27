"""Check exact primal and dual forecasts on finite vector spaces."""


def character(mask, word):
    return 1 - 2 * ((mask & word).bit_count() % 2)


def span(basis):
    result = {0}
    for row in basis:
        result |= {v ^ row for v in result}
    return result


def check_games():
    cases = 0
    for h in range(2, 10):
        q = 1 << h
        differences = range(1, q)
        weights = [max(0, y.bit_count() - 1) for y in range(q)]
        denominator = 1 + (h - 2) * (q // 2)
        assert sum(weights) == denominator
        for a in differences:
            score = sum(weights[y] * character(a, y) for y in differences)
            assert score == (1 if a.bit_count() >= 2 else 1 - q // 2)
            assert sum(character(a, y) == 1 for y in differences) == q // 2 - 1
            cases += 1
        for rank in range(1, h):
            excluded_span = span([1 << i for i in range(rank)])
            outside = sorted(set(differences) - excluded_span)
            for y in differences:
                success = sum(character(a, y) == 1 for a in outside)
                assert 2 * success <= len(outside)
                cases += 1
    return cases


def check_noncoordinate_bases():
    h = 3
    q = 1 << h
    cases = 0
    from itertools import permutations
    for basis in permutations(range(1, q), h):
        if len(span(basis)) < q:
            continue
        # Coordinates of y are its evaluations on the supplied primal basis.
        weights = [max(0, sum(character(a, y) == -1 for a in basis) - 1)
                   for y in range(q)]
        for a in set(range(1, q)) - set(basis):
            assert sum(weights[y] * character(a, y) for y in range(1, q)) == 1
        blocked = basis[0]
        permitted = [y for y in range(1, q) if character(blocked, y) == -1]
        for a in set(range(1, q)) - {blocked}:
            assert sum(character(a, y) for y in permitted) == 0
        cases += 1
    return cases


if __name__ == "__main__":
    print(f"Verified {check_games()} character and outside-span scores "
          f"and {check_noncoordinate_bases()} ordered bases.")
