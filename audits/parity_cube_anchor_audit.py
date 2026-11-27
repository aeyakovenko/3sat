"""Check the two fixed parity classifiers on actual DIMACS cubes and anchors."""

from itertools import product

from anchored_literal_census_audit import anchor
from one_byte_dense_successor_audit import clause, encode, parse
from selector_parity_cube_audit import minimum, padding, physical_template, truth


CONTRADICTION = set(product((1, -1), (2, -2), (3, -3)))


def guarded_predictions(raw):
    # The fixture is canonical. The proof uses a token-based implementation
    # of the same guard for valid noncanonical input as well.
    if CONTRADICTION <= parse(raw):
        return False, False
    parity = bool(sum(byte.bit_count() for byte in raw) % 2)
    return parity, not parity


def main():
    yes = {clause(1, 2, 3)}
    for count in (3, 6, 9, 15):
        assert guarded_predictions(anchor(count)) == (False, False)
    checks = blocks = 0
    for dimension in (1, 2, 3, 4):
        for sources in ((yes, CONTRADICTION), (CONTRADICTION, yes)):
            fixed, selectors, v = physical_template(*sources, dimension, h=4)
            count = len(fixed) + dimension
            start = minimum(v, count, 25) + 2
            orientations = {}
            for delta in range(4):
                extra = padding(v, count, start + delta)
                fits = {0, 1}
                for mask in product((0, 1), repeat=dimension):
                    tags = {clause(p, q, (a,b)[bit])
                            for (p,q,a,b), bit in zip(selectors, mask)}
                    rows = fixed | tags | extra
                    raw = encode(rows)
                    result = truth(rows)
                    preds = guarded_predictions(raw)
                    fits &= {i for i, got in enumerate(preds) if got == result}
                    checks += 1
                assert len(fits) == 1 and len(raw) % 4 not in orientations
                orientations[len(raw) % 4] = next(iter(fits))
                blocks += 1
            assert len(orientations) == 4
    print(f'{checks} physical SAT/UNSAT corners, {blocks} whole cubes fit, four explicit anchors')


if __name__ == '__main__':
    main()
