"""Check every numerical/branch corner for small widths and both sharp promises."""
from itertools import product

from ramsey_dimacs_word_audit import calculate


def main():
    numerical = branches = files = 0
    for width in range(1, 12):
        original = calculate(0, 0, width)
        for alternative in range(1, 1 << width):
            corners = [calculate(x, y, width) for x, y in
                       ((0, alternative), (alternative, 0), (alternative, alternative))]
            for i, value in enumerate(original):
                assert any(result[i] == value or value == 0 and result[i] == alternative
                           for result in corners)
                numerical += 1
            for i in range(14, 20):
                assert original[i] == corners[-1][i]
                branches += 1
    for size in range(2, 13):
        for cells in product((0, 1), repeat=size):
            z = cells[1]
            x = cells[z]
            assert (x == 0 and all(v == 0 for v in cells[2:])) == (not any(cells))
            files += 1
    print(f'{numerical} opcode corners, {branches} diagonal comparisons, {files} complete files')


if __name__ == '__main__':
    main()
