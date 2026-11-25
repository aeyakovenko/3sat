"""Compare exact finite truth-table lookup with signature collisions and suites."""

from itertools import product


def main():
    tables = collision_cases = refutations = 0
    # Three possible outputs per program: timeout, NO, YES.
    # File 0 is the false fallback anchor; the remaining files can have any label.
    for cells in product((None, False, True), repeat=6):
        probes = (cells[:3], cells[3:])
        signatures = list(zip(*probes))
        keys = list(dict.fromkeys(signatures))
        for extra in product((False, True), repeat=2):
            labels = (False, *extra)
            for cutoff in range(4):
                tail = list(range(cutoff, 3))
                pairs = [(x, y) for x in tail for y in tail
                         if x < y and labels[x] != labels[y] and signatures[x] == signatures[y]]
                lookup = any(all(groups[keys.index(signatures[x])] == labels[x] for x in tail)
                             for groups in product((False, True), repeat=len(keys)))
                assert lookup == (not pairs)
                tables += 1
                for x, y in pairs:
                    # Append all behaviours of parameters already excluded at the anchor.
                    # They can be faster or give any verdict on the other two files.
                    candidates = list(probes)
                    for anchor in (None, True):
                        candidates.extend((anchor, *rest) for rest in product((None, False, True), repeat=2))
                    for run in candidates:
                        assert any(run[j] != labels[j] for j in (0,x,y))
                        refutations += 1
                    collision_cases += 1
    print(f'{tables} lookup/collision equivalences; {collision_cases} opposite pairs; '
          f'{refutations} three-file candidate refutations')


if __name__ == '__main__':
    main()
