"""Check local XOR-selector suites on all small feature assignments."""

from itertools import product


class Ledger:
    def __init__(self):
        self.rows = {}

    def reduce(self, row):
        label = 0
        for pos in sorted(self.rows, reverse=True):
            if row >> pos & 1:
                pivot, bit = self.rows[pos]
                row ^= pivot
                label ^= bit
        return row, label

    def predict(self, row):
        remainder, label = self.reduce(row)
        assert remainder == 0
        return label

    def insert(self, remainder, bit):
        pos = remainder.bit_length() - 1
        assert pos >= 0 and pos not in self.rows
        self.rows[pos] = remainder, bit


def local_value(gate, child_prediction):
    if isinstance(gate, int):
        return gate
    left, right = gate
    return child_prediction(left) | child_prediction(right)


def pivot_suite(gates, rows):
    ledger = Ledger()
    suite = []
    for i, (gate, row) in enumerate(zip(gates, rows, strict=True)):
        label = local_value(gate, lambda j: ledger.predict(rows[j]))
        remainder, predicted = ledger.reduce(row)
        if remainder:
            ledger.insert(remainder, label ^ predicted)
            suite.append(i)
        elif predicted != label:
            return suite + [i], False
    return suite, True


def failed_roots(mask, gates, rows):
    bits = [(mask & row).bit_count() % 2 for row in rows]
    return {
        i for i, gate in enumerate(gates)
        if bits[i] != local_value(gate, bits.__getitem__)
    }


def exhaust():
    gates = (0, 1, (0, 1), (0, 2), (2, 3))
    for k in (1, 2, 3):
        consistent = total = 0
        for rows in product(range(1 << k), repeat=len(gates)):
            suite, fits = pivot_suite(gates, rows)
            selected = set(suite)
            answers = []
            for mask in range(1 << k):
                failed = failed_roots(mask, gates, rows)
                assert (not failed) == failed.isdisjoint(selected)
                answers.append(not failed)
            assert any(answers) == fits
            assert len(suite) <= k + int(not fits)
            consistent += fits
            total += 1
        print(f"k={k}: {total} assignments, {consistent} consistent")


def necessity():
    for k in range(1, 9):
        gates = [1] + [(0, 0)] * k
        rows = [1] + [1 ^ (1 << j) ^ (1 << (j + 1)) for j in range(k - 1)]
        rows.append(1 ^ (1 << (k - 1)))
        suite, fits = pivot_suite(gates, rows)
        assert not fits and len(suite) == k + 1
        failures = [failed_roots(mask, gates, rows) for mask in range(1 << k)]
        assert all(failures)
        assert all({i} in failures for i in range(k + 1))
    print("k=1 through 8: each of k+1 tautology roots is individually necessary")


if __name__ == "__main__":
    exhaust()
    necessity()
