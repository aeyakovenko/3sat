"""Exact finite tests of the mask, its physical CNF, and the parity challenge bound."""

from fractions import Fraction
from itertools import combinations
from math import comb

def subset_xors(columns):
    possible = {0}
    for column in columns:
        possible |= {value ^ column for value in possible}
    return possible


def spectrum(r, copies):
    orders = list(range(1, 1 << r)) * copies
    q = 1 << r
    best = [len(orders) + 1] * q
    for unread in range(1 << len(orders)):
        cols = [column for j, column in enumerate(orders) if unread >> j & 1]
        forbidden = q - len(subset_xors(cols))
        cost = len(orders) - len(cols)
        best[forbidden] = min(best[forbidden], cost)
    for m in range(q - 2, 0, -1):
        best[m] = min(best[m], best[m + 1])
    for m in range(1, q):
        possible_dim = (q - m).bit_length() - 1
        assert best[m] == copies * (q - (1 << possible_dim))
    return q - 1


def parity_challenges(d, q):
    """Enumerate subsets of the wrong parity representable by a width-q CNF."""
    even = [x for x in range(1 << d) if x.bit_count() % 2 == 0]
    masks = [m for m in range(1 << d) if m.bit_count() <= q]
    full = (1 << len(even)) - 1
    regions = []
    for region in range(1, full + 1):
        points = {x for j, x in enumerate(even) if region >> j & 1}
        allowed = {m: {x & m for x in points} for m in masks}
        closure = {x for x in range(1 << d) if all(x & m in allowed[m] for m in masks)}
        if closure == points:
            regions.append(region)
    counts = [full + 1] * (full + 1)
    counts[0] = 0
    for covered in range(full + 1):
        for region in regions:
            merged = covered | region
            counts[merged] = min(counts[merged], counts[covered] + 1)
    assert (counts[full] - 1).bit_length() == (d+q-1)//q - 1
    return len(regions)


class Circuit:
    def __init__(self):
        self.clauses = []
        self.n = 0

    def var(self):
        self.n += 1
        return self.n

    def xor(self, a, b):
        c = self.var()
        self.clauses.extend([(a, b, -c), (-a, -b, -c), (a, -b, c), (-a, b, c)])
        return c

    def fold(self, entries, zero):
        if not entries:
            return zero
        acc = entries[0]
        for entry in entries[1:]:
            acc = self.xor(acc, entry)
        return acc


def unit_models(clauses, n):
    # All wires must be forced on these fully pinned acyclic test circuits.
    values = {}
    while True:
        old_count = len(values)
        for clause in clauses:
            if any(values.get(abs(lit)) == (lit > 0) for lit in clause):
                continue
            unknown = [lit for lit in clause if abs(lit) not in values]
            if not unknown:
                return 0
            if len(set(unknown)) == 1:
                lit = unknown[0]
                values[abs(lit)] = lit > 0
        if old_count == len(values):
            assert len(values) == n
            return 1


def physical(r, copies):
    q = 1 << r
    circuit = Circuit()
    zero = circuit.var()
    circuit.clauses.append((-zero,))
    pins = [[circuit.var() for _ in range(copies)] for _ in range(q-1)]
    table = [zero] + [circuit.fold(group, zero) for group in pins]
    out = []
    for _ in range(r):
        half = len(table)//2
        out.append(circuit.fold(table[half:], zero))
        table = [circuit.xor(a,b) for a,b in zip(table[:half], table[half:])]
    out.reverse()
    # Small cases use a single width-r inequality, r<=3.
    checks = 0
    columns = [v for v in range(1,q) for _ in range(copies)]
    flat = [pin for group in pins for pin in group]
    for mask in range(1 << len(flat)):
        fixed = [(pin if mask >> j & 1 else -pin,) for j,pin in enumerate(flat)]
        syndrome = 0
        for j, value in enumerate(columns):
            if mask >> j & 1:
                syndrome ^= value
        for offset in range(q):
            for name in range(q):
                ref = offset ^ name
                inequality = tuple(-bit if ref >> j & 1 else bit for j,bit in enumerate(out))
                legal = unit_models(circuit.clauses + fixed + [inequality], circuit.n)
                assert legal == ((syndrome ^ offset) != name)
                checks += 1
    return checks


def sampled_error(d, menu_size):
    cases = 0
    for b in range(d+1):
        worst = max(Fraction(comb(d-errors,b) if d-errors >= b else 0,
                             menu_size * comb(d,b)) for errors in range(1,d+1,2))
        assert worst == Fraction(d-b, d * menu_size)
        if b and d % b == 0:
            blocks = d//b
            worst = max(Fraction(blocks-errors, blocks*menu_size)
                        for errors in range(1,blocks+1,2))
            assert worst == Fraction(d-b,d*menu_size)
        cases += 1
    return cases


if __name__ == '__main__':
    spectra = sum(spectrum(r,c) for r,c in [(2,1),(2,3),(3,1),(3,2),(4,1)])
    regions = sum(parity_challenges(d,q) for d in range(1,5) for q in range(1,d+1))
    checks = sum(physical(r,c) for r,c in [(2,1),(2,2),(3,1)])
    risks = sum(sampled_error(d,k) for d in range(1,13) for k in range(2,8))
    print(f"{spectra} sharp exclusion counts, {regions} CNF regions in exact parity covers, "
          f"{checks} fully propagated CNF pins and {risks} statistical error bounds.")
