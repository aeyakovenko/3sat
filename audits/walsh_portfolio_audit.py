"""Finite portfolio, ordinary 3-CNF, and native stage-accounting checks."""

from itertools import product
from random import Random


def parity(a, x):
    return (a & x).bit_count() % 2


def forecast(report, x, pin):
    return (report >> (2*x + pin)) & 1


def spectrum(report, size):
    # Score twice the pin-averaged proposed checksum sign.
    scores = [2*(forecast(report, x, 0) - forecast(report, x, 1))
              for x in range(size)]
    initial_energy = sum(value*value for value in scores)
    step = 1
    while step < size:
        for start in range(0, size, 2*step):
            for j in range(start, start+step):
                u, v = scores[j], scores[j+step]
                scores[j], scores[j+step] = u+v, u-v
        step *= 2
    assert sum(value*value for value in scores) == size*initial_energy <= 4*size**2
    return scores


def actual_signed_agreement(report, a, size):
    correct = sum(forecast(report, x, pin) == (parity(a, x) == pin)
                  for x in range(size) for pin in (0, 1))
    return 2*correct - 2*size


def select(spectra, weights, size):
    costs = [sum(weight * coeff[a]**2 for weight, coeff in zip(weights, spectra, strict=True))
             for a in range(size)]
    a = min(range(size), key=costs.__getitem__)
    assert costs[a] <= 4*size*sum(weights)
    assert all(weight*coeff[a]**2 <= 4*size*sum(weights)
               for weight, coeff in zip(weights, spectra, strict=True))
    return a


def portfolio_checks():
    size = 4
    cols = [spectrum(report, size) for report in range(1 << (2*size))]
    for report, row in enumerate(cols):
        assert row == [actual_signed_agreement(report, a, size) for a in range(size)]
    for c1, c2 in product(cols, repeat=2):
        select((c1,c2), (1,1), size)
    rng = Random(17171)
    weighted = 0
    for _ in range(500):
        size = 1 << rng.randrange(8)
        reports = [rng.getrandbits(2*size) for _ in range(rng.randrange(9))]
        weights = [1 << rng.randrange(7) for _ in reports]
        a = select([spectrum(r, size) for r in reports], weights, size)
        assert all(w * actual_signed_agreement(r, a, size)**2 <= 4*size*sum(weights)
                   for r, w in zip(reports, weights, strict=True))
        weighted += 1
    return len(cols)**2, weighted


class ClauseList:
    """Signed literals, with an exact three-variable or shorter mux relation."""
    def __init__(self):
        self.n = 0
        self.one = self.var()
        self.clauses = [(self.one,)]
        self.muxes = {}

    def var(self):
        self.n += 1
        return self.n

    def mux(self, selector, zero, one):
        if zero == one:
            return one
        if (zero, one) == (-self.one, self.one):
            return selector
        if (zero, one) == (self.one, -self.one):
            return -selector
        key = (selector, zero, one)
        if key not in self.muxes:
            out = self.var()
            self.clauses.extend([(selector, -zero, out), (selector, zero, -out),
                                 (-selector, -one, out), (-selector, one, -out)])
            self.muxes[key] = out
        return self.muxes[key]

    def lookup(self, inputs, bits):
        table = [self.one if bit else -self.one for bit in bits]
        for selector in inputs:
            table = [self.mux(selector, table[i], table[i+1]) for i in range(0, len(table), 2)]
        assert len(table) == 1
        return table[0]


def finite_formula(arity, reporters):
    # The closed-table computation uses an exhaustive ROM on the raw report
    # bits for these small cases, avoiding dependence on a particular RAM
    # simulator implementation. The ROM entries use direct SAT agreement.
    cnf = ClauseList()
    size = 1 << arity
    report_bits = [cnf.var() for _ in range(2*size*reporters)]
    public_x = [cnf.var() for _ in range(arity)]
    pin = cnf.var()
    chosen = []
    for encoded in range(1 << len(report_bits)):
        reports = [(encoded >> (2*size*i)) & ((1 << (2*size)) - 1) for i in range(reporters)]
        costs = [sum(actual_signed_agreement(r, a, size)**2 for r in reports)
                 for a in range(size)]
        chosen.append(min(range(size), key=costs.__getitem__))
    frequency = [cnf.lookup(report_bits, [(a >> i) & 1 for a in chosen]) for i in range(arity)]
    dot = -cnf.one
    for a, x in zip(frequency, public_x, strict=True):
        term = cnf.mux(a, -cnf.one, x)
        dot = cnf.mux(term, dot, -dot)
    cnf.clauses += [(-dot, pin), (dot, -pin)]
    assert all(1 <= len(c) <= 3 for c in cnf.clauses)
    return cnf, report_bits, public_x, pin


def solve_pinned(cnf, inputs):
    # Inputs fix every mux output by unit propagation. On SAT draws this also
    # checks that all declared variables, including all hidden ROM gates, are
    # forced; on UNSAT draws it returns only after an actual clause conflict.
    values = dict(inputs)
    while True:
        before = len(values)
        for clause in cnf.clauses:
            unknown = []
            for literal in clause:
                bit = values.get(abs(literal))
                if bit is None:
                    unknown.append(literal)
                elif bit == (literal > 0):
                    break
            else:
                if not unknown:
                    return False
                if len(unknown) == 1:
                    lit = unknown[0]
                    values[abs(lit)] = lit > 0
        if len(values) == before:
            assert len(values) == cnf.n
            return True


def cnf_checks():
    cases = positives = 0
    for arity, reporters in [(1,1), (1,2), (2,1)]:
        cnf, bits, public_x, terminal = finite_formula(arity, reporters)
        size = 1 << arity
        for encoded in range(1 << len(bits)):
            words = [(encoded >> (2*size*i)) & ((1 << (2*size))-1) for i in range(reporters)]
            a = select([spectrum(r, size) for r in words], [1]*reporters, size)
            base = {var: (encoded >> i) & 1 for i, var in enumerate(bits)}
            for x in range(size):
                x_bits = {var: (x >> i) & 1 for i, var in enumerate(public_x)}
                verdicts = [solve_pinned(cnf, base | x_bits | {terminal: pin}) for pin in (0,1)]
                assert verdicts == [parity(a,x) == pin for pin in (0,1)]
                cases += 2
                positives += sum(verdicts)
    assert positives*2 == cases
    return cases


def stage_bounds():
    checks = 0
    for a_param in range(1, 6):
        for j in (16,32,64,128,256,512,1024,2048):
            h = (2*a_param+3)*(j+1).bit_length()  # ceil(log2(j+2))
            n = 1 << h
            clock = 1 << j
            # Even the larger envelope of two (j+1)-sized collections per
            # reporter suffices for the elementary bias calculation.
            cap = 2*(j+1)**2
            assert (j+1)**(2*a_param) * cap < n
            assert sum(clock >> (i+1) for i in range(j+1)) < clock
            if j >= 512:
                work = cap*n*(h+1)
                largest_cost = 4*cap*n*n
                assert work < clock // (j+1) and largest_cost.bit_length() < j
            checks += 1
    return checks


if __name__ == "__main__":
    plain, weighted = portfolio_checks()
    print(f"{plain:,} exhaustive two-reporter portfolios; {weighted} weighted portfolios")
    print(f"{cnf_checks():,} pinned explicit width-three formulas, exactly half uniquely satisfiable")
    print(f"{stage_bounds()} stage/bias budgets, including integer Walsh accumulator sizes")
