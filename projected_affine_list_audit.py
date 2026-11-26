"""Existential projection of binary affine-guard, affine-leaf decision lists.

Run: python projected_affine_list_audit.py

A form is a nonnegative integer mask. Bit 0 is its constant. Bit i+1 is
the coefficient on coordinate i. Public coordinates precede hidden ones.
A row (g, h) returns h when g=0, and otherwise continues to the next row.
The last answer is an affine form. No dependency beyond Python's stdlib.
"""

from dataclasses import dataclass
from itertools import product
from random import Random


def bit(form, assignment):
    return (form & (2 * assignment + 1)).bit_count() % 2


@dataclass(frozen=True)
class DecisionList:
    rows: tuple
    last: int

    def evaluate(self, assignment):
        for guard, leaf in self.rows:
            if bit(guard, assignment) == 0:
                return bit(leaf, assignment)
        return bit(self.last, assignment)


class Equations:
    """A consistent echelon system of affine equations equal to zero."""

    def __init__(self, rows=()):
        # Ordered by decreasing pivot, with all public pivots below private ones.
        self.rows = rows

    def reduce(self, form):
        for pivot, row in self.rows:
            if form & pivot:
                form ^= row
        return form

    def impose(self, form, target):
        row = self.reduce(form ^ target)
        if row == 0:
            return self
        if row == 1:
            raise ValueError("inconsistent continuation")
        pivot = 1 << (row.bit_length() - 1)
        rows = tuple(sorted((*self.rows, (pivot, row)), reverse=True))
        return Equations(rows)


def project_leaf(system, form, public):
    # A residual hidden coefficient can be independently chosen over each
    # public point in the active image. Either final value is then attainable.
    reduced = system.reduce(form)
    return 1 if reduced >> (public + 1) else reduced


def fold_last_line(result, public):
    if not result.rows or len(result.rows) < public:
        return result
    assert len(result.rows) == public
    line = Equations()
    for guard, _ in result.rows[:-1]:
        line = line.impose(guard, 1)
    guard, leaf = result.rows[-1]
    zero = line.impose(guard, 0).reduce(leaf)
    one = line.impose(guard, 1).reduce(result.last)
    assert zero in (0, 1) and one in (0, 1)
    last = zero ^ (guard if one != zero else 0)
    return DecisionList(result.rows[:-1], last)


def project(program, public, hidden):
    """Produce a symbolic decision list for exists(hidden) program(public,hidden)."""
    if public < 0 or hidden < 0:
        raise ValueError("negative dimension")
    forms = (form for pair in program.rows for form in pair)
    limit = 1 << (public + hidden + 1)
    if not 0 <= program.last < limit or any(not 0 <= form < limit for form in forms):
        raise ValueError("affine form uses an undeclared coordinate")

    system = Equations()
    out = []
    for guard, leaf in program.rows:
        reduced = system.reduce(guard)
        if reduced == 1:
            continue
        if reduced == 0:
            last = project_leaf(system, leaf, public)
            break

        early = project_leaf(system.impose(reduced, 0), leaf, public)
        system = system.impose(reduced, 1)
        if reduced >> (public + 1):
            # Both signs of the guard are possible above every remaining
            # public point. An accepting early exit settles that point.
            if early == 1:
                last = 1
                break
            if early != 0:
                out.append((early ^ 1, 1))
                system = system.impose(early, 0)
        else:
            # Every witness over a fixed public point takes the same branch.
            out.append((reduced, early))
    else:
        last = project_leaf(system, program.last, public)

    result = fold_last_line(DecisionList(tuple(out), last), public)
    assert len(result.rows) <= min(len(program.rows), max(0, public - 1))
    return result


def brute_projection(program, public, hidden):
    return tuple(int(any(program.evaluate(x | (y << public)) for y in range(1 << hidden)))
                 for x in range(1 << public))


def check_projection(program, public, hidden):
    result = project(program, public, hidden)
    expected = brute_projection(program, public, hidden)
    assert tuple(result.evaluate(x) for x in range(1 << public)) == expected
    return result


def algebraic_degree(table, dimension):
    """Independent lower-bound certificate from the truth-table Mobius transform."""
    coefficients = list(table)
    for i in range(dimension):
        for mask in range(1 << dimension):
            if mask & (1 << i):
                coefficients[mask] ^= coefficients[mask ^ (1 << i)]
    return max((mask.bit_count() for mask, value in enumerate(coefficients) if value), default=-1)


def audit():
    # All lists up to two guards on one visible and one hidden bit, and up
    # to one guard on two visible and one hidden bit. Include constant forms.
    exhaustive = 0
    for public, hidden, max_rows in ((1, 1, 2), (2, 1, 1)):
        forms = range(1 << (public + hidden + 1))
        for n in range(max_rows + 1):
            for data in product(forms, repeat=2 * n + 1):
                rows = tuple(zip(data[0:-1:2], data[1:-1:2]))
                check_projection(DecisionList(rows, data[-1]), public, hidden)
                exhaustive += 1
    print(f"{exhaustive} complete small affine lists match brute existential projection")

    rng = Random(74297)
    for _ in range(1800):
        public, hidden = rng.randrange(7), rng.randrange(5)
        forms = 1 << (public + hidden + 1)
        rows = tuple((rng.randrange(forms), rng.randrange(forms)) for _ in range(rng.randrange(12)))
        check_projection(DecisionList(rows, rng.randrange(forms)), public, hidden)
    print("1800 randomized lists, including no private/public bits and dependent guards")

    # AND of s=min(v,L+1) public bits forces s-1 guards by algebraic degree.
    # Pad with always-continue rows to test the cap at every specified length.
    sharp = 0
    for public in range(9):
        for length in range(10):
            s = min(public, length + 1)
            rows = [(1 << (i + 1), 0) for i in range(max(0, s - 1))]
            rows.extend([(1, 0)] * (length - len(rows)))
            last = 1 << s if s else 1
            program = DecisionList(tuple(rows), last)
            result = check_projection(program, public, 1)
            truth = tuple(result.evaluate(x) for x in range(1 << public))
            assert algebraic_degree(truth, public) == s
            assert len(result.rows) == min(length, max(0, public - 1))
            sharp += 1
    print(f"{sharp} public-dimension/source-length pairs attain the sharp guard bound")

    # A final guard reading the last public variable is initially emitted.
    # Its singleton leaves fold into that variable. Prefix a hidden parity
    # requirement, and use the same parity in the default leaf.
    for public, hidden in ((7, 3), (144, 100)):
        private_parity = ((1 << hidden) - 1) << (public + 1)
        rows = ((private_parity, 0),) + tuple((1 << (i + 1), 0) for i in range(public))
        program = DecisionList(rows, private_parity)
        result = project(program, public, hidden)
        assert len(result.rows) == public - 1
        assert result.evaluate((1 << public) - 1) == 1
        assert all(result.evaluate(((1 << public) - 1) ^ (1 << i)) == 0 for i in range(public))
        if public < 10:
            check_projection(program, public, hidden)
    print("Nontrivial private parity and final-line fold checked up to 144 public + 100 hidden bits")


if __name__ == "__main__":
    audit()
