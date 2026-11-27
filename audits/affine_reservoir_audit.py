"""Check affine updates, complete finite search paths, and printed query ports."""

from dataclasses import dataclass


def apply_form(form, bits, width):
    return ((form >> width) ^ (form & bits).bit_count()) & 1


@dataclass
class Chart:
    reservoir: tuple
    unused: tuple
    forms: dict

    @classmethod
    def initial(cls, variables, width):
        width = min(variables, width)
        return cls(tuple(range(width)), tuple(range(width, variables)), {})

    def point(self, values, untouched):
        width = len(self.reservoir)
        word = 0
        for i, variable in enumerate(self.reservoir):
            word |= ((values >> i) & 1) << variable
        for i, variable in enumerate(self.unused):
            word |= ((untouched >> i) & 1) << variable
        for variable, form in self.forms.items():
            word |= apply_form(form, values, width) << variable
        return word

    def points(self):
        return {
            self.point(r, u)
            for r in range(1 << len(self.reservoir))
            for u in range(1 << len(self.unused))
        }

    def projected(self, word):
        coordinates = self.reservoir + self.unused[:1]
        return sum(((word >> var) & 1) << i for i, var in enumerate(coordinates))

    def restrict(self, mask, side):
        width = len(self.reservoir)
        fresh, *remaining = self.unused
        basis = list(self.reservoir)
        if mask >> width:
            forms = self.forms.copy()
            forms[fresh] = (mask ^ (1 << width)) | (side << width)
        else:
            pivot = mask & -mask
            i = pivot.bit_length() - 1
            row = mask | (side << width)
            forms = {v: f ^ row if f & pivot else f for v, f in self.forms.items()}
            forms[basis[i]] = row ^ pivot
            basis[i] = fresh
        return Chart(tuple(basis), tuple(remaining), forms)


def verify_paths(chart, expected):
    assert chart.points() == expected
    if not chart.unused:
        return 1
    width = len(chart.reservoir)
    count = 1
    for mask in range(1, 1 << (width + 1)):
        for side in (0, 1):
            subset = {w for w in expected if (chart.projected(w) & mask).bit_count() % 2 == side}
            assert len(subset) * 2 == len(expected)
            count += verify_paths(chart.restrict(mask, side), subset)
    return count


def verify_search(models, policy):
    chart = Chart.initial(3, 1)
    while chart.unused:
        parents = chart.points() & models
        menu = [(m, s) for m in (1, 2, 3) for s in (0, 1)]
        available = policy(menu, len(chart.unused))
        if not available:
            return None, bool(parents)
        mask, side = available[0]
        yes = any((chart.projected(w) & mask).bit_count() % 2 == side for w in parents)
        before = bool(parents)
        chart = chart.restrict(mask, side if yes else 1 - side)
        assert bool(chart.points() & models) == before
    return bool(chart.points() & models), False


def xor_clauses(a, b, c):
    return ((a, b, -c), (-a, -b, -c), (a, -b, c), (-a, b, c))


def query_suffix(d, mask, side):
    digits = (d + 3) // 4
    entries = []
    for group in range(4):
        subset = (mask >> (digits * group)) & ((1 << digits) - 1)
        entries.append(int(f"{group + 1}{subset:0{digits}b}"))
    base = 6 * 10**digits
    a, b, c = (base + i for i in (4, 5, 6))
    clauses = xor_clauses(*entries[:2], a) + xor_clauses(*entries[2:], b) + xor_clauses(a, b, c)
    # The fixed part equates the consecutive names ending 2/3 to the output
    # and its complement, and forces the last two padding literals false.
    clauses += ((base + 2 + side, base + 7, base + 8),)
    return "".join(f"{x} {y} {z} 0\n" for x, y, z in clauses).encode("ascii")


def verify_suffix(d):
    base = query_suffix(d, 0, 0)
    columns = []
    used = set()
    for i in range(d + 1):
        trial = query_suffix(d, 1 << i if i < d else 0, int(i == d))
        positions = [j for j, (a, b) in enumerate(zip(base, trial)) if a != b]
        assert len(positions) == (4 if i < d else 1)
        assert all(base[j] ^ trial[j] == 1 for j in positions)
        assert used.isdisjoint(positions)
        used.update(positions)
        columns.append(positions)
    for mask in range(1 << d):
        for side in (0, 1):
            expected = bytearray(base)
            bits = mask | (side << d)
            for i, positions in enumerate(columns):
                if bits >> i & 1:
                    for j in positions:
                        expected[j] ^= 1
            assert expected == query_suffix(d, mask, side)


def main():
    paths = 0
    for n, b in ((0, 2), (2, 3), (3, 3), (4, 1), (5, 2), (5, 3)):
        paths += verify_paths(Chart.initial(n, b), set(range(1 << n)))
    policies = [lambda menu, r: menu[-1:], lambda menu, r: menu[r:r+1],
                lambda menu, r: menu if r == 2 else [], lambda menu, r: []]
    for mask in range(256):
        models = {w for w in range(8) if mask >> w & 1}
        for policy in policies:
            verdict, positive_stall = verify_search(models, policy)
            if verdict is None:
                assert positive_stall == bool(models)
            else:
                assert verdict == bool(models)
    for d in range(1, 10):
        verify_suffix(d)
    print(f"{paths} chart nodes matched their full affine image across all paths")
    print("256 source families under four timely-answer/timeout policies")
    print("all printed query suffixes and both polarities through dimension 9")


if __name__ == "__main__":
    main()
