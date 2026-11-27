"""Compile nonseparable equality into a pair of aligned proper DIMACS files.

Each table literal is one positive decimal identifier, split between an original
data word and a neighboring query word. No individual token starts with zero.
"""

from argparse import ArgumentParser
from itertools import product
from math import isqrt
from random import Random
from subprocess import run


def wordline(line, width):
    assert len(line) < width
    return line + b' ' * (width - 1 - len(line)) + b'\n'


class Layout:
    def __init__(self, coordinates, alphabet, width=32):
        assert coordinates >= 2 and alphabet >= 2
        self.n = coordinates
        self.k = alphabet
        self.width = width
        self.digits = len(str(alphabet - 1))
        top_name = self.name(alphabet - 1, alphabet - 1)
        self.select = [top_name + 1 + i for i in range(coordinates)]
        rows = [tuple(-v if mask >> (v - 1) & 1 else v for v in (1, 2, 3)) for mask in range(1, 8)]
        rows.extend(((4, 5, 1), (-4, -5, 1), (6, 1, 2)))
        for a, x in product(range(alphabet), repeat=2):
            mixed = self.name(a, x)
            target = 4 if a == x else -4
            rows.extend(((mixed, -target, 1), (-mixed, target, 1)))
        rows.extend((-4, z, 1) for z in self.select)
        last = self.select[0]
        for i, z in enumerate(self.select[1:], 1):
            out = self.select[-1] + i
            rows.extend(((out, -last, 1), (out, -z, 1), (-out, last, z)))
            last = out
        rows.append((last, 1, 2))
        self.vars = last
        self.clauses = len(rows) + 2 * coordinates
        self.header = wordline(f'p cnf {last} {self.clauses}'.encode(), width)
        self.public = [self.header] + [wordline((' '.join(map(str, row)) + ' 0').encode(), width) for row in rows]
        self.first = len(self.public)

    def name(self, a, x):
        return int(f'9{a:0{self.digits}d}{x:0{self.digits}d}')

    def data(self, a):
        assert 0 <= a < self.k
        ending = f'9{a:0{self.digits}d}'.encode()
        assert len(ending) < self.width
        return ending.rjust(self.width, b' ')

    def query(self, x, flag):
        assert 0 <= x < self.k and flag in (4, 5, 6)
        return wordline(f'{x:0{self.digits}d} 1 0\n{flag} 1 2 0'.encode(), self.width)

    def left(self, i):
        text = f'-{self.select[i]} '.encode()
        return text.rjust(self.width, b' ')

    def addr(self, i, kind):
        return self.first + 3 * i + (1 if kind == 'A' else 2)

    def coord(self, address):
        if self.first <= address < self.first + 3 * self.n:
            i, part = divmod(address - self.first, 3)
            if part:
                return i, 'A' if part == 1 else 'X'
        return None

    def file(self, a, x, tag_slot, sign):
        assert len(a) == len(x) == self.n
        words = self.public.copy()
        for i in range(self.n):
            flag = (4 if sign else 5) if i == tag_slot else 6
            words.extend((self.left(i), self.data(a[i]), self.query(x[i], flag)))
        assert len(words) == 7 * self.n + 2 * self.k**2 + 9
        return b''.join(words)

    @staticmethod
    def detect(file_words, header, width):
        try:
            prefix, kind, variables, clauses = header.split()
            if (prefix, kind) != (b'p', b'cnf'):
                return None
            c = int(clauses)
            n = file_words - c - 1
            rest = c - 6 * n - 8
            if n < 2 or rest < 8:
                return None
            k = isqrt(rest // 2)
            if 2 * k**2 != rest:
                return None
            candidate = Layout(n, k, width)
            return candidate if candidate.header == header and candidate.vars == int(variables) else None
        except (AssertionError, ValueError):
            return None


def proper_cnf(raw):
    lines = raw.splitlines()
    header = lines[0].split()
    assert len(header) == 4 and header[:2] == [b'p', b'cnf']
    nvars, count = map(int, header[2:])
    assert len(lines) == count + 1
    rows = []
    for line in lines[1:]:
        a, b, c, end = map(int, line.split())
        assert end == 0 and len({abs(a), abs(b), abs(c)}) == 3
        assert all(0 < abs(x) <= nvars for x in (a, b, c))
        rows.append((a, b, c))
    return rows


def satisfies(rows):
    """A complete fallback for general proper 3-CNF inputs in this finite audit."""
    def solve(clauses):
        while clauses:
            if any(not row for row in clauses):
                return False
            unit = next((row[0] for row in clauses if len(row) == 1), None)
            if unit is None:
                chosen = clauses[0][0]
                return solve(clauses + [(chosen,)]) or solve(clauses + [(-chosen,)])
            clauses = [tuple(lit for lit in row if lit != -unit) for row in clauses if unit not in row]
        return True
    return solve(rows)


class WordRam:
    def __init__(self, raw, width):
        assert len(raw) % width == 0
        self.width = width
        self.size = len(raw) // width
        self.cells = {i // width: int.from_bytes(raw[i:i + width], 'little') for i in range(0, len(raw), width)}
        self.trace = []

    def load(self, address):
        value = self.cells.get(address, 0)
        self.trace.append(('R', address, value))
        return value

    def word(self, address):
        return self.load(address).to_bytes(self.width, 'little')

    def store(self, address, value):
        self.trace.append(('W', address, value))
        self.cells[address] = value


def scanner(raw, width, mode):
    ram = WordRam(raw, width)

    def ordinary_sat():
        original = b''.join(ram.word(i) for i in range(ram.size))
        return satisfies(proper_cnf(original)), ram.trace

    layout = Layout.detect(ram.size, ram.word(0), width)
    if layout is None:
        return ordinary_sat()
    for i, expected in enumerate(layout.public[1:], 1):
        if ram.word(i) != expected:
            return ordinary_sat()
    for i in range(layout.n):
        if ram.word(layout.first + 3 * i) != layout.left(i):
            return ordinary_sat()
    n = layout.n
    if mode == 'data-first':
        order = [(i, side) for side in ('A', 'X') for i in range(n)]
    elif mode == 'pairwise':
        order = [(i, side) for i in range(n) for side in ('A', 'X')]
    elif mode == 'reverse-query':
        order = [(i, side) for side in ('X', 'A') for i in reversed(range(n))]
    else:
        raise ValueError(mode)
    tag = None
    for i, side in order:
        contents = ram.word(layout.addr(i, side))
        try:
            if side == 'A':
                a = int(contents[-layout.digits:])
                if not 0 <= a < layout.k or contents != layout.data(a):
                    return ordinary_sat()
                ram.store(ram.size + i, a)
            else:
                x = int(contents[:layout.digits])
                flag = int(contents[layout.digits + 5:layout.digits + 6])
                if flag not in (4, 5, 6) or not 0 <= x < layout.k or contents != layout.query(x, flag):
                    return ordinary_sat()
                ram.store(ram.size + n + i, x)
                if flag != 6:
                    if tag is not None:
                        return ordinary_sat()
                    tag = flag
        except ValueError:
            return ordinary_sat()
    if tag is None:
        # The validated zero-tag file allows either orientation of equality.
        return True, ram.trace
    equal = True
    for i in range(n):
        a = ram.load(ram.size + i)
        x = ram.load(ram.size + n + i)
        equal &= a == x
    return (tag == 4) == equal, ram.trace


def audit_files(solver):
    examples = []
    for n, k in ((3, 2), (2, 3)):
        for a in product(range(k), repeat=n):
            for x in product(range(k), repeat=n):
                examples.extend((n, k, a, x, j) for j in range(n))
    rng = Random(20261127)
    for _ in range(12):
        n, k = 5, 11
        a = tuple(rng.randrange(k) for _ in range(n))
        x = a if rng.randrange(2) else tuple(rng.randrange(k) for _ in range(n))
        examples.append((n, k, a, x, rng.randrange(n)))
    for n, k, a, x, j in examples:
        layout = Layout(n, k)
        files = [layout.file(a, x, j, s) for s in (False, True)]
        diffs = [(byte // layout.width, u ^ v) for byte, (u, v) in enumerate(zip(*files, strict=True)) if u != v]
        assert diffs == [(layout.addr(j, 'X'), 1)]
        for s, raw in enumerate(files):
            proper_cnf(raw)
            expected = bool(s) == (a == x)
            assert scanner(raw, layout.width, 'pairwise')[0] == expected
            if solver:
                process = run([solver, '-q'], input=raw, capture_output=True, check=False)
                assert process.returncode == (10 if expected else 20)
    print(f'{2 * len(examples)} proper physical files, including two-digit split identifiers and single-bit tags')


def audit_prefixes():
    layout = Layout(24, 4)
    a = tuple(i % 4 for i in range(layout.n))
    modes = ('data-first', 'pairwise', 'reverse-query')
    quota = 2
    default = layout.file(a, a, -1, False)
    visited = set()
    for mode in modes:
        _, trace = scanner(default, layout.width, mode)
        private = set()
        for op, addr, _ in trace:
            coordinate = layout.coord(addr)
            if op == 'R' and coordinate is not None:
                private.add(coordinate[0])
                if len(private) == quota:
                    break
        assert len(private) == quota
        visited |= private
    assert len(visited) <= quota * len(modes)
    tag = next(i for i in range(layout.n) if i not in visited)
    holes = {layout.addr(i, 'X') for i in range(layout.n) if i not in visited}
    for mode in modes:
        cuts = []
        for sign in (False, True):
            raw = layout.file(a, a, tag, sign)
            verdict, trace = scanner(raw, layout.width, mode)
            assert verdict == sign
            cut = next(t for t, event in enumerate(trace) if event[0] == 'R' and event[1] in holes)
            cuts.append(trace[:cut])
            for i in range(layout.n):
                flipped = list(a)
                flipped[i] ^= 1
                for left, right in ((flipped, a), (a, flipped)):
                    assert scanner(layout.file(left, right, tag, sign), layout.width, mode)[0] != verdict
        assert cuts[0] == cuts[1]
        observed = {layout.coord(addr) for op, addr, _ in cuts[0] if op == 'R' and layout.coord(addr) is not None}
        assert len({i for i, _ in observed}) >= quota
        n_old = sum(part == 'A' for _, part in observed)
        n_query = len(observed) - n_old
        print(f'{mode}: identical first-hole prefix; {n_old} original A words, {n_query} frozen X words; all 48 word pivots')
    # Change a wholly public clause into another valid proper clause, leaving
    # the byte length and public metadata intact. This follows the fallback.
    small = Layout(2, 2)
    file = small.file((0, 1), (0, 1), 1, True)
    damaged = file[:small.width] + wordline(b'1 2 3 0', small.width) + file[2 * small.width:]
    assert scanner(damaged, small.width, 'pairwise')[0] == satisfies(proper_cnf(damaged))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--solver', help='path to CaDiCaL for independent verification')
    audit_files(parser.parse_args().solver)
    audit_prefixes()
