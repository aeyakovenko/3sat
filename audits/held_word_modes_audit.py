"""Check actual proper DIMACS files for the half-sensitive held-word compiler."""

from argparse import ArgumentParser
from dataclasses import dataclass
from itertools import product
from subprocess import run

MODES = 'A00111001010011A'


def mode(key, width):
    assert width >= 4 and width % 4 == 0
    group = width // 4
    mask = (1 << group) - 1
    syndrome = sum((((key >> (i * group)) & mask).bit_count() % 2) << i for i in range(4))
    return MODES[syndrome]


def answer(kind, source_answer):
    return source_answer if kind == 'A' else kind == '1'


def min_sensitivity(width):
    for value in (False, True):
        table = [answer(mode(key, width), value) for key in range(1 << width)]
        least = min(sum(verdict != table[key ^ (1 << j)] for j in range(width))
                    for key, verdict in enumerate(table))
        assert least == width // 2
        assert mode(0, width) == 'A'
        assert sum(table[1 << j] != value for j in range(width)) == width // 2


def forbid(variables, bits):
    return tuple(-v if bit else v for v, bit in zip(variables, bits, strict=True))


def encode_row(row):
    assert len(row) == 3 and len({abs(k) for k in row}) == 3
    return (' '.join(map(str, row)) + ' 0\n').encode('ascii')


def decode_formula(raw):
    rows = []
    lines = raw.splitlines()
    p, cnf, top, count = lines[0].split()
    assert (p, cnf) == (b'p', b'cnf')
    for line in lines[1:]:
        digits = line.split()
        if not digits:
            continue
        a, b, c, end = map(int, digits)
        assert not end and len({abs(a), abs(b), abs(c)}) == 3
        assert all(0 < abs(lit) <= int(top) for lit in (a, b, c))
        rows.append((a, b, c))
    assert len(rows) == int(count)
    return rows


def held_word(key, bits, word_bytes):
    digits = (bits + 2) // 3
    return (b'1' + format(key, f'0{digits}o').encode('ascii') + b' 1 2 0\n').ljust(word_bytes)


@dataclass
class Template:
    bits: int
    word_bytes: int
    ahead: bytes
    after: bytes

    def file(self, key):
        return self.ahead + held_word(key, self.bits, self.word_bytes) + self.after


def compile_source(source, bits=4, word_bytes=16):
    digits = (bits + 2) // 3
    flags = [int('1' + format(z, f'0{digits}o')) for z in range(1 << bits)]
    vars_source = len({abs(lit) for row in source for lit in row})
    # Normalized source labels and gate outputs occupy separate ranges above all flags.
    assert len(held_word(0, bits, word_bytes)) == word_bytes
    def shift(lit):
        return flags[-1] + lit if lit > 0 else -(flags[-1] - lit)

    rows = [forbid((1, 2, 3), p) for p in product((0, 1), repeat=3) if any(p)]
    u, v = 4, 5
    rows.append((u, v, 1))
    gate = flags[-1] + vars_source
    for row in source:
        a, b, c = map(shift, row)
        gate += 1
        rows.extend(((u, a, gate), (-gate, b, c)))
    for key, flag in enumerate(flags):
        kind = mode(key, bits)
        rows.extend(((-flag, u if kind == '1' else -u, 1),
                     (-flag, v if kind == 'A' else -v, 1)))
    body = b''.join(map(encode_row, rows))
    header = f'p cnf {gate} {len(rows)+1}\n'.encode()
    prefix = header + body
    ahead = prefix.ljust((len(prefix)//word_bytes + 1) * word_bytes)
    # An actual second word follows. A caching program can read it before the held address.
    return Template(bits, word_bytes, ahead, b' ' * word_bytes)


def dpll(clauses):
    residual = list(clauses)
    while residual:
        for row in residual:
            if not row:
                return False
        units = {row[0] for row in residual if len(row) == 1}
        if not units:
            break
        if any(-v in units for v in units):
            return False
        residual = [tuple(lit for lit in row if -lit not in units) for row in residual
                    if not any(lit in units for lit in row)]
    if not residual:
        return True
    v = min(residual, key=len)[0]
    return dpll([(v,), *residual]) or dpll([(-v,), *residual])


def audit(solver):
    for bits in (4, 8, 12):
        min_sensitivity(bits)
    unsigned = (1, 2, 3)
    clause_sets = [(), ((1, 2, 3),), tuple(forbid(unsigned, pattern)
                                             for pattern in product((0, 1), repeat=3)),
                   ((1, 2, 3), (-1, -2, -3))]
    cases = edits = constituents = 0
    for source in clause_sets:
        template = compile_source(source)
        truth = dpll(source)
        verdicts = []
        variants = [template.file(key) for key in range(1 << template.bits)]
        for key, raw in enumerate(variants):
            predicted = answer(mode(key, template.bits), truth)
            clauses = decode_formula(raw)
            # The seven guard clauses force the sole triple 000; unit-propagate it explicitly.
            assert {tuple(c) for c in clauses[:7]} == {
                forbid((1, 2, 3), p) for p in product((0, 1), repeat=3) if any(p)}
            actual = dpll([(-1,), (-2,), (-3,), *clauses])
            assert actual == predicted, (source, key)
            if solver:
                result = run([solver, '-q'], input=raw, capture_output=True, check=False)
                assert result.returncode == (10 if predicted else 20), (source, key)
            verdicts.append(actual)
            cases += 1
        for key, raw in enumerate(variants):
            changes = 0
            for j in range(template.bits):
                alternate = variants[key ^ (1 << j)]
                differing = [(i, x ^ y) for i, (x, y) in enumerate(zip(raw, alternate, strict=True)) if x != y]
                assert len(differing) == 1
                byte, delta = differing[0]
                assert delta.bit_count() == 1 and len(template.ahead) <= byte < len(template.ahead) + template.word_bytes
                changes += verdicts[key] != verdicts[key ^ (1 << j)]
                edits += 1
            assert changes >= template.bits // 2
            constituents += mode(key, template.bits) == 'A' and verdicts[key] == truth
    print(f'{cases} physical formulas, {edits} one-bit neighbor checks, {constituents} source-preserving keys. '
          'Minimum half-word sensitivity checked through 12 independent bits.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--solver')
    audit(parser.parse_args().solver)
