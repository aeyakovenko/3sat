"""Exhaust small dynamically addressed native blocks with and without writer labels."""

from argparse import ArgumentParser
from dataclasses import dataclass
from functools import cache
from itertools import product
from subprocess import run

from native_block_compiler_audit import new_file


@dataclass(frozen=True)
class Input:
    first: int
    query: int
    overlap: bool
    target: int


@dataclass(frozen=True)
class Record:
    choice: int | None
    imports: tuple
    writes: tuple
    allowed: bool


def microcode(y, block, choice, read, write):
    if block == 0:
        write(choice, choice)
        write(choice, 1 - choice)
        return True
    address = y.first if block == 1 else y.query
    bit = read(address)
    assert read(address) == bit
    if block == 1:
        dest = y.first if y.overlap else 2 + bit
        write(dest, bit)
        write(dest, 1 - bit)
    else:
        dest = 4 + bit
        write(dest, 1 - bit)
    assert read(dest) == 1 - bit
    return block == 1 or bit == y.target


def actual(y, choice):
    memory = {}
    owner = {}
    single_writer = True
    approved = True
    for block in range(3):
        def put(a, v, block=block):
            nonlocal single_writer
            single_writer &= a not in owner or owner[a] == block
            owner[a] = block
            memory[a] = v

        approved &= microcode(y, block, choice, lambda a: memory.get(a, 0), put)
    return approved, single_writer


@cache
def record(y, block, seed, tagged):
    imports = []
    writes = []
    local = {}
    bit = seed & 1
    tag = (seed >> 1) - 1 if tagged else None

    def read(address):
        if address in local:
            return local[address]
        imports.append((address, bit, tag))
        return bit

    def write(address, value):
        local[address] = value
        writes.append((address, value))

    allowed = microcode(y, block, bit, read, write)
    if tagged and imports:
        allowed &= -1 <= tag < block and (tag != -1 or bit == 0)
    return Record(bit if block == 0 else None, tuple(imports), tuple(writes), allowed)


def compare_pair(first, second, index, tagged):
    dictionary = dict(first.writes)
    if not tagged and dictionary.keys() & dict(second.writes).keys():
        return False, 0
    nonzero_hits = 0
    for address, bit, origin in second.imports:
        if tagged:
            if origin == index and dictionary.get(address) != bit:
                return False, 0
            if origin < index and address in dictionary:
                return False, 0
        elif address in dictionary:
            if dictionary[address] != bit:
                return False, 0
            nonzero_hits += bit != 0
    return True, nonzero_hits


def accepts(y, seeds, tagged):
    rows = [record(y, i, seed, tagged) for i, seed in enumerate(seeds)]
    for j, row in enumerate(rows):
        if not row.allowed or any(record(y, j, smaller, tagged) == row for smaller in range(seeds[j])):
            return False
        total = 0
        for i in range(j):
            matched, hits = compare_pair(rows[i], row, i, tagged)
            if not matched:
                return False
            total += hits
        if not tagged and total != sum(bit != 0 for _, bit, _ in row.imports):
            return False
    return True


def audit_sources():
    cases = paths = 0
    for first, query, overlap, target in product(range(2), range(4), (False, True), range(2)):
        y = Input(first, query, overlap, target)
        for tagged in (False, True):
            true = [actual(y, bit) for bit in (0, 1)]
            expected = sum(good and (tagged or single_writer) for good, single_writer in true)
            surviving = [seeds for seeds in product(range(8), repeat=3) if accepts(y, seeds, tagged)]
            assert len(surviving) == expected
            assert {seeds[0] & 1 for seeds in surviving} == {
                choice for choice, (good, single) in enumerate(true) if good and (tagged or single)}
            cases += 8 ** 3
            paths += len(surviving)
    print(f'{cases} candidate block-seed histories compared with actual RAM execution; {paths} genuine paths survived')


def source_formula(y, tagged):
    refs = [list(range(4 + 3 * b, 7 + 3 * b)) for b in range(3)]
    next_name = 13
    ports = []
    tests = []

    def add(bits, predicate):
        ports.append(bits)
        tests.append(predicate)

    for j in range(3):
        add(refs[j], lambda u, j=j: record(y, j, u, tagged).allowed)
        for v in range(8):
            add(refs[j], lambda u, j=j, v=v: not (v < u and record(y, j, v, tagged) == record(y, j, u, tagged)))
        counters = []
        for i in range(j):
            def pair(word, i=i, j=j):
                left = record(y, i, word & 7, tagged)
                right = record(y, j, (word >> 3) & 7, tagged)
                return compare_pair(left, right, i, tagged)

            both = refs[i] + refs[j]
            add(both, lambda word, pair=pair: pair(word)[0])
            if not tagged:
                count = [next_name, next_name + 1]
                next_name += 2
                counters.extend(count)
                for idx, name in enumerate(count):
                    add(both + [name], lambda word, idx=idx, pair=pair:
                        ((pair(word & 63)[1] >> idx) & 1) == (word >> 6))
        if not tagged:
            def exact(word, j=j):
                reader = record(y, j, word & 7, False)
                required = sum(bit != 0 for _, bit, _ in reader.imports)
                total = sum((word >> (3 + 2 * i)) & 3 for i in range(j))
                return total == required

            add(refs[j] + counters, exact)
    return new_file(next_name - 4, ports, tests)


def enumerate_models(raw, solver):
    header, clauses = raw.split(b'\n', maxsplit=1)
    tag, kind, n, count = header.split()
    assert (tag, kind) == (b'p', b'cnf')
    n, count = int(n), int(count)
    blocking = []
    while True:
        query = f'p cnf {n} {count + len(blocking)}\n'.encode() + clauses + b''.join(blocking)
        result = run([solver, '-q'], input=query, capture_output=True, check=False)
        if result.returncode == 20:
            return len(blocking)
        assert result.returncode == 10
        assignment = [int(lit) for line in result.stdout.splitlines() if line.startswith(b'v ')
                      for lit in line[2:].split() if lit != b'0']
        assert len(assignment) == n and len({abs(lit) for lit in assignment}) == n
        blocking.append((' '.join(str(-lit) for lit in assignment) + ' 0\n').encode())
        assert len(blocking) <= 2


def audit_cnf(solver):
    files = assignments = 0
    single = set()
    for y in (Input(0, 0, True, 0), Input(0, 1, True, 0), Input(0, 1, False, 1), Input(0, 1, False, 0)):
        for tagged in (False, True):
            expected = sum(a and (tagged or one) for a, one in (actual(y, bit) for bit in (0, 1)))
            file = source_formula(y, tagged)
            raw = file.materialize()
            result = enumerate_models(raw, solver)
            assert result == expected
            single.add(result)
            assignments += result
            files += 1
    assert single == {0, 1, 2}
    print(f'CaDiCaL enumerated {assignments} distinct full assignments over {files} proper files, realizing counts 0, 1 and 2')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--solver', help='CaDiCaL binary for counting physical models')
    audit_sources()
    chosen = parser.parse_args().solver
    if chosen:
        audit_cnf(chosen)
