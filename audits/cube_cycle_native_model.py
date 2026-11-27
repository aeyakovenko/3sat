"""Cube-cycle catalog: independent scalar model of the four-bit native RAM and of the
16-bit cube-cycle catalog.

Written from the machine paragraph of exact-clocks-for-two-word-sat-inputs.md
and the operation list (ALU / BRANCH tuples) of clocked_native_path.py.  Nothing
is imported from the journal; `--crosscheck PATH` compares this file's ALU table
with the journal's `primitive` when a copy of clocked_native_path.py is given.

Machine convention used everywhere in round 13
----------------------------------------------
* 4-bit words, 16 memory words.  mem[i] = input word i for i = 0..3, the other
  twelve memory words and every register start at 0.
* Unlimited registers and code; every 4-bit literal is an immediate operand.
* One step each: LOAD reg <- mem[addr], STORE mem[addr] <- value (addr and
  value are a literal or a register), one ALU operation on two register/literal
  operands, one comparison branch (eq, unsigned lt, signed lt) on two
  register/literal operands; both outcomes go to arbitrary fixed labels.
* ACCEPT / REJECT are free terminal states.  ACCEPT = "satisfiable",
  REJECT = "unsatisfiable (every cube vertex excluded, a cover)".

Catalog convention
------------------
mask bit j says clause label j (edge j of the Hamiltonian cycle) is present.
Input word i holds mask bits 4i..4i+3 (bit 4i is the low bit of the word).
UNSAT  <=>  (mask | rotl16(mask, 1)) == 0xffff.
"""

import json
import sys

ALU = ('and', 'or', 'xor', 'add', 'sub', 'mul', 'shl', 'shr', 'sar',
       'shlmod', 'shrmod', 'sarmod', 'rol', 'ror',
       'eq', 'lt', 'slt', 'ne', 'ge', 'sge')
BRANCH = ('eq', 'lt', 'slt')


def signed(a):
    return a - 16 if a & 8 else a


def alu(name, a, b):
    """Scalar semantics of the twenty ALU operations on 4-bit words."""
    assert 0 <= a < 16 and 0 <= b < 16
    if name == 'and':
        return a & b
    if name == 'or':
        return a | b
    if name == 'xor':
        return a ^ b
    if name == 'add':
        return (a + b) % 16
    if name == 'sub':
        return (a - b) % 16
    if name == 'mul':
        return (a * b) % 16
    if name == 'shl':                      # saturating count
        return 0 if b >= 4 else (a << b) % 16
    if name == 'shr':
        return 0 if b >= 4 else a >> b
    if name == 'sar':
        fill = 15 if a & 8 else 0
        return fill if b >= 4 else (signed(a) >> b) % 16
    if name == 'shlmod':                   # count modulo the word width
        return (a << (b % 4)) % 16
    if name == 'shrmod':
        return a >> (b % 4)
    if name == 'sarmod':
        return (signed(a) >> (b % 4)) % 16
    if name == 'rol':
        k = b % 4
        return ((a << k) | (a >> (4 - k))) % 16
    if name == 'ror':
        k = b % 4
        return ((a >> k) | (a << (4 - k))) % 16
    if name == 'eq':
        return int(a == b)
    if name == 'ne':
        return int(a != b)
    if name == 'lt':
        return int(a < b)
    if name == 'ge':
        return int(a >= b)
    if name == 'slt':
        return int(signed(a) < signed(b))
    if name == 'sge':
        return int(signed(a) >= signed(b))
    raise ValueError(name)


def branch(name, a, b):
    if name == 'eq':
        return a == b
    if name == 'lt':
        return a < b
    if name == 'slt':
        return signed(a) < signed(b)
    raise ValueError(name)


# ---------------------------------------------------------------- catalog

def words_of(mask):
    """Input words (address 0..3) of a 16-bit mask: word i = bits 4i..4i+3."""
    return [(mask >> (4 * i)) & 15 for i in range(4)]


def mask_of(words):
    return sum(w << (4 * i) for i, w in enumerate(words))


def is_cover(mask):
    rot = ((mask << 1) & 0xffff) | (mask >> 15)
    return (mask | rot) == 0xffff


def is_cover_by_assignments(mask, cycle=None):
    """Independent semantic definition: enumerate the 16 assignments of the
    4-cube and the clauses on the edges of a Hamiltonian cycle."""
    if cycle is None:
        cycle = [i ^ (i >> 1) for i in range(16)]        # reflected Gray cycle
    for vertex in range(16):
        falsified = False
        for j in range(16):
            if (mask >> j) & 1 and vertex in (cycle[j], cycle[(j + 1) % 16]):
                falsified = True       # clause j is false exactly at its two endpoints
                break
        if not falsified:
            return False               # a satisfying assignment exists
    return True


SAFE = tuple(w for w in range(16)
             if all(((w >> j) & 1) or ((w >> (j + 1)) & 1) for j in range(3)))


# ------------------------------------------------------------ interpreter

class StepLimit(Exception):
    pass


def run(program, words, limit=64):
    """Execute a tree/graph program.  Returns (verdict, steps).

    program: nested dicts or a dict of labelled nodes {"start": ..., "nodes": {...}}.
    Node forms:
      "ACCEPT" / "REJECT"
      {"op": "load", "dst": r, "addr": x, "next": n}
      {"op": "store", "addr": x, "val": y, "next": n}
      {"op": <ALU name>, "dst": r, "a": x, "b": y, "next": n}
      {"op": "br", "cmp": eq|lt|slt, "a": x, "b": y, "then": n, "else": n}
    Operands: an int literal 0..15 or a register name (str).  A node reference
    may be a nested node or the name (str starting with '@') of a labelled node.
    """
    nodes = {}
    node = program
    if isinstance(program, dict) and 'start' in program:
        nodes = program['nodes']
        node = program['start']
    mem = list(words) + [0] * 12
    reg = {}
    steps = 0

    def val(x):
        if isinstance(x, int):
            assert 0 <= x < 16
            return x
        return reg.get(x, 0)

    while True:
        while isinstance(node, str) and node.startswith('@'):
            node = nodes[node]
        if node in ('ACCEPT', 'REJECT'):
            return node, steps
        steps += 1
        if steps > limit:
            raise StepLimit
        op = node['op']
        if op == 'load':
            reg[node['dst']] = mem[val(node['addr'])]
            node = node['next']
        elif op == 'store':
            mem[val(node['addr'])] = val(node['val'])
            node = node['next']
        elif op == 'br':
            node = node['then'] if branch(node['cmp'], val(node['a']), val(node['b'])) else node['else']
        else:
            reg[node['dst']] = alu(op, val(node['a']), val(node['b']))
            node = node['next']


def evaluate(program, limit=64):
    """Run on all 65,536 masks.  Returns (errors, histogram {steps: count},
    worst mask list)."""
    hist = {}
    errors = []
    worst = (0, [])
    for mask in range(65536):
        verdict, steps = run(program, words_of(mask), limit)
        expect = 'REJECT' if is_cover(mask) else 'ACCEPT'
        if verdict != expect:
            errors.append(mask)
        hist[steps] = hist.get(steps, 0) + 1
        if steps > worst[0]:
            worst = (steps, [mask])
        elif steps == worst[0] and len(worst[1]) < 8:
            worst[1].append(mask)
    return errors, dict(sorted(hist.items())), worst


def dump_tables(path):
    """ALU and branch tables for the C++ programs' self-check."""
    table = {name: [[alu(name, a, b) for b in range(16)] for a in range(16)] for name in ALU}
    btab = {name: [[int(branch(name, a, b)) for b in range(16)] for a in range(16)] for name in BRANCH}
    with open(path, 'w') as out:
        json.dump({'alu': table, 'branch': btab, 'order': list(ALU)}, out)


def crosscheck(path):
    import importlib.util
    spec = importlib.util.spec_from_file_location('journal_model', path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    assert tuple(mod.ALU) == ALU and tuple(mod.BRANCH) == BRANCH
    n = 0
    for name in ALU:
        for a in range(16):
            for b in range(16):
                assert int(mod.primitive(name, a, b)) == alu(name, a, b), (name, a, b)
                n += 1
    for name in BRANCH:
        for a in range(16):
            for b in range(16):
                assert bool(mod.primitive(name, a, b)) == branch(name, a, b)
                n += 1
    print(f'cross-check with {path}: {n} table entries agree')


if __name__ == '__main__':
    if len(sys.argv) >= 3 and sys.argv[1] == '--crosscheck':
        crosscheck(sys.argv[2])
    elif len(sys.argv) >= 3 and sys.argv[1] == '--dump':
        dump_tables(sys.argv[2])
        print('tables written to', sys.argv[2])
    else:
        covers = [m for m in range(65536) if is_cover(m)]
        assert all(is_cover_by_assignments(m) == is_cover(m) for m in range(65536))
        print('covers:', len(covers), 'SAFE words:', SAFE)
