"""Exact finite dynamics and proper-CNF queries for nested butterfly substitution."""

from argparse import ArgumentParser
from dataclasses import dataclass
from itertools import product
from random import Random
from subprocess import run


@dataclass(frozen=True)
class Edge:
    level: int
    x: int
    y: int
    rev: int


class Butterfly:
    def __init__(self, degree, depth):
        self.degree, self.depth = degree, depth
        self.side = degree**depth
        self.edges = []
        for level, x, digit in product(range(depth), range(self.side), range(degree)):
            place = degree**level
            original = x//place % degree
            y = x + (digit-original)*place
            rev = (level*self.side+y)*degree+original
            self.edges.append(Edge(level, x, y, rev))
        self.paths = {(x,y): self.path(x,y) for x,y in product(range(self.side),repeat=2)}
        self.masks = {p: sum(1 << i for i in edges) for p, edges in self.paths.items()}

    def path(self, x, y):
        indices = []
        for level in range(self.depth):
            place = self.degree**level
            digit = y//place % self.degree
            indices.append((level*self.side+x)*self.degree+digit)
            x += (digit-(x//place % self.degree))*place
        return indices

    def where(self, data, x, y):
        mask = self.masks[x,y]
        return data & mask == mask

    def plain(self, data):
        return sum(int(self.where(data,e.x,e.y)) << j for j,e in enumerate(self.edges))

    def step(self, data, rules):
        queries = {p: data & mask == mask for p,mask in self.masks.items()}
        nxt = 0
        for j,e in enumerate(self.edges):
            a = ((data >> j) & 1) + 2*((data >> e.rev) & 1)
            a += 4*queries[e.x,e.x] + 8*queries[e.y,e.y]
            a += 16*queries[e.x,e.y] + 32*queries[e.y,e.x]
            nxt |= (rules[j] >> a & 1) << j
        return nxt


def rule(fun):
    return sum(fun(*(n >> j & 1 for j in range(6))) << n for n in range(64))


def witness(b):
    rules, start = [], 0
    for i,e in enumerate(b.edges):
        if e.x == e.y:
            start |= 1 << i
            # X=1 is the period-three row. Rows X=0,3 have a period-two tick.
            if e.x == 1:
                z = rule(lambda a,ar,xx,yy,xy,yx:
                         int(e.level == 0) if xx else (1-a if e.level == 0 else 1))
            elif e.x in (0,3):
                z = rule(lambda a,ar,xx,yy,xy,yx: int(e.level == 1) if xx else 1)
            else:
                z = rule(lambda a,ar,xx,yy,xy,yx: a)
        elif (e.level, min(e.x,e.y), max(e.x,e.y)) in ((0,0,1),(1,1,3)):
            modulus = 4 if e.level == 0 else 3
            def count(a,ar,xx,yy,xy,yx):
                if not (xx and yy):
                    return a
                primary = e.x < e.y
                val = ((2*a + ar) if primary else (2*ar+a)) + 1
                val %= modulus
                return val//2 if primary else val%2
            z = rule(count)
        else:
            z = rule(lambda a,ar,xx,yy,xy,yx: a)
        rules.append(z)
    return rules,start


def least_period(values):
    return next(k for k in range(1,len(values)+1)
                if all(values[i] == values[(i+k)%len(values)] for i in range(len(values))))


class CNF:
    def __init__(self):
        self.maximum = 3
        self.rows = [tuple(-j if mask & (1 << (j-1)) else j for j in (1,2,3)) for mask in range(1,8)]
        self.ands = {}

    def pin(self, x):
        self.row((x,))

    def fresh(self):
        self.maximum += 1
        return self.maximum

    def row(self, lits):
        assert len(set(map(abs,lits))) == len(lits)
        row = list(lits)
        row.extend(a for a in (1,2,3) if a not in set(map(abs,lits)) and len(row)<3)
        assert len(row) == 3 and len(set(map(abs,row))) == 3
        self.rows.append(tuple(row))

    def conj(self, a, b):
        if a == 1 or b == 1 or a == -b:
            return 1
        if a == -1 or a == b:
            return b
        if b == -1:
            return a
        key = tuple(sorted((a,b)))
        if key not in self.ands:
            z = self.fresh()
            self.ands[key] = z
            self.row((-z,a))
            self.row((-z,b))
            self.row((z,-a,-b))
        return self.ands[key]

    def query(self, data, indices):
        h = -1
        for j in indices:
            h = self.conj(h,data[j])
        return h

    def table(self, values, bits):
        if bits == 0:
            return 1
        width = 1 << len(values)
        if bits == (1 << width)-1:
            return -1
        half = width//2
        lo,hi = bits % (1 << half), bits >> half
        if lo == hi:
            return self.table(values[:-1],lo)
        c = values[-1]
        a,b = self.table(values[:-1],lo),self.table(values[:-1],hi)
        return -self.conj(-self.conj(-c,a),-self.conj(c,b))

    def text(self):
        body = ''.join(f'{a} {b} {c} 0\n' for a,b,c in self.rows)
        return (f'p cnf {self.maximum} {len(self.rows)}\n'+body).encode()


def compact_order(h):
    return h if h < 22 else 22+(h-22)%72


def formula(b, rules, start, h, tag):
    cnf = CNF()
    state = [cnf.fresh() for _ in b.edges]
    for j,v in enumerate(state):
        cnf.pin(v if (start >> j) & 1 else -v)
    for _ in range(compact_order(h)):
        table = {p:cnf.query(state,indices) for p,indices in b.paths.items()}
        state = [cnf.table([state[i],state[e.rev],table[e.x,e.x],table[e.y,e.y],
                            table[e.x,e.y],table[e.y,e.x]],rules[i]) for i,e in enumerate(b.edges)]
    out = cnf.query(state,b.paths[0,3])
    cnf.pin(out if tag else -out)
    return cnf.text()


def audit(solver):
    small = Butterfly(2,2)
    changed = 0
    for data in range(1 << len(small.edges)):
        once = small.plain(data)
        twice = small.plain(once)
        assert small.plain(twice) == twice
        changed += once != twice
        for s,t in small.paths:
            assert small.where(once,s,t) == small.where(twice,s,t)
    assert changed
    print(f'All 65,536 unsigned databases stabilized as predicted; {changed:,} distinguish the first two substitutions.')

    checks = 0
    rng = Random(7222)
    for degree,depth,count in ((2,2,240),(2,3,128),(3,2,128),(3,3,20),(2,4,28)):
        fly = Butterfly(degree,depth)
        for _ in range(count):
            rules = [rng.getrandbits(64) for _ in fly.edges]
            state = rng.getrandbits(len(fly.edges))
            states = [state]
            for _ in range(105):
                states.append(fly.step(states[-1],rules))
            assert states[22:34] == states[94:106]
            checks += 12
    print(f'{checks:,} adaptive database cutoff identities checked.')

    rules, state = witness(small)
    states, verdicts = [], []
    for _ in range(72):
        states.append(state)
        verdicts.append(small.where(state,0,3))
        state = small.step(state,rules)
    assert state == states[0] and least_period(states) == least_period(verdicts) == 72
    print('Exact period 72 in one fixed source–sink verdict on 16 edges.')
    if solver:
        count = 0
        for h in (0,4,21,22,43,71,72,93,94,4096,10**50):
            for tag in (0,1):
                raw = formula(small,rules,states[0],h,tag)
                out = run([solver,'-q'],input=raw,capture_output=True,check=False)
                assert out.returncode == (10 if verdicts[h%72] == bool(tag) else 20), (h,tag,out.returncode)
                count += 1
        print(f'{count} proper physical CNFs checked by the specified SAT solver.')


if __name__ == '__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('--solver', help='Optional CaDiCaL path for the actual proper-CNF tests.')
    audit(p.parse_args().solver)
