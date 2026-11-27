"""Check timestamped sparse pointer replay across original packed-input holes."""

from argparse import ArgumentParser
from dataclasses import dataclass
from itertools import combinations_with_replacement, product
from random import Random
from subprocess import run

from last_physical_word_pointer_audit import OrbitIndex
from one_overwritten_address_audit import CachedReplay, Deferred
from packed_row_queries import RowQueryLayout


@dataclass(frozen=True)
class Real:
    value: int
    marked: bool = False
    original_reply: int | None = None


class Eager:
    def __init__(self, old, holes):
        self.old, self.holes = old, holes
        self.writes = {}
        self.c = self.m = 0
        self.endpoints = set()
        self.raw = set()

    def load(self, address):
        a = address.value
        if address.original_reply is not None:
            self.raw.add(address.original_reply)
        known = not address.marked and (a in self.writes or a in self.holes)
        if a in self.writes:
            reply = self.writes[a]
        elif a in self.holes:
            reply = Real(self.holes[a], original_reply=self.holes[a])
        else:
            reply = Real(self.old.get(a,0))
        return Real(reply.value, not known, reply.original_reply)

    def store(self, a, b):
        if a.marked or b.marked:
            self.m += 1
        else:
            self.endpoints.update((a.value,b.value))
        self.writes[a.value] = b

    def consume(self, a, b):
        self.c += int(a.marked or b.marked)


class HoleIndex:
    def __init__(self, old, hole_ids):
        self.hole_ids = set(hole_ids)
        self.f = {x:y for x,y in old.items() if x not in self.hole_ids and y}
        self.orbits = OrbitIndex(self.f)
        nodes = set(self.orbits.labels) | self.hole_ids
        self.first = {}
        for x in nodes:
            pos = x
            seen = set()
            while pos not in seen and pos not in self.hole_ids:
                seen.add(pos)
                pos = self.f.get(pos,0)
            self.first[x] = (len(seen),pos) if pos in self.hole_ids else None

    def first_label(self, x):
        if x in self.first:
            return self.first[x]
        h = self.first[0]
        return (h[0]+1,h[1]) if h is not None else None


class Replay(CachedReplay):
    def __init__(self, static, holes):
        assert static.hole_ids == set(holes)
        self.static, self.holes = static, holes
        self.index = static.orbits
        self.cache, self.first_cache = {}, {}
        self.overlay = {}
        self.writes = []
        self.powers = 0
        self.raw_origins = set()
        self.label(0)

    def label(self, number):
        if number not in self.cache:
            self.cache[number] = self.index.labels.get(number)
            self.first_cache[number] = self.static.first_label(number)
        return self.cache[number]

    def load(self, x):
        if not isinstance(x, Deferred):
            if x in self.overlay:
                return self.overlay[x]
            if x in self.holes:
                return self.holes[x]
        return super().load(x)

    def resolve(self, x):
        if not isinstance(x, Deferred):
            return x
        origin, steps = x.origin, 0
        self.label(origin)
        raw_last = False
        for version in x.versions:
            if raw_last:
                # This instruction actually uses a just-forwarded hole reply
                # as an address. A hole at the end of a chain avoids this cost.
                self.raw_origins.add(origin)
                self.label(origin)
                raw_last = False
            for key, value in reversed(self.writes[:version]):
                if self.hits(origin,steps,key):
                    origin,steps = value,0
                    break
            else:
                cut = self.first_cache[origin]
                if cut is not None and cut[0] == steps:
                    origin,steps,raw_last = self.holes[cut[1]],0,True
                else:
                    assert cut is None or steps < cut[0]
                    steps += 1
        if steps == 0:
            return origin
        self.powers += 1
        return self.index.advance(origin,steps)

    def record(self, x, y):
        key,value = super().record(x,y)
        self.overlay[key] = value
        return key,value


class Paired:
    def __init__(self, old, holes, static=None):
        self.real = Eager(old,holes)
        self.sim = Replay(static or HoleIndex(old,holes),holes)
        self.prefixes = 0

    def budget(self):
        a,b = self.real,self.sim
        assert b.raw_origins <= a.raw
        assert len(b.cache)+b.powers <= 1 + 4*a.c + 6*a.m + len(a.endpoints) + len(a.raw)
        self.prefixes += 1

    def load(self, operand):
        x,v = operand
        y,w = self.real.load(x),self.sim.load(v)
        assert y.marked == isinstance(w,Deferred)
        if not y.marked:
            assert y.value == w
        self.budget()
        return y,w

    def store(self, a, b):
        x,u = a
        y,v = b
        self.real.store(x,y)
        assert self.sim.record(u,v) == (x.value,y.value)
        self.budget()

    def compare(self, a, b):
        x,u = a
        y,v = b
        self.real.consume(x,y)
        assert (self.sim.resolve(u),self.sim.resolve(v)) == (x.value,y.value)
        self.budget()
        return x.value == y.value

    def xor(self, a, b):
        x,u = a
        y,v = b
        self.real.consume(x,y)
        new = x.value ^ y.value
        assert new == self.sim.resolve(u) ^ self.sim.resolve(v)
        self.budget()
        return lit(new)


def lit(x):
    return Real(x),x


def hazards():
    old = {0:4, 4:1, 10:11, 23:37, 37:5, 39:11}
    holes = {1:23, 11:23, 5:39}
    # Replay two dependent registers across the first overwrite of the same hole.
    p = Paired(old,holes)
    at_hole = p.load(lit(10))
    before = p.load(at_hole)
    p.store(lit(11),lit(0))
    after = p.load(at_hole)
    assert p.compare(before,lit(23)) and p.compare(after,lit(0))
    assert 23 not in p.sim.raw_origins  # both chains end immediately at the reply
    used = p.load(before)
    p.store(lit(11),lit(37))
    assert p.compare(used,lit(37)) and p.real.raw == {23}
    assert p.load(lit(11)) == lit(37)
    # Current write at 11 is 37, but 'after' was produced when it was zero.
    assert p.compare(p.load(after),lit(4))
    # Hole 0, non-index origins, duplicate raw replies, overwritten hole sources.
    p = Paired({2:7,4:14,8:1,19:22},{0:4,7:4,22:19})
    r = lit(99)
    for _ in range(3):
        r = p.load(r)
    assert p.compare(r,lit(14))
    r = p.load(p.load(lit(2)))
    p.store(lit(7),lit(0))
    assert p.compare(p.load(r),lit(14)) and p.real.raw == {4}
    p.store(lit(0),lit(0))
    assert p.compare(p.load(p.load(lit(101))),lit(0))
    # A later store does not retroactively replace a retained dependent chain.
    q = p.load(p.load(lit(19)))
    p.store(lit(22),lit(0))
    assert p.compare(p.load(q),lit(22))


def exhaustive_walks():
    cases = 0
    # Every small hole set and initial map, every address/value written, and
    # every placement of those writes between dependent LOADs.
    for size,nstores,nloads in ((2,2,4),(3,1,5)):
        words = range(size)
        for digits,hm in product(product(words,repeat=size),range(1,1<<size)):
            holes = {i:digits[i] for i in words if (hm >> i)&1}
            old = dict(enumerate(digits))
            static = HoleIndex(old,holes)
            for writes in product(product(words,repeat=2),repeat=nstores):
                schedules = combinations_with_replacement(range(nloads+1),nstores)
                for times in schedules:
                    for start in range(size+1):
                        p = Paired(old,holes,static)
                        v = lit(start)
                        j = 0
                        for t in range(nloads+1):
                            while j < nstores and times[j] == t:
                                key,value = writes[j]
                                p.store(lit(key),lit(value))
                                j += 1
                            if t != nloads:
                                v = p.load(v)
                        assert p.compare(v,lit(v[0].value))
                        cases += 1
    return cases


def random_replay(rng):
    checks = 0
    for _ in range(1400):
        universe = 48
        old = {k:rng.randrange(universe) for k in rng.sample(range(universe),24)}
        ids = rng.sample(range(universe),rng.randrange(2,11))
        values = rng.sample(range(universe),rng.randrange(1,6))
        holes = {i:rng.choice(values) for i in ids}
        p = Paired(old,holes)
        regs = [lit(rng.randrange(2*universe)) for _ in range(10)]
        for k in range(120):
            i,j,dst = (rng.randrange(len(regs)) for _ in range(3))
            move = rng.randrange(16)
            if move < 4:
                regs[dst] = p.load(regs[i])
            elif move < 6:
                regs[dst] = p.load(lit(rng.choice(ids)))
            elif move < 8:
                p.store(regs[i],regs[j])
            elif move == 8:
                p.store(lit(rng.choice(ids)),lit(0))
            elif move == 9:
                p.store(lit(rng.randrange(universe)),regs[j])
            elif move == 10:
                regs[dst] = regs[i]
                p.budget()
            elif move < 13:
                p.compare(regs[i],regs[j])
            elif move < 15:
                regs[dst] = p.xor(regs[i],regs[j])
            else:
                regs[dst] = lit(rng.randrange(2*universe))
                p.budget()
        for v in regs:
            p.compare(v,lit(v[0].value))
        checks += p.prefixes
    return checks


def valid_seed(layout, segment, word):
    bs = word.to_bytes(layout.word_bytes,'little')
    try:
        a,b,pad,z,c,e,pad2,z2 = map(int,bs.split())
    except ValueError:
        return False
    if (-a,c,pad,z,pad2,z2,e) != (layout.query_flags.start+segment,layout.query_flags.start+segment,1,0,1,0,-b):
        return False
    return b in layout.query_names and bs == layout.packet(layout.data_count+segment,b-layout.query_names.start)


def packed_queries(solver, k):
    book = tuple(product(range(2),repeat=2))
    layout = RowQueryLayout(k,columns=2,packet_bits=2,segment_codebook=book,half_tag=True)
    W = layout.word_bytes
    first = len(layout.public)//W
    tagaddr = first+layout.data_count
    start = tagaddr+1
    hole_ids = list(range(tagaddr,start+layout.query_count))
    order = [*range(layout.data_count),layout.half_slot,
             *range(layout.data_count,layout.data_count+layout.query_count)]
    miss = 1 << (8*W-1)
    clean = miss+1
    n_half = layout.query_count//2
    pairs = negatives = positives = satchecks = maximal = 0
    rows_list = ([1]*k, [1,2]*(k//2), [1,1,2,2]*(k//4)) if k == 8 else ([1]*k,)
    for rows in rows_list:
        sample = layout.render(rows,[0]*layout.query_count,order,half=0)
        # All nonhole input and all auxiliary tables are present before the cut.
        old = {a:int.from_bytes(sample[a*W:(a+1)*W],'little')
               for a in range(len(sample)//W) if a not in hole_ids}
        old.update({miss:miss,clean:clean})
        keys = set()
        for j,seed in product(range(layout.query_count),range(len(book))):
            raw = layout.packet(layout.data_count+j,seed)
            key = int.from_bytes(raw,'little')
            assert key not in keys and key not in old and key > max(hole_ids)
            keys.add(key)
            good = all(rows[2*j+i] >> col & 1 for i,col in enumerate(book[seed]))
            old[key] = miss if not good else clean if (j+1)%n_half == 0 else start+j+1
        static = HoleIndex(old,hole_ids)
        assert not valid_seed(layout,0,0)
        assert not valid_seed(layout,0,int.from_bytes(layout.packet(layout.data_count+1,0),'little'))
        invalid = bytearray(layout.packet(layout.data_count,0))
        invalid[-1] = ord('X')
        assert not valid_seed(layout,0,int.from_bytes(invalid,'little'))
        selected = product(range(len(book)),repeat=layout.query_count) if k == 8 else [
            (0,)*layout.query_count,(0,)*(layout.query_count-1)+(1,)]
        for seeds in selected:
            answers = []
            seen_raw = []
            for half in (0,1):
                raw = layout.render(rows,seeds,order,half=half)
                holes = {a:int.from_bytes(raw[a*W:(a+1)*W],'little') for a in hole_ids}
                p = Paired(old,holes,static)
                tag = p.load(lit(tagaddr))
                assert tag[0].value == int.from_bytes(layout.packet(layout.half_slot,half),'little')
                # Validate the actual word held at *every* known address. The
                # expected flag and allowed name interval need only their bases.
                for j in range(layout.query_count):
                    pkt = p.load(lit(start+j))
                    assert not pkt[0].marked
                    assert valid_seed(layout,j,pkt[0].value)
                head = lit(start+half*n_half)
                for _ in range(2*n_half):
                    head = p.load(head)
                ans = p.compare(head,lit(miss))
                decoded = [book[v] for v in seeds]
                expected = any(not (rows[2*j+t] >> col & 1)
                               for j in range(half*n_half,(half+1)*n_half)
                               for t,col in enumerate(decoded[j]))
                assert ans == expected
                assert (p.real.c,p.real.m,len(p.real.endpoints)) == (1,0,0)
                assert p.real.raw <= keys and 1 <= len(p.real.raw) <= n_half
                if solver and (k>8 or sum(seeds)%29 == 0 or tuple(seeds) == (0,0,0,1)):
                    result = run([solver,'-q'],input=raw,check=False,capture_output=True)
                    assert result.returncode == (10 if ans else 20)
                    satchecks += 1
                seen_raw.append(len(p.real.raw))
                answers.append(ans)
                positives += ans
                negatives += not ans
            if answers[0] != answers[1]:
                left = layout.render(rows,seeds,order,half=0)
                right = layout.render(rows,seeds,order,half=1)
                assert sum((a ^ b).bit_count() for a,b in zip(left,right,strict=True)) == 1
                pairs += 1
                maximal += all(n == n_half for n in seen_raw)
    assert pairs and maximal
    return positives,negatives,pairs,maximal,satchecks


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--solver', help='Optional CaDiCaL path for actual CNF checks.')
    arg = parser.parse_args()
    hazards()
    print(f'{exhaustive_walks():,} exhaustively enumerated small original-hole and write histories.')
    print(f'{random_replay(Random(7704)):,} step prefixes pass eager/delayed value and resource checks.')
    for size in (8,16,32,64):
        y,n,p,b,c = packed_queries(arg.solver,size)
        print(f'{size} rows: {y:,} positive and {n:,} negative physical files; {p} opposite pairs, '
              f'{b} using all {size//4} selected segment keys on both signs; {c} CaDiCaL checks.')
