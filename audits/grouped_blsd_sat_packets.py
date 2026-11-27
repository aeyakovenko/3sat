"""Ordinary proper 3-CNFs for a grouped blocked-set-disjointness query."""

from argparse import ArgumentParser
from itertools import product
from random import Random
from subprocess import run

from packed_residue_dimacs import parse_proper_dimacs


def power(n):
    return isinstance(n,int) and n > 0 and (n & (n-1)) == 0


def line(row):
    assert len(row) == 3 and len(set(map(abs,row))) == 3
    return (' '.join(map(str,row))+' 0\n').encode('ascii')


class GroupedLayout:
    cap = 24

    def __init__(self, rows, groups, columns, chunk):
        if not all(map(power,(rows,groups,columns))) or not (1 <= groups <= rows and columns >= 2 and chunk >= 1):
            raise ValueError('expected powers of two, 1 <= groups <= rows, columns >= 2, chunk >= 1')
        self.L,self.Q,self.B = rows,groups,columns
        self.P = rows//groups
        self.qbits,self.cbits = groups.bit_length()-1,columns.bit_length()-1
        self.m = self.qbits+self.P*self.cbits
        self.chunk = min(chunk,self.m)
        # Anchors 1..3 are false. Positive tags 4 and 5 are consecutive names.
        self.maximum = 5
        self.public = [tuple(-j if mask & (1 << (j-1)) else j for j in (1,2,3)) for mask in range(1,8)]
        self.data = self.reserve(rows*columns)
        self.bits = self.reserve(self.m)
        self.tokens = []
        for begin in range(0,self.m,self.chunk):
            part = self.bits[begin:begin+self.chunk]
            names = self.reserve(1 << len(part))
            self.tokens.append(names)
            for value,name in enumerate(names):
                for k,bit in enumerate(part):
                    self.clause(-name,bit if (value >> k)&1 else -bit)
        self.R = len(self.tokens)
        masks = []
        for p in range(self.P):
            begin = self.qbits+p*self.cbits
            col = self.bits[begin:begin+self.cbits]
            current = [-col[0],col[0]]
            for bit in col[1:]:
                current = [self.conj(a,z) for z in (-bit,bit) for a in current]
            masks.append(current)
        hits = []
        for group in range(groups):
            leaves = [self.conj(self.data[((group*self.P+p)*columns)+j],masks[p][j])
                      for p in range(self.P) for j in range(columns)]
            while len(leaves)>1:
                leaves = [-self.conj(-a,-b) for a,b in zip(leaves[::2],leaves[1::2],strict=True)]
            hits.append(leaves[0])
        for bit in self.bits[:self.qbits]:
            hits = [self.mux(bit,a,b) for a,b in zip(hits[::2],hits[1::2],strict=True)]
        out, = hits
        for taglit,wanted in ((4,-out),(5,out)):
            self.clause(-taglit,wanted)
            self.clause(taglit,-wanted)
        n_public = len(self.public)
        n_required = len(self.data)+self.R+1
        self.slots = max(n_required,(n_public+self.cap-1)//self.cap)
        self.filler = self.reserve(self.slots-n_required)
        ell = 1
        while (1 << ell) < 1024*ell*self.slots+2:
            ell += 1
        self.word_bytes = 128*ell
        assert ell == (8*self.word_bytes*self.slots+1).bit_length()
        self.header = f'p cnf {self.maximum} {n_public+self.slots}\n'.encode()
        self.static = [(self.header if a == 0 else b'')+
                       b''.join(line(row) for row in self.public[self.cap*a:self.cap*(a+1)])
                       for a in range(self.slots)]

    def reserve(self, n):
        out = tuple(range(self.maximum+1,self.maximum+n+1))
        self.maximum += n
        return out

    def clause(self, *lits):
        used = list(dict.fromkeys(lits))
        if any(-x in used for x in used):
            return
        for a in (1,2,3):
            if len(used)<3 and a not in map(abs,used):
                used.append(a)
        assert len(used) == 3 and len(set(map(abs,used))) == 3
        self.public.append(tuple(used))

    def conj(self, a, b):
        z, = self.reserve(1)
        self.clause(-z,a)
        self.clause(-z,b)
        self.clause(z,-a,-b)
        return z

    def mux(self, s, lo, hi):
        z, = self.reserve(1)
        self.clause(s,-lo,z)
        self.clause(s,lo,-z)
        self.clause(-s,-hi,z)
        self.clause(-s,hi,-z)
        return z

    def data_packets(self, database):
        if len(database) != self.L or any(mask < 0 or mask >= 1 << self.B for mask in database):
            raise ValueError('bad row mask')
        pins = [(name if (database[i//self.B] >> (i%self.B))&1 else -name,1,2)
                for i,name in enumerate(self.data)]
        return pins+[(z,-1,2) for z in self.filler]

    def query_packets(self, group, columns):
        if not 0 <= group < self.Q or len(columns) != self.P or any(not 0 <= c < self.B for c in columns):
            raise ValueError('bad group query')
        key = group+sum(c << (self.qbits+j*self.cbits) for j,c in enumerate(columns))
        out = []
        for names in self.tokens:
            out.append((names[key % len(names)],1,2))
            key //= len(names)
        assert key == 0
        return out

    def word(self, address, movable):
        raw = self.static[address]+line(movable)
        assert len(raw) <= self.word_bytes
        return raw[:-1].ljust(self.word_bytes-1,b' ')+b'\n'

    def render(self, packets, placement):
        if len(packets) != self.slots or sorted(placement) != list(range(self.slots)):
            raise ValueError('expected a permutation of the slot inventory')
        return b''.join(self.word(a,packets[placement[a]]) for a in range(self.slots))

    def meaning(self, database, group, cols):
        return any(database[group*self.P+p] >> c & 1 for p,c in enumerate(cols))


def audit(solver):
    rng = Random(1094)
    agreements = tested = opposite = solved = 0
    header_both = False
    for dimensions in ((2,1,2,1),(4,2,2,2),(4,2,4,2),(8,4,4,3),(8,2,2,4)):
        z = GroupedLayout(*dimensions)
        assert not z.filler
        small = z.L*z.B <= 8
        bases = list(product(range(1 << z.B),repeat=z.L)) if small else [
            [0]*z.L,[(1 << z.B)-1]*z.L,*[[rng.randrange(1 << z.B) for _ in range(z.L)] for _ in range(24)]]
        for database in bases:
            allcols = list(product(range(z.B),repeat=z.L)) if small else [
                [rng.randrange(z.B) for _ in range(z.L)] for _ in range(10)]
            for cols in allcols:
                full = any(row >> c & 1 for row,c in zip(database,cols,strict=True))
                split = any(z.meaning(database,q,cols[q*z.P:(q+1)*z.P]) for q in range(z.Q))
                assert split == full
                agreements += 1
        # Physical pairs span balanced, mixed, and both constant databases.
        picked = [bases[0],bases[-1],*rng.sample(bases,min(8,len(bases)))]
        for database in picked:
            installed = z.data_packets(database)
            assert len(set(installed)) == len(installed)
            choices = list(product(range(z.B),repeat=z.P))
            if len(choices)>16:
                choices = rng.sample(choices,16)
            for q,cols in product(range(z.Q),choices):
                chosen = z.query_packets(q,cols)
                must = z.meaning(database,q,cols)
                inventory = installed+chosen
                order = list(range(z.slots))
                rng.shuffle(order)
                if tested % 7 == 0:
                    idx = order.index(z.slots-1)
                    order[idx],order[0] = order[0],order[idx]
                    header_both = True
                files = [z.render(inventory+[(4+tag,1,2)],order) for tag in (0,1)]
                address = order.index(z.slots-1)
                diff = [(j,a^b) for j,(a,b) in enumerate(zip(files[0],files[1],strict=True)) if a != b]
                assert len(diff) == 1 and diff[0][1] == 1 and diff[0][0]//z.word_bytes == address
                for tag,raw in enumerate(files):
                    clauses = parse_proper_dimacs(raw)
                    assert len(clauses) == len(z.public)+z.slots
                    if solver and (tested%23 == 0 or (not must and tested%17 == 0)):
                        res = run([solver,'-q'],input=raw,check=False,capture_output=True)
                        assert res.returncode == (10 if must == bool(tag) else 20), (dimensions,q,cols,tag)
                        solved += 1
                tested += 1
                opposite += 1
        # A machine may choose slots adaptively; public text changes by address.
        # Install the data packets in logical order while feeding these full replies.
        unseen = list(range(z.slots))
        where = {}
        cursor = 0
        for i,packet in enumerate(z.data_packets(bases[0])):
            addr = unseen.pop(cursor%len(unseen))
            where[addr] = i
            cursor = sum(z.word(addr,packet))+addr
        tag = unseen.pop(cursor%len(unseen))
        assert len(unseen) == z.R
        where[tag] = z.slots-1
        for r,addr in enumerate(sorted(unseen)):
            where[addr] = z.slots-1-z.R+r
        perm = [where[a] for a in range(z.slots)]
        for sign in (4,5):
            inp = z.render(z.data_packets(bases[0])+z.query_packets(0,[0]*z.P)+[(sign,1,2)],perm)
            assert len(parse_proper_dimacs(inp)) == len(z.public)+z.slots
    assert header_both
    # With an oversized token library the explicit neutral inventory gives each
    # physical word a movable packet at unchanged width.
    extra = GroupedLayout(8,1,2,8)
    assert extra.filler
    pads = extra.data_packets([0]*8)
    assert len(pads) == len(set(pads)) == extra.slots-extra.R-1
    large = extra.render(pads+extra.query_packets(0,[0]*8)+[(4,1,2)],list(range(extra.slots)))
    assert len(parse_proper_dimacs(large)) == len(extra.public)+extra.slots
    print(f'{agreements:,} grouped/full query identities; {opposite:,} proper physical one-bit pairs, '
          f'{solved} independent CaDiCaL verdicts; adaptive slot and oversized-library checks passed.')


if __name__ == '__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('--solver', help='Optional CaDiCaL executable for physical SAT verdict tests.')
    audit(p.parse_args().solver)
