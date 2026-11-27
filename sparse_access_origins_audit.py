"""Check origin decoding, touched sets, and proper three-literal memory constraints."""

from itertools import combinations, product
from random import Random

from adaptive_sparse_presentation_audit import solver


def choose_edges(sources, maps):
    """Small augmenting-path check using the actual labelled edges."""
    match = {}

    def insert(src, seen):
        half = len(maps[0])
        tag, pos = divmod(src, half)
        for port, mapping in enumerate(maps):
            dest = mapping[pos]
            if dest in seen:
                continue
            seen.add(dest)
            if dest not in match or insert(match[dest][0], seen):
                match[dest] = (src, (tag, port))
                return True
        return False

    assert all(insert(src, set()) for src in sources)
    return match


def check_paths():
    width = 32
    layers = []
    for right in (16, 8):
        maps = []
        high = right.bit_length() - 2
        for a in range(4):
            maps.append([(((p << 1) % right) | (p >> high)) ^ a for p in range(right)])
        layers.append(maps)
    cases = decoded = 0
    for size in range(4):
        for touched in combinations(range(width), size):
            top = {s: (s, ()) for s in touched}
            for maps in layers:
                chosen = choose_edges(top, maps)
                top = {d: (top[src][0], top[src][1]+(port,)) for d,(src,port) in chosen.items()}
            assert len(top) == len(touched)
            for vertex, (source, labels) in top.items():
                pos = vertex
                for (tag, port), maps in zip(reversed(labels), reversed(layers)):
                    pos = tag * len(maps[port]) + maps[port].index(pos)
                assert pos == source
                decoded += 1
            cases += 1
    return cases, decoded


def true_result(x, y, events):
    state = list(x)
    for address, write, data in events:
        if write:
            state[address] = data
        elif state[address] != data:
            return False
    return tuple(state) == y


def authenticated(x, y, events, active):
    if any(x[a] != y[a] for a in range(len(x)) if a not in active):
        return False
    records = [(a, -1, True, x[a]) for a in active]
    records += [(a, t, wr, data) for t, (a, wr, data) in enumerate(events)]
    records += [(a, len(events), False, y[a]) for a in active]
    previous = None
    for a,t,write,data in sorted(records):
        if a != previous and t != -1:
            return False
        if write:
            state = data
        elif state != data:
            return False
        previous = a
    return True


def check_semantics():
    event = tuple(product(range(3), (0,1), (0,1)))
    banks = tuple(product((0,1), repeat=3))
    cases = accepting = routes = 0
    for length in range(3):
        active_sets = [s for t in range(length+1) for s in combinations(range(3),t)]
        for events in product(event, repeat=length):
            for x,y in product(banks, repeat=2):
                actual = true_result(x, y, events)
                verdicts = [authenticated(x, y, events, s) for s in active_sets]
                assert any(verdicts) == actual
                routes += len(verdicts)
                accepting += actual
                cases += 1
    return cases, accepting, routes


class ProperCNF:
    """Small signed-wire compiler; 1,2,3 are reserved for padding."""
    def __init__(self):
        self.last, self.rows = 3, []
        self.one = self.fresh()
        self.clause(self.one)

    def fresh(self):
        self.last += 1
        return self.last

    def clause(self, *lits):
        distinct = list(dict.fromkeys(lits))
        if any(-a in distinct for a in distinct):
            return
        pads = list(range(1, 4-len(distinct)))
        assert all(abs(a) > 3 for a in distinct) and len(distinct) <= 3
        for signs in product((1,-1), repeat=len(pads)):
            self.rows.append(tuple(distinct + [a*b for a,b in zip(pads,signs)]))

    def and_(self, a, b):
        z = self.fresh()
        self.clause(-z,a)
        self.clause(-z,b)
        self.clause(z,-a,-b)
        return z

    def mux(self, ctl, a, b):
        z = self.fresh()
        for test, wire in ((ctl, a),(-ctl, b)):
            self.clause(-test, -wire, z)
            self.clause(-test, wire, -z)
        return z

    def eq_if(self, test, x, y):
        self.clause(-test, x, -y)
        self.clause(-test, -x, y)

    def number(self, x, width):
        return tuple(self.one if (x >> i) & 1 else -self.one for i in range(width))

    def equality(self, xs, ys):
        result = self.one
        for x,y in zip(xs, ys):
            result = self.and_(result, self.mux(x,y,-y))
        return result

    def ordered(self, lhs, rhs):
        le = self.one
        for x,y in zip(lhs,rhs):
            le = self.mux(x,self.and_(y,le),-self.and_(-y,-le))
        self.clause(le)

    def permute(self, rows):
        if len(rows) == 1:
            return rows
        def switches(inrows):
            a,b = [],[]
            for i in range(0,len(inrows),2):
                sw = self.fresh()
                x,y = inrows[i:i+2]
                a.append(tuple(self.mux(sw,p,q) for p,q in zip(x,y)))
                b.append(tuple(self.mux(sw,q,p) for p,q in zip(x,y)))
            return a,b
        a,b = switches(rows)
        if len(rows) == 2:
            return [a[0], b[0]]
        first,second = self.permute(a), self.permute(b)
        top,bot = switches([r for pair in zip(first,second) for r in pair])
        return [r for pair in zip(top,bot) for r in pair]

    def verify(self, solve):
        for row in self.rows:
            assert len(row) == len({abs(x) for x in row}) == 3
        # Serialize the actual proper files, reparse all names, and solve the bytes.
        def literal(w):
            return ('-' if w < 0 else '') + ('7'+format(abs(w),'016b').translate(str.maketrans('01','12')))
        rows = [' '.join(literal(w) for w in row)+' 0' for row in self.rows]
        raw = ('p cnf '+('7'+'2'*16)+' '+str(len(rows))+'\n'+'\n'.join(rows)+'\n').encode('ascii')
        lines = raw.decode('ascii').splitlines()
        parsed = []
        for line in lines[1:]:
            fields = line.split()
            assert fields[-1] == '0'
            def decode(s):
                ident = s.lstrip('-')
                assert ident[0] == '7' and set(ident[1:]) <= {'1','2'}
                n = int(ident[1:].translate(str.maketrans('12','01')),2)
                return -n if s[0] == '-' else n
            parsed.append(tuple(map(decode,fields[:3])))
        assert parsed == self.rows
        return solve(parsed,self.last)


def make_file(x,y,events):
    f = ProperCNF()
    # Two slots independently choose one of all four sources or are inactive.
    slots = [(f.fresh(),(f.fresh(),f.fresh())) for _ in range(2)]
    both = f.and_(slots[0][0], slots[1][0])
    f.clause(-both, -f.equality(slots[0][1],slots[1][1]))
    active_at = [[f.and_(en,f.equality(addr,f.number(a,2))) for en,addr in slots] for a in range(4)]
    for a in range(4):
        if x[a] != y[a]:
            f.clause(*active_at[a])
    def data_at(bits, addr):
        val = -f.one
        for a in range(4):
            val = f.mux(f.equality(addr,f.number(a,2)),f.one if bits[a] else -f.one,val)
        return val
    # time in the two least significant key bits; dummy marker is most significant
    rows = []
    for en,addr in slots:
        rows.append(f.number(0,2)+addr+(-en, f.one, data_at(x,addr)))
        rows.append(f.number(3,2)+addr+(-en,-f.one,data_at(y,addr)))
    for t,(a,w,v) in enumerate(events,1):
        rows.append(f.number(t,2)+f.number(a,2)+(-f.one,f.one if w else -f.one,f.one if v else -f.one))
    while len(rows) < 8:
        rows.append(f.number(0,4)+(f.one,-f.one,-f.one))
    rows = f.permute(rows)
    state = -f.one
    for i,row in enumerate(rows):
        time,addr,dummy,write,data = row[:2],row[2:4],row[4],row[5],row[6]
        if i:
            f.ordered(rows[i-1][:5],row[:5])
        first = f.one if i == 0 else -f.equality(addr,rows[i-1][2:4])
        last = f.one if i == len(rows)-1 else -f.and_(-rows[i+1][4],f.equality(addr,rows[i+1][2:4]))
        f.eq_if(-dummy, first, f.equality(time,f.number(0,2)))
        f.eq_if(-dummy, last, f.equality(time,f.number(3,2)))
        f.eq_if(f.and_(-dummy,-write),data,state)
        state = f.mux(write,data,state)
    return f


def check_files():
    rng = Random(11417)
    solve = solver()
    positives = 0
    for i in range(48):
        x = tuple(rng.randrange(2) for _ in range(4))
        live = list(x)
        events = []
        for _ in range(i % 3):
            a,w,data = rng.randrange(4),rng.randrange(2),rng.randrange(2)
            if w:
                live[a] = data
            else:
                data = live[a]
            events.append((a,w,data))
        if i % 2:
            live[rng.randrange(4)] ^= 1
        if i % 5 == 0 and events:
            a,w,data = events[0]
            events[0] = (a,w,1-data)
        y = tuple(live)
        expected = true_result(x,y,events)
        assert make_file(x,y,events).verify(solve) == expected
        positives += expected
    return 48,positives


if __name__ == '__main__':
    print('touched sets, two-layer origins', check_paths(), flush=True)
    print('event lists with bank pairs, positive, active-set challenges',check_semantics(),flush=True)
    print('serialized proper files, positive',check_files())
