"""Exhaust signed DIMACS replacements and compare guarded walks with certificates."""
from itertools import count, product

from coded_row_last_packet_audit import model_count
from late_clause_replay_audit import Layout


class Gates:
    def __init__(self, reserved):
        self.clauses = []
        self.names = (v for v in count(1) if v not in reserved)

    def fresh(self):
        return next(self.names)

    def clause(self, *lits):
        distinct = set(lits)
        if not any(-v in distinct for v in lits):
            self.clauses.append(tuple(dict.fromkeys(lits)))

    def both(self, x, y, out=None):
        if out is None:
            out = self.fresh()
        self.clause(-out, x)
        self.clause(-out, y)
        self.clause(out, -x, -y)
        return out

    def exclusive_summary(self, ports):
        """Forbid two true ports and return a literal for a nonempty list's OR."""
        acc, *rest = ports
        for lit in rest:
            self.clause(-acc, -lit)
            acc = -self.both(-acc, -lit)
        return acc

    def choose(self, size):
        flags = [self.fresh() for _ in range(size)]
        self.clause(self.exclusive_summary(flags))
        return flags


class Chain:
    def __init__(self, vertices, guarded_arcs, supports=((0, 1), (1,))):
        columns = 1 + max(max(inputs) for inputs in supports)
        self.tags = [(10*v + 12, 10*v + 13) for v in range(vertices)]
        gates = Gates({v for pair in self.tags for v in pair})
        self.row = gates.choose(2)
        self.source = gates.choose(vertices)
        target = gates.choose(vertices)
        mode = gates.fresh()
        for t, (neg, pos) in zip(target, self.tags):
            gates.both(t, mode, pos)
            gates.both(t, -mode, neg)
        self.library = [gates.fresh() for _ in range(4)]
        for i, row in enumerate(self.row):
            for mask, wire in enumerate(self.library):
                gates.clause(-row, wire if mask >> i & 1 else -wire)
        self.inputs = [gates.fresh() for _ in range(columns)]
        outputs = []
        for bank in supports:
            wire = self.inputs[bank[0]]
            for h in bank[1:]:
                y = self.inputs[h]
                parity = gates.fresh()
                for a, b in product(range(2), repeat=2):
                    gates.clause(-wire if a else wire, -y if b else y, parity if a ^ b else -parity)
                wire = parity
            outputs.append(wire)
        cut = [gates.fresh() for _ in range(vertices)]
        incoming = [[gates.both(q, mode)] for q in self.source]
        outgoing = [[gates.both(q, mode)] for q in target]
        for u, v, j, value in guarded_arcs:
            guard = outputs[j] if value else -outputs[j]
            flow = gates.fresh()
            gates.clause(-flow, guard)
            gates.clause(-cut[u], -guard, cut[v])
            outgoing[u].append(flow)
            incoming[v].append(flow)
        for s, t, side, ins, outs in zip(self.source, target, cut, incoming, outgoing):
            gates.clause(mode, -s, side)
            gates.clause(mode, -t, -side)
            i = gates.exclusive_summary(ins)
            o = gates.exclusive_summary(outs)
            gates.clause(-i, o)
            gates.clause(i, -o)
        used = {abs(v) for c in gates.clauses for v in c} | set(self.inputs)
        bound = max(used)
        gates.clauses.extend([(-v,) for v in range(1, bound+1) if v not in used])
        bits = 1 << 16
        while True:
            self.layout = Layout(r=3, count=2*columns, bits=bits, variables=bound)
            anchors = self.layout.anchors
            guards = [tuple(-v if pattern >> j & 1 else v for j, v in enumerate(anchors))
                      for pattern in range(1, 8)]
            public = guards + [self.pad(c) for c in gates.clauses]
            header = f'p cnf {anchors[-1]} {len(public)+6*columns}\n'.encode()
            region = header + b''.join(self.layout.record(c) for c in public)
            if len(region)+(1+2*columns)*self.layout.word_bytes <= bits//8:
                break
            bits *= 2
        self.prefix = region + b' ' * (-len(region) % self.layout.word_bytes)

    def pad(self, c):
        return c + self.layout.anchors[:3-len(c)]

    def packet_bytes(self, clauses):
        return self.layout.packet(clauses).to_bytes(self.layout.word_bytes, 'little')

    def data(self, h, mask):
        x, y = self.inputs[h], self.library[mask]
        return self.packet_bytes([self.pad((-x, y)), self.pad((x, -y))])

    def query(self, i, s, t, positive):
        return self.packet_bytes([self.pad((x,)) for x in
                                  [self.row[i], self.source[s], self.tags[t][positive]]])

    def file(self, words):
        data = self.prefix + b''.join(words)
        assert len(data)*8 <= self.layout.bits
        return data.ljust(self.layout.bits // 8)


def reachable(vertices, arcs, masks, row, source):
    keys = [masks[0] ^ masks[1], masks[1]]
    seen = {source}
    work = [source]
    adjacency = [[] for _ in range(vertices)]
    for u, v, index, value in arcs:
        if (keys[index] >> row & 1) == value:
            adjacency[u].append(v)
    while work:
        for v in adjacency[work.pop()]:
            if v not in seen:
                work.append(v)
                seen.add(v)
    return seen


def physical_cases():
    graphs = [
        (3, [(0, 0, 0, 0), (0, 1, 0, 1), (1, 2, 1, 1), (1, 0, 1, 0), (2, 1, 0, 1)],
         list(product(range(4), repeat=2))),
        (4, [(0, 1, 0, 1), (0, 2, 0, 1), (1, 3, 1, 0), (2, 3, 1, 1),
             (2, 0, 1, 1), (3, 3, 0, 1), (1, 3, 1, 0)], [(0, 0), (1, 2), (2, 1), (3, 3)])
    ]
    pairs = masters = 0
    for vertices, arcs, cases in graphs:
        formula = Chain(vertices, arcs)
        for masks in cases:
            original = [formula.data(h, mask) for h, mask in enumerate(masks) for _ in range(2)]
            assert model_count(formula.file(original), 1) == 1
            masters += 1
            for i, s in product(range(2), range(vertices)):
                answers = reachable(vertices, arcs, masks, i, s)
                for t in range(vertices):
                    queries = [formula.query(i, s, t, mode) for mode in (0, 1)]
                    assert [(a, b) for a, b in zip(*queries) if a != b] == [(50, 51)]
                    for slot in range(4):
                        for mode, packet in enumerate(queries):
                            words = original.copy()
                            words[slot] = packet
                            assert model_count(formula.file(words), 1) == int(mode == (t in answers))
                        pairs += 1
    return masters, pairs


def all_three_vertex_graphs():
    vertices = range(3)
    possible = list(product(vertices, repeat=2))
    checked = 0
    for mask in range(1 << len(possible)):
        arcs = [edge for i, edge in enumerate(possible) if mask >> i & 1]
        # Enumerate capacity-one flows once per graph by recording admissible imbalances.
        endpoints = set()
        for subset in range(1 << len(arcs)):
            ins, outs = [0]*3, [0]*3
            for i, (u, v) in enumerate(arcs):
                if subset >> i & 1:
                    ins[v] += 1
                    outs[u] += 1
            for s, t in product(vertices, repeat=2):
                if all(ins[v]+(v == s) == outs[v]+(v == t) <= 1 for v in vertices):
                    endpoints.add((s, t))
        for s, t in product(vertices, repeat=2):
            has_cut = any(side >> s & 1 and not side >> t & 1 and
                          all(not side >> u & 1 or side >> v & 1 for u, v in arcs)
                          for side in range(8))
            answer = t in reachable(3, [(u, v, 0, 0) for u, v in arcs], (0, 0), 0, s)
            assert ((s, t) in endpoints) == answer == (not has_cut)
            checked += 1
    return checked


def all_flipped(y, m):
    groups = m//6
    parity, residue = 0, 0
    for i in range(groups):
        shift = 6*i
        c = ((y >> shift) ^ (y >> (shift+1))) & 1
        pos = shift+2+2*c
        parity ^= ((y >> pos) ^ (y >> (pos+1))) & 1
        residue = (residue+c) % 3
    return y ^ (((1 << m)-1) if parity ^ (residue == 0) else 0)


def controller(m, named=False):
    g = m//6

    def dispatch(key):
        stage, h, par, residue, saved = key
        if stage == 'start':
            return h, [('c0', 0, b, 0, 0) for b in range(2)]
        if stage == 'c0':
            return 6*h, [('c1', h, par, residue, b) for b in range(2)]
        if stage == 'c1':
            return 6*h+1, [('p0', h, par, (residue + (saved ^ b)) % 3, saved ^ b) for b in range(2)]
        if stage == 'p0':
            return 6*h+2+2*saved, [('p1', h, par ^ b, residue, saved) for b in range(2)]
        if stage == 'p1':
            keys = []
            for b in range(2):
                if h+1 == g:
                    keys.append(('yes' if par ^ b ^ (residue == 0) else 'no', 0, 0, 0, 0))
                else:
                    keys.append(('c0', h+1, par ^ b, residue, 0))
            return 6*h+3+2*saved, keys
        return None

    states = [('start', j, 0, 0, 0) for j in range(m)]
    ids = {k: i for i, k in enumerate(states)}
    arcs = []
    for source, key in enumerate(states):
        item = dispatch(key)
        if item is None:
            continue
        j, targets = item
        for b, dest in enumerate(targets):
            if dest not in ids:
                ids[dest] = len(states)
                states.append(dest)
            arcs.append((source, ids[dest], j, b))
    if named:
        return states, arcs
    return len(states), arcs, ids[('yes', 0, 0, 0, 0)]


def nonlinear_audit():
    truth_checks = physical = extensions = 0
    for m in (6, 8, 12):
        n, arcs, terminal = controller(m)
        branch = {(v, bit): (j, dest) for v, dest, j, bit in arcs}
        # A deterministic state queries exactly one coordinate.
        state_var = {v: j for v, _, j, _ in arcs}
        full = (1 << m)-1
        for y in range(1 << m):
            z = all_flipped(y, m)
            assert all_flipped(z, m) == y and all_flipped(y ^ full, m) == z ^ full
            for j in range(m):
                v = j
                steps = 0
                while v in state_var:
                    k = state_var[v]
                    _, v = branch[v, y >> k & 1]
                    steps += 1
                assert steps == 1+4*(m//6)
                assert (v == terminal) == bool(z >> j & 1)
                truth_checks += 1
        if m == 12:
            # A surjective fresh-coordinate map after prescribing the old raw data.
            # Data are (old, fresh) and generate G(old,fresh)=pad(old) XOR fresh.
            # Independently count every old answer fiber, then perform the inverse lift.
            from collections import Counter
            for old in range(16):
                counts = Counter(all_flipped(old ^ fresh, m) & 63 for fresh in range(1 << m))
                assert set(counts.values()) == {64} and len(counts) == 64
                for old_z in counts:
                    new_z = (old << 6) ^ old_z
                    fresh = old ^ all_flipped(new_z, m)
                    assert all_flipped(old ^ fresh, m) == new_z
                    extensions += 1
        if m == 12:
            # Check the canonical three-pivot identity tail below with *two* fresh groups.
            # g0=0 uses no old groups here; a general g0 has the same additive update.
            for wanted in range(3):
                for payload in (0, 1):
                    for free in range(1 << 9):
                        bits = [0] * 12
                        independent = [1, 3, 4, 5, 7, 8, 9, 10, 11]
                        for h, position in enumerate(independent):
                            bits[position] = free >> h & 1
                        # p0 XOR q0 replaces the stored q0 coordinate in this parametrization.
                        bits[0] = bits[1] ^ int(wanted > 0)
                        bits[6] = bits[7] ^ int(wanted > 1)
                        def tail_action():
                            cs = [bits[h] ^ bits[h+1] for h in (0, 6)]
                            ps = [bits[h+2+2*c] ^ bits[h+3+2*c] for h, c in zip((0, 6), cs)]
                            return sum(cs) % 3, ps[0] ^ ps[1]
                        correction = tail_action()[1] ^ payload
                        bits[2] ^= correction
                        bits[4] ^= correction
                        assert tail_action() == (wanted, payload)
                        extensions += 1
        if m == 6:
            formula = Chain(n, arcs, tuple((j,) for j in range(m)))
            for y in (0, 1, 21, 63):
                # Use dissimilar bit columns in the second row.
                masks = [(y >> h & 1) | (((3*y+7) >> h & 1) << 1) for h in range(m)]
                base = [formula.data(h, value) for h, value in enumerate(masks) for _ in range(2)]
                for i, start in product(range(2), range(m)):
                    raw_row = sum((mask >> i & 1) << h for h, mask in enumerate(masks))
                    expected = all_flipped(raw_row, m) >> start & 1
                    for mode in (0, 1):
                        slot = (i*m+start) % len(base)
                        words = base.copy()
                        words[slot] = formula.query(i, start, terminal, mode)
                        assert model_count(formula.file(words), 1) == int(expected == mode)
                        physical += 1
    from math import comb
    for g in range(4, 80):
        coeffs = [sum(comb(k, weight) for weight in range(0, k+1, 3)) % 2 for k in range(1, g+1)]
        assert coeffs == [int(k % 3 != 0) for k in range(1, g+1)]
        assert max(k for k, c in enumerate(coeffs, 1) if c) == g-int(g % 3 == 0)
    return truth_checks, physical, extensions


def embedded_state_audit():
    old, old_arcs = controller(6, named=True)
    new, new_arcs = controller(18, named=True)
    new_ids = {key: v for v, key in enumerate(new)}
    mapping = {v: new_ids[key] for v, key in enumerate(old)}
    inverse = {new_v: old_v for old_v, new_v in mapping.items()}

    def enabled(arcs, y):
        return {u: (index, v) for u, v, index, guard in arcs if (y >> index & 1) == guard}

    def follow(arcs, y, s):
        vertices, transcript = {s}, []
        while s in arcs:
            i, s = arcs[s]
            transcript.append((i, y >> i & 1))
            assert s not in vertices
            vertices.add(s)
        return vertices, transcript

    qualifying = []
    for tail in range(1 << 12):
        par = residues = 0
        for shift in (0, 6):
            c = ((tail >> shift) ^ (tail >> (shift+1))) & 1
            i = shift+2+2*c
            par ^= ((tail >> i) ^ (tail >> (i+1))) & 1
            residues += c
        if residues % 3 == 0 and par == 0:
            qualifying.append(tail)
    pairs = 0
    for y in range(64):
        short = enabled(old_arcs, y)
        for tail in qualifying[::32]:
            large = y | tail << 6
            longer = enabled(new_arcs, large)
            for s in range(len(old)):
                visits, reads = follow(short, y, s)
                extended, longer_reads = follow(longer, large, mapping[s])
                assert {inverse[v] for v in extended if v in inverse} == visits
                assert longer_reads[:len(reads)] == reads
                pairs += len(old)
    return pairs


def all_endpoint_index():
    m = 24
    groups = m//6
    states, arcs = controller(m, named=True)
    levels = {'c0': 0, 'c1': 1, 'p0': 2, 'p1': 3}
    def level(key):
        stage, h, *_ = key
        if stage == 'start':
            return -1
        return 4*h+levels[stage] if stage in levels else 4*groups

    rows = [0, 1, 149, 0x5a5a5a, 0xff00fe, 0x193804, 0x788552, 0xffffff]
    words = [sum(((y >> j) & 1) << i for i, y in enumerate(rows)) for j in range(m)]
    live = (1 << len(rows))-1
    par = [0]
    residue = [[live, 0, 0]]
    for start in range(0, m, 6):
        a, b, p0, p1, q0, q1 = words[start:start+6]
        c, p, q = a ^ b, p0 ^ p1, q0 ^ q1
        par.append(par[-1] ^ p ^ ((p ^ q) & c))
        residue.append([(residue[-1][r] & (live ^ c)) | (residue[-1][(r-1)%3] & c)
                        for r in range(3)])

    checked = 0
    for i, y in enumerate(rows):
        next_state = {states[u]: states[v] for u, v, k, b in arcs if y >> k & 1 == b}
        def locate(s, target):
            if level(s) > level(target):
                return False
            while level(s) < level(target) and s[0] != 'c0':
                s = next_state[s]
            if s[0] == 'c0' and level(s) < level(target):
                left = s[1]
                right = min(level(target)//4, groups-1)  # leave the final group to produce its terminus
                if right > left:
                    get_residue = lambda p: next(r for r in range(3) if residue[p][r] >> i & 1)
                    acc = s[2] ^ ((par[right] ^ par[left]) >> i & 1)
                    mod = (s[3] + get_residue(right) - get_residue(left)) % 3
                    s = ('c0', right, acc, mod, 0)
                while level(s) < level(target):
                    s = next_state[s]
            return s == target
        for s in states:
            actual = {s}
            v = s
            while v in next_state:
                v = next_state[v]
                actual.add(v)
            for target in states:
                assert locate(s, target) == (target in actual)
                checked += 1
    return checked


if __name__ == '__main__':
    print(f'{all_three_vertex_graphs()} graph/start/target triples with exhaustive flows and cuts')
    masters, pairs = physical_cases()
    print(f'{masters} master files, {pairs} one-ASCII-bit signed pairs at every marked slot')
    routes, files, lifts = nonlinear_audit()
    print(f'{routes} nonlinear walks, {files} physical nonlinear DIMACS queries, {lifts} verified lifts')
    print(f'{embedded_state_audit()} embedded source-target verdicts and their source transcripts')
    print(f'{all_endpoint_index()} packed interval-index queries on intermediate and terminal states')
