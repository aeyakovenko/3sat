"""Exhaust the four-cube cycles and test ordinary proper files after arbitrary shuffles."""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations, permutations
from random import Random

FULL = (1 << 16) - 1
GRAY = tuple(i ^ (i >> 1) for i in range(16))
EXACT_ONE_DROP = frozenset([2, 3, 6, 7, 14, 15])
EQUALITY_DROP = frozenset([0, 3, 6, 9, 10, 15])
DUPLICATED_DROP = frozenset([0, 1, 3, 4, 7, 8])


def edge_list(cycle):
    return list(zip(cycle, cycle[1:] + cycle[:1]))


def normalize(cycle):
    j = cycle.index(0)
    return min(tuple(cycle[(j + sign * i) % 16] for i in range(16)) for sign in (-1, 1))


def cycle_orbits():
    pending = set()

    def extend(seq, seen):
        if len(seq) == 16:
            if seq[-1] in (1, 2, 4, 8):
                pending.add(normalize(seq))
            return
        for bit in (1, 2, 4, 8):
            val = seq[-1] ^ bit
            if val not in seen:
                extend(seq + [val], seen | {val})

    extend([0], {0})
    assert len(pending) == 1344
    reps = []
    while pending:
        cycle = min(pending)
        orbit = set()
        for perm in permutations(range(4)):
            permuted = [sum(((v >> i) & 1) << j for i, j in enumerate(perm)) for v in cycle]
            for offset in range(16):
                orbit.add(normalize([v ^ offset for v in permuted]))
        assert orbit <= pending
        reps.append((cycle, len(orbit)))
        pending -= orbit
    return reps


PATTERNS = [
    (scope, sum(1 << v for v in range(16) if v & scope == val))
    for scope in range(1, 16) if scope.bit_count() <= 2
    for val in range(16) if val & scope == val
]


@lru_cache(None)
def project(rows, scope):
    return sum(1 << i for i, (coords, fiber) in enumerate(PATTERNS)
               if coords & scope == coords and (fiber & rows) == 0)


@lru_cache(None)
def permitted(bans, scope=15):
    rows = FULL
    for i, (coords, fiber) in enumerate(PATTERNS):
        if bans >> i & 1 and coords & scope == coords:
            rows &= ~fiber
    return rows


def local_rounds(cycle, dropped):
    tables = {15 ^ axis: FULL for axis in (1, 2, 4, 8)}
    for j, (u, v) in enumerate(edge_list(cycle)):
        if j not in dropped:
            tables[15 ^ (u ^ v)] &= ~((1 << u) | (1 << v))
    bans = 0
    for depth in range(1, 7):
        enlarged = bans
        for scope, raw in tables.items():
            if raw != FULL:
                enlarged |= project(permitted(bans, scope) & raw, scope)
        bans = enlarged
        if all(permitted(bans, scope) & ~raw == 0 for scope, raw in tables.items()):
            return depth
    return None


def audit_census():
    reps = cycle_orbits()
    lasts = []
    sharp = []
    defects = Counter()
    for c, multiplicity in reps:
        rounds = Counter()
        for missing in range(6):
            for drop in combinations(range(16), missing):
                depth = local_rounds(c, drop)
                assert depth is not None
                rounds[depth] += 1
                if depth == 6:
                    sharp.append((c, drop))
        assert sum(rounds.values()) == 6885
        lasts.append((multiplicity, max(rounds)))
        for drop in combinations(range(16), 6):
            missing = set(drop)
            vertices = [c[i] for i in range(16) if i in missing and (i-1)%16 in missing]
            rows = sum(1<<v for v in vertices)
            extra = permitted(project(rows, 15)) & ~rows
            if extra:
                cols = {min(col,tuple(1-t for t in col)) for j in range(4)
                        if len(set(col := tuple((v>>j)&1 for v in vertices))) > 1}
                miss = extra.bit_length()-1
                axes = {}
                for j in range(4):
                    cvec = tuple(((v^miss)>>j)&1 for v in vertices)
                    if len(set(cvec))>1:
                        axes.setdefault(min(cvec,tuple(1-x for x in cvec)),j)
                chosen = tuple(axes.values())
                projected = {sum((((v^miss)>>j)&1)<<i for i,j in enumerate(chosen))
                             for v in vertices}
                rot = lambda x: ((x<<1)&7)|(x>>2)
                assert {v for v in projected if rot(v) in projected and rot(rot(v)) in projected} == {1,2,4}
                assert len(projected)==len(vertices)
                defects[len(vertices),len(cols),extra.bit_count()] += multiplicity
    assert defects == {(3,3,1):103680,(4,3,1):43392,(5,3,1):3456}
    assert sorted(lasts) == sorted(zip([192, 192, 96, 48, 384, 192, 48, 96, 96],
                                        [5, 6, 5, 5, 4, 4, 4, 3, 3]))
    edges = edge_list(GRAY)
    rows = FULL
    not_bijunctive = Counter()
    for mask in range(1 << 16):
        rows = sum(1 << GRAY[i] for i in range(16)
                   if mask >> i & 1 and mask >> ((i - 1) % 16) & 1)
        if permitted(project(rows, 15)) != rows:
            not_bijunctive[mask.bit_count()] += 1
    assert min(not_bijunctive) == 6
    vertices = set(range(16)) - {v for i, edge in enumerate(edges)
                                if i not in EXACT_ONE_DROP for v in edge}
    assert vertices == {2, 4, 8}
    return reps, lasts, not_bijunctive, sharp


def bank(cycle, dropped, names):
    clauses = []
    for i, (u, v) in enumerate(edge_list(cycle)):
        if i in dropped:
            continue
        clauses.append(tuple(-name if u >> j & 1 else name for j, name in enumerate(names)
                             if (u ^ v) != 1 << j))
    return clauses


def emit(clauses, rng, declared=None):
    shuffled = [list(c) for c in clauses]
    rng.shuffle(shuffled)
    for c in shuffled:
        rng.shuffle(c)
    n = max((abs(lit) for c in shuffled for lit in c), default=0)
    return (f"p cnf {n if declared is None else declared} {len(shuffled)}\n" +
            "".join(" ".join(map(str, c)) + " 0\n" for c in shuffled)).encode("ascii")


def parse(raw):
    head, *lines = raw.splitlines()
    p, cnf, n, count = head.split()
    assert (p, cnf) == (b'p', b'cnf') and int(count) == len(lines)
    clauses = []
    for line in lines:
        a, b, c, end = map(int, line.split())
        assert end == 0 and len({abs(a), abs(b), abs(c)}) == 3
        assert all(0 < abs(l) <= int(n) for l in (a, b, c))
        clauses.append((a, b, c))
    return clauses


def binary_rounds(clauses):
    """Scope data only. The caller supplies no bank names, cycles or partition."""
    tables = {}
    for clause in clauses:
        c = tuple(sorted(clause, key=abs))
        names = tuple(map(abs, c))
        false_row = sum((lit < 0) << j for j, lit in enumerate(c))
        tables[names] = tables.get(names, 255) & ~(1 << false_row)
    indices = [(j,) for j in range(3)] + list(combinations(range(3), 2))
    banned = set()
    for _ in range(6):
        delta = set()
        for names, table in tables.items():
            positive = [tuple(name if (val >> j & 1) else -name
                              for j, name in enumerate(names)) for val in range(8)]
            small = [{tuple(vals[i] for i in sub) for sub in indices} for vals in positive]
            visible = set.union(*small)
            surviving = [small[val] for val in range(8)
                         if (table >> val) & 1 and banned.isdisjoint(small[val])]
            delta.update(visible.difference(set().union(*surviving)))
        banned.update(delta)
    return banned


def subsumed(c, bans):
    fiber = tuple(sorted((-lit for lit in c), key=abs))
    return any(term in bans for size in (1, 2) for term in combinations(fiber, size))


def evaluates(clauses, values):
    return all(any(values[abs(lit)] == (lit > 0) for lit in c) for c in clauses)


def encode_name(kind, *components):
    # Every component is a signed, nonzero or zero integer. Digit pairs 00..09
    # are the payload. The sign and separator pairs are disjoint from that range.
    parts = [kind]
    for x in components:
        parts.append("11" if x < 0 else "12")
        parts.extend(f"{int(d):02d}" for d in str(abs(x)))
        parts.append("10")
    return int("".join(parts))


def source_wire(lit):
    return encode_name("1", lit)


def compile_sat(source, declared, clone=False):
    source = set(tuple(sorted(c, key=abs)) for c in source)
    active_old = {abs(lit) for c in source for lit in c}
    t, f, g, h = (encode_name("2", i) for i in range(1, 5))
    positive = [(t, f, g), (t, f, h), (t, g, h)]
    positive += [(source_wire(i), source_wire(-i), f)
                 for i in sorted({abs(l) for c in source for l in c})]
    for c in source:
        l1, l2, l3 = sorted(c, key=abs)
        assert len({abs(l1), abs(l2), abs(l3)}) == 3
        z, a, b, u, d = (encode_name("3", l1, l2, l3, i) for i in range(5))
        positive.extend([(z, source_wire(l1), a), (z, source_wire(l2), b),
                         (a, b, u), (z, source_wire(-l3), d)])
    builder = []
    old_wires = {}
    if clone == "single":
        serial = 0

        def fresh():
            nonlocal serial
            serial += 1
            return serial

        def dupl(x, twin, y, z):
            builder.append((DUPLICATED_DROP, (x,y,-twin,z)))

        def pinned_zero():
            p,a,b,c,d,u,v,s,t = (fresh() for _ in range(9))
            dupl(p,a,b,c)
            dupl(-a,-d,u,v)
            dupl(-d,-b,s,t)
            return p

        uses = defaultdict(list)
        for atom in positive:
            x,y,z = ports = tuple(fresh() for _ in range(3))
            for var,port in zip(atom,ports):
                uses[var].append(port)
            dupl(x,fresh(),y,z)
        for var,ports in uses.items():
            old_wires[var] = ports[0]
            if len(ports)==1:
                continue
            prev = None
            for j,port in enumerate(ports):
                nxt = fresh() if j+1<len(ports) else None
                arms = [x for x in (prev,port,nxt) if x is not None]
                while len(arms)<3:
                    arms.append(fresh())
                dupl(arms[0],arms[1],-arms[2],pinned_zero())
                prev = nxt
    elif clone:
        uses = defaultdict(list)
        for j,atom in enumerate(positive):
            ports = tuple(encode_name("5", j, k) for k in range(3))
            for var,port in zip(atom,ports):
                uses[var].append(port)
            builder.append((EXACT_ONE_DROP,(encode_name("6",j),) + ports))
        for idx,(var, ports) in enumerate(uses.items()):
            old_wires[var] = ports[0]
            prev = None
            for j,port in enumerate(ports):
                if len(ports) == 1:
                    break
                nxt = encode_name("7",idx,j) if j+1 < len(ports) else None
                names = [x for x in [prev,port,nxt] if x is not None]
                while len(names)<4:
                    names.append(encode_name("8",idx,j,len(names)))
                builder.append((EQUALITY_DROP,tuple(names)))
                prev = nxt
    else:
        for atom in positive:
            old_wires.update({v:v for v in atom})
            private = encode_name("4", *sorted(atom))
            builder.append((EXACT_ONE_DROP,(private,) + atom))
    if clone:
        mult = Counter(abs(x) for _,names in builder for x in names)
        assert max(mult.values()) <= 2
        seen_pairs = set()
        for _,names in builder:
            names = sorted(map(abs,names))
            assert len(set(names))==4
            for pair in combinations(names,2):
                assert pair not in seen_pairs
                seen_pairs.add(pair)
    result = [c for dropped,names in builder for c in bank(GRAY, dropped, names)]
    active = {name:i+1 for i,name in enumerate(sorted({abs(l) for c in result for l in c}))}
    dense = [tuple(active[abs(l)] if l > 0 else -active[abs(l)] for l in c) for c in result]
    return dense, {x:active[old_wires[source_wire(x)]] for x in active_old}, len(active) + declared - len(active_old)


def audit_physical(reps):
    """Independent full model checks on tiny shuffled unannotated files."""
    rng = Random(110327)
    files = 0
    for case in range(252):
        original = []
        base_assignment = rng.randrange(1 << 7)
        for _ in range(1 + case % 5):
            c = rng.choice(reps)[0]
            names = rng.sample(range(1, 8), 4)
            translation = rng.randrange(16)
            cycle = tuple(v ^ translation for v in c)
            missing = set(rng.sample(range(16), rng.randrange(6)))
            if case % 2:
                at = sum(((base_assignment >> (x-1)) & 1) << j for j, x in enumerate(names))
                idx = cycle.index(at)
                missing = {idx, (idx-1) % 16}
                missing.update(rng.sample(sorted(set(range(16)) - missing), rng.randrange(4)))
            original.extend(bank(cycle, missing, tuple(names)))
        parsed = parse(emit(original, rng))
        bans = binary_rounds(parsed)
        assert all(subsumed(c, bans) for c in parsed)
        extracted = [tuple(-v for v in b) for b in bans]
        for row in range(1 << 7):
            assign = {j+1: (row >> j) & 1 for j in range(7)}
            assert evaluates(parsed, assign) == evaluates(extracted, assign)
        files += 1
    return files


def bipartite_cover(adj):
    match = {}

    def augment(u, seen):
        for v in adj[u]:
            if v in seen:
                continue
            seen.add(v)
            if v not in match or augment(match[v], seen):
                match[v] = u
                return True
        return False

    for u in adj:
        augment(u, set())
    left = set(adj) - set(match.values())
    right = set()
    search = list(left)
    while search:
        u = search.pop()
        for v in adj[u]:
            if match.get(v) == u or v in right:
                continue
            right.add(v)
            if v in match and match[v] not in left:
                left.add(match[v])
                search.append(match[v])
    return set(adj) - left, right


def six_kernel_test(reps):
    rng = Random(14405)
    counts = Counter()
    for case in range(240):
        e = 1 + case % 4
        base = rng.randrange(256)
        clauses = []
        for j in range(e + case % 2):
            cycle = rng.choice(reps)[0]
            names = rng.sample(range(1, 9), 4)
            chosen = sum(((base >> (v-1)) & 1) << i for i,v in enumerate(names))
            idx = cycle.index(chosen)
            omitted = {idx, (idx-1)%16}
            if case % 3 == 0 and j < e:
                cycle = GRAY
                chosen = rng.choice([2,4,8]) ^ chosen
                cycle = tuple(v ^ chosen for v in cycle)
                omitted = EXACT_ONE_DROP
            else:
                n = 6 if j < e else rng.randrange(2,6)
                omitted.update(rng.sample(sorted(set(range(16))-omitted), n-2))
            if case % 10 == 0 and j == e-1:
                cycle = tuple(v ^ 7 for v in cycle)
            clauses.extend(bank(cycle, omitted, tuple(names)))
        clauses = parse(emit(clauses, rng))
        bans = binary_rounds(clauses)
        residual = [c for c in clauses if not subsumed(c, bans)]
        core = {abs(l) for c in residual for l in c}
        assert len(core) <= 4*e
        for w in combinations(sorted(core), 4):
            aset = set(w)
            local = [c for c in clauses if all(abs(l) in aset for l in c)]
            rows = []
            for val in range(16):
                at = {x:bool(val>>j&1) for j,x in enumerate(w)}
                if evaluates(local, at):
                    rows.append(at)
            for n in (1, 2):
                for coords in combinations(w,n):
                    seen = {tuple(x if row[x] else -x for x in coords) for row in rows}
                    for a in range(1<<n):
                        term = tuple(x if a>>j&1 else -x for j,x in enumerate(coords))
                        if term not in seen:
                            bans.add(term)
        binary = [tuple(-l for l in b) for b in bans]
        worlds = [{i+1:bool(x>>i&1) for i in range(8)} for x in range(256)]
        domain = [w for w in worlds if evaluates(binary, w)]
        adj = defaultdict(set)
        edges = []
        for c in residual:
            event = sum(1<<i for i,w in enumerate(domain) if not evaluates([c], w))
            if event:
                scope = tuple(sorted(abs(x) for x in c))
                adj[event].add(scope)
                edges.append((event,scope,c))
        le,ri = bipartite_cover(adj)
        assert len(le)+len(ri) <= e
        selected = [next((c for k,s,c in edges if k==event),None) for event in le]
        selected += [c for k,scope,c in edges if scope in ri]
        backdoor = {abs(c[0]) for c in selected[:len(le)]} | {scope[0] for scope in ri}
        assert len(backdoor)<=e and all(any(abs(l) in backdoor for l in c) for c in selected)
        assert len(selected)==0 or len(domain)>0
        for w in worlds:
            assert evaluates(clauses,w) == (evaluates(binary,w) and evaluates(selected,w))
        counts[len(le)+len(ri)] += 1
    return sorted(counts.items())


def check_compiler():
    try:
        from pysat.solvers import Cadical195
    except ImportError:
        return "unavailable (install python-sat to run the independent uniqueness check)"
    rng = Random(110427)
    cases = 0
    for case in range(32):
        vs = 3 + (case % 3)
        source = [tuple(x if rng.randrange(2) else -x for x in rng.sample(range(1, vs+1), 3))
                  for _ in range(1 + case % 7)]
        if case % 5 == 0:
            source.append(tuple(reversed(source[0])))
        if case % 7 == 0:
            source.extend(tuple(-x if mask >> (x-1) & 1 else x for x in range(1, 4))
                          for mask in range(8))
        printed, wire, declared = compile_sat(source, vs + case % 4, clone=[False, True, "single"][case % 3])
        reduced = parse(emit(printed, rng, declared))
        ids = {name: i+1 for i, name in enumerate(sorted({abs(l) for c in reduced for l in c}))}
        dense = [[ids[abs(l)] if l > 0 else -ids[abs(l)] for l in c] for c in reduced]
        free = sorted({abs(l) for c in source for l in c})
        assert declared - len(ids) == (vs + case % 4) - len(free)
        with Cadical195(bootstrap_with=dense) as solver:
            for vals in range(1 << len(free)):
                assignment = {x: bool(vals >> i & 1) for i, x in enumerate(free)}
                units = [ids[wire[x]] if val else -ids[wire[x]] for x,val in assignment.items()]
                sat = solver.solve(assumptions=units)
                assert sat == evaluates(source, assignment)
                if sat:
                    model = solver.get_model()
                    # Active names all occur; disallow exactly this total completion.
                    solver.add_clause([-lit for lit in model])
                    assert not solver.solve(assumptions=units)
                cases += 1
    return f"32 physical six-omission reductions (21 on incidence-degree-two clones, 10 on one fixed mask), {cases} source assignments"


if __name__ == "__main__":
    reps, stats, nonbinary, sharp = audit_census()
    print("cycles 1344 in 9 orbits; 61965 masks up to five; (orbit, max direct-subsumer round)", stats)
    print("all 65536 reflected masks; non-bijunctive by omission count", sorted(nonbinary.items()))
    print("six-round witnesses on the unique orbit", [m for c,m in sharp])
    print("unannotated physical files:", audit_physical(reps))
    print("240 hidden mixed six-omission kernels, cover sizes:", six_kernel_test(reps))
    print("CaDiCaL:", check_compiler())
