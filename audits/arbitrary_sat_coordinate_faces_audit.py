"""Place and toggle individual bits of packed, fixed-stride 3-CNF clauses."""
from itertools import combinations, permutations, product
from random import Random


def encode(clause, w):
    record = 0
    for slot, lit in enumerate(clause):
        field = abs(lit) | ((lit < 0) << w)
        record |= field << (slot*(w+1))
    return record


def decode(record, w):
    out = []
    for slot in range(3):
        field = record >> (slot*(w+1))
        name = field & ((1 << w)-1)
        assert 0 < name < 2**w
        out.append(-name if (field >> w) & 1 else name)
    return tuple(out)


def unit_propagate(clauses):
    vals = {}
    while True:
        pending = False
        changed = False
        for clause in clauses:
            if any(vals.get(abs(lit)) == (lit > 0) for lit in clause):
                continue
            avail = {lit for lit in clause if abs(lit) not in vals}
            if not avail:
                return False
            pending = True
            if len(avail) == 1:
                lit = avail.pop()
                vals[abs(lit)] = lit > 0
                changed = True
        if not changed:
            return not pending


def is_cycle(p):
    j, count = p[0], 1
    while j:
        j = p[j]
        count += 1
    return count == len(p)


def single_cycle(bits, n):
    try:
        rows = [bits[i*n:(i+1)*n] for i in range(n)]
        if any(sum(row) != 1 for row in rows):
            return False
        dest = [row.index(1) for row in rows]
        return len(set(dest)) == n and is_cycle(dest)
    except ValueError:
        return False


def template(n, w, carriers):
    count, fixed = 2**w, 1
    assert len({r for r, _, _ in carriers}) == n*n
    clauses = [(fixed, -fixed, fixed)] * count
    used, slots = {fixed}, {r for r, _, _ in carriers}
    static = [(-fixed,)*3]
    signals = []
    for r, slot, bit in carriers:
        rec = [fixed]*3
        if bit == w:
            name = next(k for k in range(1, count) if k not in used)
            used.add(name)
            rec[slot] = name
            signals.append(-name)  # input bit one selects a negative unit
        else:
            lo = next(k for k in range(1, count) if not k & (1 << bit)
                      and k not in used and (k ^ (1 << bit)) not in used)
            hi = lo ^ (1 << bit)
            used.update([lo, hi])
            rec[slot] = lo
            static.extend([(lo,hi,hi),(-lo,-hi,-hi)])
            signals.append(hi)
        clauses[r] = tuple(rec)
    # Direct width-three checker for n=2,3. Exact row and column counts,
    # then exclude the permutations consisting of more than one cycle.
    def padded(row):
        return tuple(row+[row[-1]]*(3-len(row)))
    for stripe in ([signals[i*n:(i+1)*n] for i in range(n)]
                   + [signals[i::n] for i in range(n)]):
        static.append(padded(stripe))
        static.extend([(-a,-b,-b) for a,b in combinations(stripe, 2)])
    for p in permutations(range(n)):
        if not is_cycle(p):
            static.append(padded([-signals[i*n+j] for i,j in enumerate(p)]))
    positions = [r for r in range(count) if r not in slots]
    assert len(positions) >= len(static)
    for r,clause in zip(positions, static):
        clauses[r] = clause
    return [encode(c, w) for c in clauses]


def check(n, w, carriers):
    words = template(n, w, carriers)
    # Only the selected physical positions can change. The header specifying
    # (v=2**w-1,C=2**w) is constant and omitted from this record array.
    base = [decode(word, w) for word in words]
    trials = 0
    for raw in product((0,1), repeat=n*n):
        clauses = base.copy()
        for (r,slot,bit),value in zip(carriers,raw):
            shift = slot*(w+1)+bit
            assert (words[r] >> shift) & 1 == 0
            clauses[r] = decode(words[r] ^ (value << shift), w)
        assert unit_propagate(clauses) == single_cycle(raw, n)
        trials += 1
    return trials


if __name__ == "__main__":
    rng = Random(249)
    total = 0
    for n,w in [(2,6),(3,7)]:
        for b in [0,w-1,w,None]:
            rows = rng.sample(range(2**w),n*n)
            carriers = [(r,rng.randrange(3),b if b is not None else rng.randrange(w+1)) for r in rows]
            total += check(n,w,carriers)
    print(f"{total} physically toggled 3-CNFs matched the cycle predicate by unit propagation")
