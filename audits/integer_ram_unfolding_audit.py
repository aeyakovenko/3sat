"""the segment lemma behind the unfolding argument.

Claim tested (round-14.md, Lemma S).  Run an additive program on two input
points p, q of the box.  If both runs have the same refined history, then every
lattice point y of the segment [p, q] that does not make a recorded forbidden
address pair coincide has that same history; the recorded forbidden pairs
number at most T(T-1)/2 + nT.  Tested in
  (Z)  the integer model, any number of steps;
  (N)  the native model modulo 2**w inside the window  T + b + 2 <= w,
and then examined outside the window.  There Lemma S itself fails for loads: an
address form with 2^(w-b+1) x coincides with a written address on two parallel
hyperplanes (explicit programs below, the longer one due to the round-14 referee),
and the bound of two wrap numbers per comparison operand fails as well.  The
random search outside the window is only a frequency estimate; it finds none.

Random programs use literal loads, add, sub, the six comparisons both as
branches and as 0/1-writing instructions, direct and register-indirect loads
and stores, big literals, loads through input values and stores onto input
cells.  Usage:  python3 -B integer_ram_unfolding_audit.py [seed]
"""
import random
import sys
from math import gcd

sys.dont_write_bytecode = True
from integer_ram_step_model import ADDITIVE, COMPARE, RAM

ALLOWED = ADDITIVE | {'load', 'store'}


def literal_pool(rng, n, w, b):
    small = list(range(0, n + 3)) + [1 << k for k in range(1, b + 2)]
    if w is None:
        return small + [-1, -2, -(1 << b), 3 * (1 << b)]
    m, top = (1 << w), 1 << (w - 1)
    edge = [m - 1, m - 2, m - (1 << b), m - (1 << (b + 1)), top, top - 1, top + 1,
            top - (1 << b), top + (1 << b), rng.randrange(m), rng.randrange(m)]
    return small + edge


def rand_prog(rng, n, length, w, b, doubling=0.15):
    pool = literal_pool(rng, n, w, b)

    def operand(lit=0.3):
        return ('i', rng.choice(pool)) if rng.random() < lit else ('r', rng.randrange(64))

    prog = [('load', ('i', rng.randrange(n)))]
    while len(prog) < length:
        r = rng.random()
        if r < 0.22:
            prog.append(('load', operand(0.35)))
        elif r < 0.22 + doubling:
            prog.append(('dbl', operand(0.0)))
        elif r < 0.60:
            prog.append((rng.choice(('add', 'sub')), operand(0.2), operand(0.4)))
        elif r < 0.72:
            prog.append(('cmp', rng.choice(COMPARE), operand(0.1), operand(0.5)))
        elif r < 0.88:
            prog.append(('br', rng.choice(COMPARE), operand(0.1), operand(0.5), rng.randrange(1, 4)))
        else:
            prog.append(('store', operand(0.5), operand(0.3)))
    return prog


def run(prog, x, w):
    ram = RAM(x, w=w, allowed=ALLOWED, trace=True)
    regs = []

    def val(o):
        if o[0] == 'i':
            return o[1]
        return regs[o[1] % len(regs)] if regs else 0

    pc = 0
    while pc < len(prog):
        ins = prog[pc]
        pc += 1
        if ins[0] == 'load':
            regs.append(ram.load(val(ins[1])))
        elif ins[0] == 'dbl':
            regs.append(ram.op('add', val(ins[1]), val(ins[1])))
        elif ins[0] in ('add', 'sub'):
            regs.append(ram.op(ins[0], val(ins[1]), val(ins[2])))
        elif ins[0] == 'cmp':
            regs.append(ram.cmp(ins[1], val(ins[2]), val(ins[3])))
        elif ins[0] == 'br':
            if ram.br(ins[1], val(ins[2]), val(ins[3])):
                pc += ins[4]
        else:
            ram.store(val(ins[1]), val(ins[2]))
    return ram


def segment(rng, n, b):
    box = 1 << b
    while True:
        p = [rng.randrange(box) for _ in range(n)]
        v = [rng.choice((-2, -1, 0, 0, 1, 1, 2)) for _ in range(n)]
        g0 = 0
        for c in v:
            g0 = gcd(g0, abs(c))
        if g0 != 1:
            continue
        g = min(((box - 1 - pi) // vi if vi > 0 else pi // -vi) for pi, vi in zip(p, v) if vi)
        if g >= 2:
            return p, v, rng.randrange(2, g + 1)


def audit(rng, n, b, w, length, trials):
    stat = dict(pairs=0, same=0, points=0, differ_forbidden=0, violations=0,
                alias_hits=0, wraps=0, max_forbid=0, bound_ok=True, first_violation=None)
    for _ in range(trials):
        prog = rand_prog(rng, n, length, w, b)
        p, v, g = segment(rng, n, b)
        q = [pi + g * vi for pi, vi in zip(p, v)]
        rp, rq = run(prog, p, w), run(prog, q, w)
        stat['pairs'] += 1
        if rp.history() != rq.history():
            continue
        stat['same'] += 1
        stat['alias_hits'] += rp.alias_hits
        stat['wraps'] += rp.wraps
        pairs = set(rp.forbid)
        t = rp.steps
        stat['max_forbid'] = max(stat['max_forbid'], len(pairs))
        stat['bound_ok'] &= len(pairs) <= t * (t - 1) // 2 + n * t
        for j in range(1, g):
            y = [pi + j * vi for pi, vi in zip(p, v)]
            stat['points'] += 1
            if run(prog, y, w).history() == rp.history():
                continue
            if any(rp.coincide(pr, y) for pr in pairs):
                stat['differ_forbidden'] += 1
            else:
                stat['violations'] += 1
                if stat['first_violation'] is None:
                    stat['first_violation'] = (prog, p, q, y)
    return stat


def show(tag, s):
    print(f"{tag}: pairs={s['pairs']} same_history={s['same']} lattice_points={s['points']} "
          f"changed_on_forbidden={s['differ_forbidden']} alias_hits={s['alias_hits']} "
          f"wrapped_operands={s['wraps']} max_forbidden_pairs={s['max_forbid']} "
          f"count_bound_ok={s['bound_ok']} VIOLATIONS={s['violations']}")


def wrap_numbers(w, b, doublings, signed):
    """Distinct wrap numbers of 2**d * x (shifted by 2**(w-1) if signed) over x in [0, 2**b)."""
    shift = (1 << (w - 1)) if signed else 0
    return len({(shift + (x << doublings)) >> w for x in range(1 << b)})


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    rng = random.Random(seed)
    print('seed', seed)
    print('--- (Z) integer model ---')
    for n, b, length, trials in ((2, 5, 10, 6000), (3, 5, 14, 6000), (4, 4, 18, 4000)):
        s = audit(rng, n, b, None, length, trials)
        show(f'Z n={n} b={b} T={length}', s)
        assert s['violations'] == 0 and s['bound_ok']
    print('--- (N) native model inside the window T + b + 2 <= w ---')
    for n, b, w in ((2, 4, 16), (3, 4, 16), (3, 5, 20), (4, 3, 24)):
        length = w - b - 2
        s = audit(rng, n, b, w, length, 6000)
        show(f'N n={n} b={b} w={w} T={length}', s)
        assert s['violations'] == 0 and s['bound_ok']
    print('--- (N) native model outside the window: random search for failures of Lemma S ---')
    n, b, w = 2, 4, 12
    for length in range(w - b - 1, w + 5):
        s = audit(rng, n, b, w, length, 12000)
        print(f'N n={n} b={b} w={w} T={length} (T+b+2-w={length + b + 2 - w:+d}): '
              f"same_history={s['same']} VIOLATIONS={s['violations']}")
    print('--- explicit failures of Lemma S outside the window: n=1, b=4, w=12 ---')
    w, b = 12, 4

    def short(x):                      # load x; w-b+1 doublings; load at address 2^(w-b+1) x
        ram = RAM([x], w=w, allowed=ALLOWED, trace=True)
        r = ram.load(0)
        for _ in range(w - b + 1):
            r = ram.op('add', r, r)
        ram.load(r)
        return ram

    def longer(x):                     # the referee's program: ... add 100; store at 100; load at 100 + 512 x
        ram = RAM([x], w=w, allowed=ALLOWED, trace=True)
        r = ram.load(0)
        for _ in range(9):
            r = ram.op('add', r, r)
        addr = ram.op('add', r, 100)
        ram.store(100, 7)
        ram.load(addr)
        return ram

    for name, prog in (('load; 9 doublings; load', short), ('load; 9 doublings; add 100; store 100; load', longer)):
        r0, r8 = prog(0), prog(8)
        pairs = set(r0.forbid)
        inside = [(prog(y).history() == r0.history(), any(r0.coincide(pr, [y]) for pr in pairs)) for y in range(1, 8)]
        print(f'{name}: T={r0.steps} (T+b+2-w={r0.steps + b + 2 - w:+d}); history(0)==history(8): '
              f'{r0.history() == r8.history()}; x=1..7 with the same history: {sum(a for a, _ in inside)}; '
              f'on a recorded forbidden pair: {sum(c for _, c in inside)}')
        assert r0.history() == r8.history() and not any(a or c for a, c in inside)
    print('--- wrap numbers of the doubling form 2^d x on the box (w=16, b=4) ---')
    w, b = 16, 4
    for d in range(w - b - 3, w - b + 4):
        t = d + 2                      # load, d doublings, one comparison
        print(f'd={d} T={t} (T+b+2-w={t + b + 2 - w:+d}): unsigned wrap numbers='
              f'{wrap_numbers(w, b, d, False)} signed={wrap_numbers(w, b, d, True)}')
    print('--- explicit non-convex class: load, w-b+1 doublings, slt(.,0) at w=16, b=4 ---')

    def out(x):
        ram = RAM([x], w=w, allowed=ALLOWED, trace=False)
        r = ram.load(0)
        for _ in range(w - b + 1):
            r = ram.op('add', r, r)
        return int(ram.br('slt', r, 0)), ram.steps

    table = [out(x) for x in range(1 << b)]
    print('steps', table[0][1], '= w-b+3 =', w - b + 3)
    print('branch outcome for x=0..15:', ''.join(str(o) for o, _ in table))
    assert ''.join(str(o) for o, _ in table) == '0000111100001111'
    print('all assertions passed')


if __name__ == '__main__':
    main()
