"""Check exact canonical lengths, consecutive centers, and large aligned edits."""

from itertools import product

import pycosat


def key(row):
    return tuple((abs(x), x < 0) for x in row)


def clause(*literals):
    return tuple(sorted(literals, key=lambda x: (abs(x), x < 0)))


def encode(core):
    v = max(abs(x) for row in core for x in row)
    lines = ['%d %d %d 0' % row for row in sorted(core, key=key)]
    return (f'p cnf {v} {len(core)}\n' + '\n'.join(lines)).encode()


def parse(raw):
    head, *lines = raw.decode().splitlines()
    _, _, bound, count = head.split()
    rows = []
    for line in lines:
        a, b, c, end = map(int, line.split())
        assert end == 0 and len({abs(a), abs(b), abs(c)}) == 3
        row = (a, b, c)
        assert row == clause(*row)
        rows.append(row)
    assert len(rows) == int(count) == len(set(rows)) and rows == sorted(rows, key=key)
    assert {abs(x) for row in rows for x in row} == set(range(1, int(bound)+1))
    assert encode(set(rows)) == raw
    return set(rows)


def adjustable(guard, lengths, gain):
    """Use signs and varying decimal lengths on the two non-guard literals."""
    low, high = lengths
    extra_a = min(high-low, gain)
    extra_b = min(high-low, gain-extra_a)
    signs = gain-extra_a-extra_b
    assert 0 <= signs <= 2
    a = 2 * 10**(low + extra_a-1)
    b = 3 * 10**(low + extra_b-1)
    return clause(-a if signs else a, -b if signs == 2 else b, guard)


def general_padding():
    total = 0
    # Seven clauses leave one assignment; all eight leave none.
    for number in (7, 8):
        core = set(list(product((1,-1), (2,-2), (3,-3)))[:number])
        base_size = len(encode(core))
        outcome = pycosat.solve(list(core)) != 'UNSAT'
        v, c = 3, len(core)
        for t in range(12, 30):
            def minimum(j):
                return (base_size + len(str(v+j))-len(str(v)) + len(str(c+j))-len(str(c))
                        + sum(len(str(v+i))+7 for i in range(1,j+1)))
            for target in range(minimum(t), minimum(t+1)):
                slack = target - minimum(t)
                rows = core.copy()
                for i in range(1, t+1):
                    g = v+i
                    high = max(1, len(str(g))-1)
                    take = min(2*high, slack) if t-i < 12 else 0
                    rows.add(adjustable(g, (1, high), take))
                    slack -= take
                assert slack == 0
                data = encode(rows)
                assert len(data) == target and parse(data) == rows
                assert (pycosat.solve(list(rows)) != 'UNSAT') == outcome
                total += 1
    return total


def base_pins(i):
    literal = i if 3 <= i <= 14 or set(str(i)) == {'5'} else -i
    return [clause(a,b,literal) for a,b in product((1,-1),(2,-2))]


def small_events():
    for i in range(65, 602):
        yield from base_pins(i)
        if i == 599:
            for j in range(200, 300):
                yield clause(j, j+1, 555)


def buffers(v, gain):
    high = max(2, len(str(v))-1)
    rows = set()
    for g in range(3,15):
        take = min(gain, 2*(high-2)+2)
        rows.add(adjustable(g, (2, high), take))
        gain -= take
    assert gain == 0 and len(rows) == 12
    return rows


def small_successors():
    core = {row for i in range(3,65) for row in base_pins(i)}
    checks = edit_count = 0
    for j, row in enumerate(small_events()):
        v = max(abs(x) for c in core for x in c)
        v_next = max(v, *(abs(x) for x in row))
        nxt = core | {row}
        if j in {0,1,2,3,4,136,137,139,140,2139,2140,2141,2238,2239,2240}:
            start = core | buffers(v,0)
            end = nxt | buffers(v_next,0)
            start_size = len(encode(start))
            gap = len(encode(end))-start_size
            prev = start
            for u in range(1,gap+1):
                state = end if u == gap else core | buffers(v,u)
                raw = encode(state)
                assert len(raw) == start_size+u and parse(raw) == state
                assert len(prev-state) <= 12 and len(state-prev) <= 13
                assert pycosat.solve(list(state)) != 'UNSAT'
                prev = state
                checks += 1
            if clause(200,201,555) in core:
                for other in (535,545,565,575):
                    variant = core - {clause(200,201,555)} | {clause(200,201,other)} | buffers(v,0)
                    assert len(encode(variant)) == start_size
                    assert pycosat.solve(list(variant)) == 'UNSAT'
                    edit_count += 1
        core = nxt
    return checks, edit_count


def digit_total(end):
    start = width = 1
    total = 0
    while start <= end:
        stop = min(end, 10*start-1)
        total += (stop-start+1)*width
        start, width = 10*start, width+1
    return total


def virtual_layout(v, completed, extra_rows=0):
    positives = 12 + sum(int('5'*i) <= v for i in range(2,len(str(v))+1))
    pins = 4*(digit_total(v)-2 + 7*(v-2)) + 4*(v-2) + 4*(v-2-positives)
    flex = sum(len(str(g))+9 for g in range(3,15))
    count = (4*(v-2)+12+extra_rows+sum(10**(s-1) for s in range(3,completed+1)))
    body = pins + flex + sum(10**(s-1)*(3*s+5) for s in range(3,completed))
    header = len(f'p cnf {v} {count}\n')
    start = header + body
    size = start + 10**(completed-1)*(3*completed+5) + extra_rows*(3*(completed+1)+5)-1
    return start, size


def large_alignments():
    small = {r for i in range(3,600) for r in base_pins(i)} | buffers(599,0)
    small.update(clause(i,i+1,555) for i in range(200,300))
    raw = encode(small)
    start, nbytes = virtual_layout(599,3)
    assert nbytes == len(raw) and raw[start:].startswith(b'200 201 555 0')
    checked = 0
    for q in range(96, 241, 8):
        m = 10**(q-1)
        for v, pending in ((6*m-1,0), (60*m-1,10*m-1)):
            start, size = virtual_layout(v,q,pending)
            n = 8*size
            w = 16*(((n+1).bit_length()+15)//16)
            width_bytes = w//8
            odd = w//(w & -w)
            rep = 0
            for ell in range(1,odd+1):
                rep = 256*rep+1
                if rep % odd == 0:
                    break
            delta = rep << (8*(width_bytes-ell))
            assert delta % w == 0 and delta**2 % (1 << w) == 0
            for j in (0,1,m//2,m-1):
                pos = start+j*(3*q+5)+2*q+2
                left = ((pos+1+width_bytes-1)//width_bytes)*width_bytes-pos
                assert 0 < left and left+width_bytes <= q
                for digit in '34567':
                    changed = bytearray(b'5'*q)
                    end = left+width_bytes
                    changed[end-ell:end] = digit.encode()*ell
                    val = int(changed)
                    assert 5*m <= val <= 6*m-1 and (val == int('5'*q)) == (digit=='5')
                    checked += 1
    return checked


if __name__ == '__main__':
    print(f'{general_padding()} exact-length canonical SAT/UNSAT paddings')
    steps, edits = small_successors()
    print(f'{steps} consecutive byte steps and {edits} UNSAT identifier edits')
    print(f'{large_alignments()} large-order packed edit positions/settings')
