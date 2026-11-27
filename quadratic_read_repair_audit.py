"""Exact finite experiments for the quadratic last-write compiler. No external jobs."""
from collections import Counter
from ctypes.util import find_library
from itertools import combinations, product
from random import Random

from nine_step_native_referee_audit import upper_and_truth
from adaptive_sparse_presentation_audit import solver


class Circuit:
    """Signed wire literals. Variable 1 is an anchored false bit."""
    def __init__(self, inputs):
        self.inputs = inputs
        self.gates = []
        self.cache = {}

    def gate(self, op, a, b):
        if op == 'xor':
            if a == b:
                return 1
            if a == -b:
                return -1
            if abs(a) == 1:
                return b if a == 1 else -b
            if abs(b) == 1:
                return a if b == 1 else -a
        if op == 'and':
            if a == 1 or b == 1 or a == -b:
                return 1
            if a == -1 or a == b:
                return b
            if b == -1:
                return a
        key = (op, min(a, b), max(a, b))
        if key not in self.cache:
            self.gates.append(key)
            self.cache[key] = 3 + self.inputs + len(self.gates)
        return self.cache[key]

    def all(self, literals):
        result = -1
        for lit in literals:
            result = self.gate('and', result, lit)
        return result

    def xor(self, literals):
        result = 1
        for lit in literals:
            result = self.gate('xor', result, lit)
        return result

    def any(self, literals):
        return -self.all(-x for x in literals)

    def packed(self, output, columns, lanes):
        mask = (1 << lanes) - 1
        values = [0, 0, 0, 0] + columns
        def read(lit):
            return values[abs(lit)] ^ (mask if lit < 0 else 0)
        for op, a, b in self.gates:
            values.append((read(a) ^ read(b)) if op == 'xor' else (read(a) & read(b)))
        return read(output)

    def dimacs(self, output):
        # The explicit copy makes the final pin distinct from all anchors.
        gates = self.gates + [('xor', output, 1)]
        pins = (1, 2, 3)
        v = 3 + self.inputs + len(gates)
        rows = []
        def forbidden(ids, bits):
            return tuple(-var if bits >> j & 1 else var for j, var in enumerate(ids))
        for bits in range(1, 8):
            rows.append(forbidden(pins, bits))
        for dst, (op, a, b) in enumerate(gates, 4 + self.inputs):
            ids = list(dict.fromkeys((dst, abs(a), abs(b))))
            ids += [p for p in pins if p not in ids][:3 - len(ids)]
            for bits in range(8):
                def get(lit):
                    return ((bits >> ids.index(abs(lit))) & 1) ^ (lit < 0)
                result = (get(a) ^ get(b)) if op == 'xor' else (get(a) & get(b))
                rows.append(forbidden(ids, bits) if result != get(dst) else (-1, 2, 3))
        rows.append((v, 1, 2))
        count = 8 * len(gates) + 8
        assert len(rows) == count
        digits = len(str(v))
        raw = (f'p cnf {v} {count}\n' + ''.join(
            ''.join(f'{lit:>{digits+1}} ' for lit in row) + '0\n' for row in rows
        )).encode('ascii')
        assert len(raw) == 8 + digits + len(str(count)) + count * (3 * digits + 8)
        return raw


def multiply(a, b):
    """ANF product; a monomial is its mask of variables, including mask 0 for 1."""
    result = set()
    for x in a:
        for y in b:
            result ^= {x | y}
    return result


def substitute(poly, replacements):
    result = set()
    for term in poly:
        expansion = {0}
        while term:
            bit = term & -term
            expansion = multiply(expansion, replacements.get(bit, {bit}))
            term ^= bit
        result ^= expansion
    return result


def reduce_rows(equations, eligible):
    basis = {}
    remainder = []
    for equation in equations:
        row = set(equation)
        while True:
            top = max((m for m in row if eligible(m)), default=None)
            if top is None:
                remainder.append(row)
                break
            if top not in basis:
                basis[top] = row
                break
            row ^= basis[top]
    return basis, remainder


def param_gate(circ, poly, n, parameters):
    terms = []
    for monomial in sorted(poly):
        assert not monomial & ((1 << n) - 1)
        terms.append(circ.all(w for j, w in enumerate(parameters) if monomial >> (n+j) & 1))
    return circ.xor(terms)


def signed_gap(circ, phase, free, n, parameters):
    """Produce active, negative, exponent for the exact signed character sum."""
    free = set(free)
    phase = set(phase)
    pairs = 0
    while True:
        pair = next((a | b for a, b in combinations(sorted(free), 2) if a | b in phase), None)
        if pair is None:
            break
        a = pair & -pair
        b = pair ^ a
        phase.remove(pair)
        left = {m ^ a for m in phase if m & a}
        right = {m ^ b for m in phase if m & b}
        phase = {m for m in phase if not m & pair} ^ multiply(left, right)
        free -= {a, b}
        pairs += 1
    checks = []
    for a in sorted(free):
        checks.append(-param_gate(circ, {m ^ a for m in phase if m & a}, n, parameters))
    free_mask = sum(free)
    sign = param_gate(circ, {m for m in phase if not m & free_mask}, n, parameters)
    return circ.all(checks), sign, pairs + len(free)


def fiber_gate(circ, n, equations, parameters):
    """An ordinary circuit on the parameters tests existence of an n-bit solution."""
    time_mask = (1 << n) - 1
    quadratics, linear = reduce_rows(equations, lambda m: (m & time_mask).bit_count() == 2)
    pivots, constraints = reduce_rows(linear, lambda m: bool(m & time_mask))
    replacements = {}
    for bit, row in sorted(pivots.items()):
        assert bit.bit_count() == 1
        replacements[bit] = substitute(row - {bit}, replacements)
    basis = [substitute(row, replacements) for row in quadratics.values()]
    free = {1 << j for j in range(n)} - pivots.keys()
    valid = circ.all(-param_gate(circ, p, n, parameters) for p in constraints)
    # Sum the unnormalized signed terms modulo a power of two strictly above the bound.
    total = [1] * (n + len(basis) + 1)
    for mask in range(1 << len(basis)):
        phase = set()
        for j, row in enumerate(basis):
            if mask >> j & 1:
                phase ^= row
        active, negative, e = signed_gap(circ, phase, free, n, parameters)
        high = circ.gate('and', active, negative)
        carry = 1
        for j in range(e, len(total)):
            addend = active if j == e else high
            pair = circ.gate('xor', total[j], addend)
            new_carry = circ.any([circ.gate('and', total[j], addend), circ.gate('and', carry, pair)])
            total[j] = circ.gate('xor', pair, carry)
            carry = new_carry
    return circ.all([valid, circ.any(total)]), len(basis)


def interval_gate(circ, n, coords, domain, addr, lower, upper):
    """Strict symbolic endpoints. None denotes the missing bound. Domain rows equal zero."""
    pars = list(addr)
    common = [row ^ {1 << (n+j)} for j, row in enumerate(coords)] + list(domain)
    def choices(bits, lower_side):
        if bits is None:
            return [(-1, [])]
        start = len(pars)
        pars.extend(bits)
        alternatives = []
        for j in range(n):
            # First difference at j in most-significant-first order.
            guard = -bits[j] if lower_side else bits[j]
            rows = [{1 << k, 1 << (n+start+k)} for k in range(j+1, n)]
            rows.append(({0, 1 << j} if lower_side else {1 << j}))
            alternatives.append((guard, rows))
        return alternatives
    lows = choices(lower, True)
    highs = choices(upper, False)
    tests = []
    for gl, lr in lows:
        for gh, hr in highs:
            hit, _ = fiber_gate(circ, n, common + lr + hr, pars)
            tests.append(circ.all([gl, gh, hit]))
    return circ.any(tests)


def evaluate(poly, x):
    return sum((m & x) == m for m in poly) % 2


def columns(inputs):
    return [sum(1 << x for x in range(1 << inputs) if x >> i & 1) for i in range(inputs)]


def random_poly(rng, n, affine=False):
    terms = [0] + [1 << j for j in range(n)]
    if not affine:
        terms.extend((1 << a) | (1 << b) for a, b in combinations(range(n), 2))
    return {term for term in terms if rng.randrange(2)}


def check_fibers():
    rng = Random(7007)
    tests = ranks = 0
    maps = [(2, [set(i for i in range(4) if a >> i & 1),
                 set(i for i in range(4) if b >> i & 1)], [])
            for a in range(16) for b in range(16)]
    for _ in range(100):
        n = rng.randrange(1, 6)
        w = rng.randrange(1, 6)
        maps.append((n, [random_poly(rng, n) for _ in range(w)],
                     [random_poly(rng, n, True) for _ in range(rng.randrange(3))]))
    for n, coords, domain in maps:
        w = len(coords)
        circ = Circuit(w + 2*n)
        addr = list(range(4, 4+w))
        lower = list(range(4+w, 4+w+n))
        upper = list(range(4+w+n, 4+w+2*n))
        rows = [(z, sum(evaluate(c, z) << j for j, c in enumerate(coords)))
                for z in range(1 << n) if not any(evaluate(d, z) for d in domain)]
        cols = columns(circ.inputs)
        lanes = 1 << circ.inputs
        for l, h in [(None, None), (None, upper), (lower, None), (lower, upper)]:
            out = interval_gate(circ, n, coords, domain, addr, l, h)
            actual = circ.packed(out, cols, lanes)
            # Group by interval; for each attainable address set its lane.
            expected = 0
            for a, b in product(range(1 << n), repeat=2):
                mask = 0
                for z, value in rows:
                    if (l is None or a < z) and (h is None or z < b):
                        mask |= 1 << value
                expected |= mask << ((a << w) + (b << (w+n)))
            assert actual == expected
            tests += lanes
        ranks += 1
    print('Interval circuits:', ranks, 'maps;', tests, 'address/endpoint/bound-type tests')


def check_repairs():
    """Three possible stores, then one read. Exercise authentic and forged repairs."""
    solve = solver()
    rng = Random(173)
    cases = missed_by_trusting = omits_last = physical = 0
    truthful = set()
    for mask in range(8):
        # This is the ANF of the characteristic function of the proposed repair set.
        table = [int(t < 3 and mask >> t & 1) for t in range(4)]
        for bit in (1, 2):
            for t in range(4):
                if t & bit:
                    table[t] ^= table[t ^ bit]
        poly = {t for t in range(4) if table[t]}
        circ = Circuit(11)
        q, b = 4, 5
        same, correct = [], []
        for t in range(3):
            en, a, v = range(6 + 3*t, 9 + 3*t)
            same.append(circ.all([en, -circ.xor([q, a])]))
            correct.append(circ.all([same[-1], -circ.xor([b, v])]))
        unsound = circ.any(-correct[t] for t in range(3) if mask >> t & 1)
        obstacles = [(-1, b)] + [(t, circ.all([same[t], -correct[t]])) for t in range(3)]
        uncovered = []
        for t, obstacle in obstacles:
            bits = lambda v: [-1 if v >> j & 1 else 1 for j in range(2)]
            hit = interval_gate(circ, 2, [poly], [], [-1], None if t < 0 else bits(t), bits(3))
            uncovered.append(circ.all([obstacle, -hit]))
        incomplete = circ.any(uncovered)
        defect = circ.any([unsound, incomplete])
        lanes = 1 << 11
        result = circ.packed(defect, columns(11), lanes)
        no_authentication = circ.packed(incomplete, columns(11), lanes)
        for x in range(lanes):
            qv, claim = x & 1, (x >> 1) & 1
            prior = []
            for t in range(3):
                enabled, addr, value = [(x >> (2+3*t+k)) & 1 for k in range(3)]
                if enabled and addr == qv:
                    prior.append((t, value))
            original = prior[-1][1] if prior else 0
            if not (no_authentication >> x & 1) and original != claim:
                missed_by_trusting += 1
            certified = not (result >> x & 1)
            conflict = [t for t, v in [(-1, 0)] + prior if v != claim]
            real_repairs = {t for t, v in prior if v == claim}
            offered = {t for t in range(3) if mask >> t & 1}
            assert certified == (offered <= real_repairs and
                                 all(any(t > j for t in offered) for j in conflict))
            if certified:
                assert claim == original
                truthful.add(x)
                if conflict and prior and prior[-1][0] not in offered:
                    omits_last += 1
            cases += 1
        for x in rng.sample(range(lanes), 6):
            signature = [4+i if x >> i & 1 else -(4+i) for i in range(11)]
            raw = circ.dimacs(circ.all([defect] + signature))
            v, clauses = parsed(raw)
            assert solve(clauses, v) == bool(result >> x & 1)
            physical += 1
    assert len(truthful) == 1 << 10 and missed_by_trusting and omits_last
    print('Repair diagram tests:', cases, 'passing without last writer despite conflict:', omits_last,
          'false replies admitted without authenticating repairs:', missed_by_trusting,
          'serialized defect tests:', physical)


def field_mul(a, b, f):
    result = 0
    order = 1 << (f.bit_length()-1)
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a & order:
            a ^= f
        b >>= 1
    return result


def power(a, e, f):
    res = 1
    while e:
        if e & 1:
            res = field_mul(res, a, f)
        a = field_mul(a, a, f)
        e >>= 1
    return res


def binary_rank(words):
    basis = {}
    for word in words:
        while word:
            lead = word.bit_length()
            if lead not in basis:
                basis[lead] = word
                break
            word ^= basis[lead]
    return len(basis)


def spaces(n):
    level = {frozenset([0]): ()}
    while level:
        yield from level.items()
        nxt = {}
        for space, basis in level.items():
            for x in range(1 << n):
                if x not in space:
                    bigger = space | {x ^ y for y in space}
                    nxt.setdefault(bigger, basis + (x,))
        level = nxt


def check_flats():
    checked = Counter()
    for n, f in [(3, 0b1011), (5, 0b100101)]:
        cube = [power(x, 3, f) for x in range(1 << n)]
        assert len(set(cube)) == len(cube)
        for space, basis in spaces(n):
            reps = set(range(1 << n))
            while reps:
                a = min(reps)
                reps -= {a ^ x for x in space}
                rank = binary_rank(cube[a] ^ cube[a ^ u] ^ cube[a ^ v] ^ cube[a ^ u ^ v]
                                   for u, v in combinations(basis, 2))
                assert 2 * (1 << rank) >= len(space)
                if len(space) == 2:
                    assert rank == 0
                checked[n] += 1
    print('All affine flats, by dimension of ambient field:', dict(checked))


def sweep_program():
    """Register-only ALU, explicit input/work loads and stores, fixed-label comparison."""
    code = []
    def emit(*ins):
        code.append(ins)
    def copy(dst, src):
        emit('add', dst, src, 0)
    for name in ['d', 'end', 'q', 'modulus']:
        emit('input', name, 'head')
        emit('add', 'head', 'head', 1)
    emit('shl', 'mask', 1, 'd')
    emit('sub', 'mask', 'mask', 1)
    emit('add', 'double', 'd', 'd')
    emit('shl', 'span', 1, 'double')
    start = len(code)
    def mul(dst, left, right):
        copy('acc', 0)
        copy('left', left)
        copy('base', 'head')
        for _ in range(8):
            emit('and', 'a', 'left', 'mask')
            emit('shl', 'a', 'a', 'd')
            copy('right', right)
            for _ in range(8):
                emit('and', 'key', 'right', 'mask')
                emit('or', 'key', 'key', 'a')
                emit('add', 'key', 'key', 'base')
                emit('input', 'entry', 'key')
                emit('xor', 'acc', 'acc', 'entry')
                emit('add', 'base', 'base', 'span')
                emit('shr', 'right', 'right', 'd')
            emit('shr', 'left', 'left', 'd')
        copy(dst, 'acc')
    mul('sq', 'z', 'z')
    mul('cube', 'sq', 'z')
    store_time = len(code)
    emit('store', 'cube', 'z')
    emit('add', 'z', 'z', 1)
    period = 1 << max(store_time.bit_length(), (len(code)-start).bit_length())
    while len(code) < start + period - 1:
        copy('unused', 0)
    emit('blt', 'z', 'end', start)
    emit('load', 'answer', 'q')
    emit('and', 'answer', 'answer', 1)
    emit('return_nonzero', 'answer')  # one comparison to fixed terminal labels
    return code, start, store_time, period


def make_input(n, f):
    d = (n+7)//8
    file = [d, 1 << n, 0, f]
    def rem(a):
        while a.bit_length() > n:
            a ^= f << (a.bit_length()-n-1)
        return a
    for i, j, a, b in product(range(8), range(8), range(1 << d), range(1 << d)):
        file.append(field_mul(rem(a << (i*d)), rem(b << (j*d)), f))
    return file


def payload_shape(n, words):
    # A power-of-two physical payload, enlarged only for small test dimensions.
    h = max(1, (3*n+9)//10)
    while 12*(h+1)*words > 1 << h:
        h += 1
    return 1 << h, 12*(h+1)


def pack_input(file, width, length):
    assert all(0 <= x < 1 << width for x in file)
    packed = sum(x << (i*width) for i, x in enumerate(file))
    return packed.to_bytes(length//8, 'little')


def execute(program, file):
    code, start, first, period = program
    n = file[1].bit_length()-1
    length, width = payload_shape(n, len(file))
    word_mask = (1 << width)-1
    payload = int.from_bytes(pack_input(file, width, length), 'little')
    words = [(payload >> (i*width)) & word_mask for i in range(len(file))]
    assert words == file
    reg, work, trace = {}, {}, []
    pc = count = 0
    def get(x):
        return x if isinstance(x, int) else reg.get(x, 0)
    while True:
        ins = code[pc]
        op = ins[0]
        count += 1
        pc += 1
        if op == 'return_nonzero':
            assert count == start + period * file[1] + 3
            return bool(get(ins[1])), trace, count
        if op == 'blt':
            if get(ins[1]) < get(ins[2]):
                pc = ins[3]
        elif op == 'store':
            a, v = map(get, ins[1:])
            assert count-1 == first + period * v
            work[a] = v
            trace.append((a, v))
        elif op in ('input', 'load'):
            a = get(ins[2])
            reg[ins[1]] = words[a] if op == 'input' else work.get(a, 0)
        else:
            a, b = get(ins[2]), get(ins[3])
            if op == 'add': result = a+b
            elif op == 'sub': result = a-b
            elif op == 'shl': result = a<<b
            elif op == 'shr': result = a>>b
            elif op == 'and': result = a&b
            elif op == 'or': result = a|b
            elif op == 'xor': result = a^b
            else: raise ValueError(op)
            assert 0 <= result <= word_mask
            reg[ins[1]] = result & word_mask


def cube_file(n, f, q):
    circ = Circuit(n)
    z = list(range(4, 4+n))
    def mul(left, right):
        coeff = [1]*(2*n-1)
        for i, a in enumerate(left):
            for j, b in enumerate(right):
                coeff[i+j] = circ.xor([coeff[i+j], circ.all([a,b])])
        for k in reversed(range(n, len(coeff))):
            for j in range(n):
                if f >> j & 1:
                    coeff[k-n+j] = circ.xor([coeff[k-n+j], coeff[k]])
        return coeff[:n]
    cube = mul(mul(z,z),z)
    return circ.dimacs(circ.all([z[0]] + [x if q >> j & 1 else -x for j,x in enumerate(cube)]))


def guarded_file(core, supplied, f):
    """On the advertised sweep layout, the final rows authenticate each actual table word."""
    d, end, q, declared = supplied[:4]
    n = f.bit_length()-1
    assert d == (n+7)//8 and end == 1 << n and q < end and declared == f
    old_header, body = core.split(b'\n', 1)
    v, old_count = map(int, old_header.split()[2:])
    entries = 64 << (2*d)
    digits = len(str(v))
    row_size = 3*digits + 8
    count = old_count + entries
    header = f'p cnf {v} {count}\n'.encode()
    def guard(k):
        pair, low = divmod(k, 1 << (2*d))
        i, j = divmod(pair, 8)
        a, b = divmod(low, 1 << d)
        # field_mul expects its first operand reduced. Compute the shifted product
        # by a separate multiply-and-shift route from construction of make_input.
        expected = field_mul(field_mul(a, b, f), power(2, d*(i+j), f), f)
        lit = -1 if supplied[4+k] == expected else 1
        return (''.join(f'{x:>{digits+1}} ' for x in [lit, 2, 3]) + '0\n').encode()
    raw = header + body + b''.join(guard(k) for k in range(entries))
    assert len(raw) == 8 + digits + len(str(count)) + count*row_size
    def local_byte(pos):
        if pos < len(header):
            return header[pos]
        pos -= len(header)
        if pos < len(body):
            return body[pos]
        k, col = divmod(pos-len(body), row_size)
        return guard(k)[col]
    return raw, local_byte


def check_table_guards():
    program = sweep_program()
    solve = solver()
    f, n = 0b1011, 3
    file = make_input(n, f)
    # Find a genuine false positive for the unguarded inverse on a one-bit edit.
    # Use direct lookup of the same two multilinear products to shortlist edits.
    def indexed_product(x, y):
        v = 0
        for i in range(8):
            for j in range(8):
                low = 2*((x >> i) & 1) + ((y >> j) & 1)
                v ^= file[4+4*(8*i+j)+low]
        return v
    found = None
    for offset in range(4, len(file)):
        file[offset] ^= 1
        memory = {}
        for x in range(1 << n):
            memory[indexed_product(indexed_product(x,x),x)] = x
        candidates = [q for q in range(1 << n) if power(q,5,f) & 1 and not memory.get(q,0) & 1]
        file[offset] ^= 1
        if candidates:
            found = (offset, candidates[0])
            break
    assert found
    offset, q = found
    file[2] = q
    omitted = cube_file(n, f, q)
    v, clauses = parsed(omitted)
    assert solve(clauses, v)
    checks = 0
    for changed in [False, True]:
        if changed:
            file[offset] ^= 1
        actual, _, _ = execute(program, file)
        assert actual != changed
        raw, indexer = guarded_file(omitted, file, f)
        assert raw == bytes(indexer(j) for j in range(len(raw)))
        v, clauses = parsed(raw)
        assert solve(clauses, v) == actual
        checks += len(raw)
    print('Guarded cube file bits:', 8*len(raw), 'local bytes checked:', checks,
          'one corrupt low bit at payload word', offset, 'query', q)


def parsed(raw):
    header, *body = raw.decode('ascii').splitlines()
    kind, fmt, v, m = header.split()
    assert (kind, fmt) == ('p','cnf') and int(m) == len(body)
    clauses = []
    for line in body:
        a,b,c,end = map(int, line.split())
        assert end == 0 and len({abs(a),abs(b),abs(c)}) == 3
        assert 1 <= min(map(abs,(a,b,c))) and max(map(abs,(a,b,c))) <= int(v)
        clauses.append((a,b,c))
    return int(v), clauses


def check_sweeps():
    solve = solver()
    program = sweep_program()
    print('Native sweep setup, first store (zero-based), instruction period:', program[1:])
    for n, f in [(3, 0b1011), (5, 0b100101), (9, 0b1000010001)]:
        file = make_input(n, f)
        sizes = []
        for q in (range(1 << n) if n <= 5 else [0, 1, 299]):
            file[2] = q
            answer, writes, clock = execute(program, file)
            expected = [power(x, 3, f) for x in range(1 << n)]
            assert writes == list(zip(expected, range(1 << n)))
            inverse = power(q, ((2 << n)-1)//3, f)
            assert answer == bool(inverse & 1) and expected[inverse] == q
            raw = cube_file(n, f, q)
            v, clauses = parsed(raw)
            assert solve(clauses, v) == answer
            sizes.append(8*len(raw))
        print('Cube degree', n, 'queries', len(sizes), 'clock', clock, 'DIMACS bit range', min(sizes), max(sizes))
    print('Physical DIMACS solver:', 'libz3' if find_library('z3') else 'generic DPLL')


if __name__ == '__main__':
    check_fibers()
    check_flats()
    check_repairs()
    check_sweeps()
    check_table_guards()
    upper_and_truth()
