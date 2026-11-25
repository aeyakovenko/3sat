"""Replay the first shifted scan on four proper DIMACS files of the same length."""

from itertools import product

from shifted_dimacs_scan_wave_audit import Memory


def raw_words(word_bytes, a, b):
    clauses = [(literal, sign6 * 6, sign7 * 7)
               for literal in (-2, -3) for sign6, sign7 in product((-1, 1), repeat=2)]
    prefix = b"p cnf 7 12\n" + b"".join(
        (" ".join(map(str, clause)) + " 0\n").encode() for clause in clauses)
    assert len(prefix) < word_bytes
    blank = b" " * word_bytes
    sign = lambda negative: blank[:-1] + (b"-" if negative else b" ")
    first_anchor = blank[:-1] + b"\n"
    second_anchor = b"\n" + blank[1:-1] + b"\n"
    def suffix(name):
        return f"{name} 2 3 0\n".encode().ljust(word_bytes, b" ")
    return [prefix.ljust(word_bytes), first_anchor, sign(a), suffix(1),
            second_anchor, sign(b), suffix(1), sign(False), suffix(4),
            sign(True), suffix(5)]


def direct_sat(data):
    header, *body = data.decode('ascii').splitlines()
    p, cnf, var_count, clause_count = header.split()
    assert (p, cnf) == ('p', 'cnf')
    values = list(map(int, " ".join(body).split()))
    clauses = [values[i:i+3] for i in range(0, len(values), 4)]
    assert len(values) == 4 * int(clause_count)
    assert values[3::4] == [0] * int(clause_count)
    assert all(len({abs(x) for x in clause}) == 3 for clause in clauses)
    return any(all(any(assignment[abs(x)-1] == (x > 0) for x in clause)
                   for clause in clauses)
               for assignment in product((False, True), repeat=int(var_count)))


def observe_pass(mem):
    p = 0
    reads = []
    while p < mem.size:
        dest, stop = mem.interval(p)
        if p <= dest < stop:
            stop = dest if p < dest else p + 1
        if not reads or reads[-1][1] != dest:
            reads.append((p, dest))
        mem.write(dest, stop % mem.size)
        p = stop
    return reads


def normalized(pairs):
    out = []
    for p, value in pairs:
        if not out or value != out[-1][1]:
            out.append((p, value))
    return out


def audit(width):
    q = 1 << width
    m = q // (2*width)
    n = m*width
    assert 16 * (((n+1).bit_length()+15)//16) == width
    common_final = None
    common_other = None
    value_at = {}
    for a, b in product((0, 1), repeat=2):
        words = raw_words(width//8, a, b)
        assert direct_sat(b''.join(words)) == (a == b)
        # The rest of the file is all spaces and gives exactly the same tokens.
        numeric = [int.from_bytes(word, 'little') for word in words]
        blank = int.from_bytes(b' ' * (width//8), 'little')
        assert len(numeric) < m < min(numeric)
        pairs = normalized([*enumerate(numeric), (len(words), blank), (m, 0)])
        mem = Memory(q, pairs)
        observed = observe_pass(mem)
        assert [(lo, val) for lo, _, val in mem.runs()] == normalized(
            (lo, val) for lo, _, val in mem.runs())
        final = tuple(mem.runs())
        if common_final is None:
            common_final = final
        assert final == common_final
        assert mem.interval(2)[0] == numeric[1]+1
        assert mem.interval(5)[0] == numeric[4]+1
        positions = {p for p, _ in observed} | {2, 3, 5, 6}
        traces = Memory(q, observed)
        public = normalized((p, None if p in (2, 5) else traces.interval(p)[0])
                            for p in sorted(positions))
        if common_other is None:
            common_other = public
        assert public == common_other
        for p, selector in ((2, a), (5, b)):
            datum = traces.interval(p)[0]
            assert datum == numeric[p]
            assert datum == value_at.setdefault((p, selector), datum)
    assert value_at[2, 0] != value_at[2, 1]
    assert value_at[5, 0] != value_at[5, 1]


def list_words(width, first, second):
    k = len(first)
    assert k == len(second)
    W = width // 8
    prefix = f"p cnf {k+6} {2*k+10}\n".encode()
    for forced in (1, 2):
        for a, b in product((-1, 1), repeat=2):
            prefix += f"{-forced} {a*3} {b*4} 0\n".encode()
    assert len(prefix) < W
    words = [prefix.ljust(W)]
    blank = b' ' * W
    sign = lambda bit: blank[:-1] + (b'-' if bit else b' ')
    for i, value in enumerate(first + second):
        mask = bytes(ord('\t') if i & (1 << j) else ord(' ') for j in range((2*k-1).bit_length()))
        anchor = mask.ljust(W-1) + b'\n'
        words.extend([anchor, sign(value), f"{7+i%k} 1 2 0\n".encode().ljust(W)])
    words.extend([sign(0), b'5 1 2 0\n'.ljust(W), sign(1), b'6 1 2 0\n'.ljust(W)])
    return words


def audit_all_three_bit_lists():
    width = 2048
    q = 1 << width
    m = q // (2*width)
    blank = int.from_bytes(b' ' * (width//8), 'little')
    lists = list(product((0, 1), repeat=3))
    final = None
    for alice, bob in product(lists, repeat=2):
        words = list_words(width, alice, bob)
        assert direct_sat(b''.join(words)) == (alice == bob)
        nums = [int.from_bytes(word, 'little') for word in words]
        mem = Memory(q, normalized([*enumerate(nums), (len(words), blank), (m, 0)]))
        reads = Memory(q, observe_pass(mem))
        for j, value in enumerate(alice + bob):
            address = 2 + 3*j
            assert reads.interval(address)[0] == nums[address]
            assert mem.interval(address)[0] == nums[address-1]+1
        boundary = tuple(mem.runs())
        if final is None:
            final = boundary
        assert boundary == final


if __name__ == '__main__':
    for w in (1024, 1536, 2048, 4096):
        audit(w)
    print('16 proper DIMACS files, exact complete read traces and coalescent whole memories at four widths')
    audit_all_three_bit_lists()
    print('64 private-list pairs in a three-bit equality test')
