"""Generate the five proper DIMACS tests and run their five-instruction program."""

from itertools import product


U = (-1, 2, 3)
V = (1, -2, 3)
X = (1, 2, 3)
SETTINGS = ((False, False, False), (True, False, False), (False, True, False),
            (False, False, True), (True, True, False))


def files():
    public = [row for row in product((1, -1), (2, -2), (3, -3)) if row not in (U, X)]
    # Six public rows, including the other copy of V.
    order = (0, 2, 3, 4, 6, 1, 7, 5, 8)
    rows = public + [U, U, (-2, 1, 3)]
    outputs = []
    for changed in SETTINGS:
        body = bytearray(b'p cnf 3 9\n')
        marks = []
        for index in order:
            row = bytearray(('%d %d %d 0\n' % rows[index]).encode())
            if index >= 6:
                assert len(body)%2 == 1 and body[-1:] == b'\n' and row[0:1] == b'-'
                marks.append(len(body)//2)
                if changed[index-6]:
                    row[0] = ord(' ')
            body.extend(row)
        outputs.append(bytes(body[:-1]))
    return outputs, marks


def parse(raw):
    header, *records = raw.splitlines()
    assert header == b'p cnf 3 9'
    rows = []
    for record in records:
        if not record.split():
            continue
        a, b, c, end = map(int, record.split())
        assert end == 0 and {abs(a), abs(b), abs(c)} == {1, 2, 3}
        rows.append((a, b, c))
    assert len(rows) == 9
    return rows


def unpack(raw):
    return [int.from_bytes(raw[i:i+2], 'little') for i in range(0,len(raw),2)]


def brute(rows):
    return any(all(any(bits[abs(x)-1] == (x>0) for x in c) for c in rows)
               for bits in product((False,True), repeat=3))


def run(words, marks):
    # The LOADs have immediate addresses. Only the executed branch returns a verdict.
    a = words[marks[0]]
    b = words[marks[1]]
    if a != b:
        return False, 3
    a = words[marks[2]]
    return a == 0x2d0a, 5


def main():
    outputs, marks = files()
    base = unpack(outputs[0])
    n = 8*len(outputs[0])
    assert 16*((((n+2)-1).bit_length()+15)//16) == 16
    assert len(set(marks)) == 3 and not set(marks)&{0, n, 16}
    assert all(v > max(marks) for v in base)
    verdicts = []
    for raw, bits in zip(outputs, SETTINGS):
        assert len(raw) == len(outputs[0])
        words = unpack(raw)
        assert {i for i,z in enumerate(words) if z != base[i]} == {a for a,b in zip(marks,bits) if b}
        assert all(words[a] == (0x200a if t else 0x2d0a) for a,t in zip(marks,bits))
        answer, cost = run(words, marks)
        assert cost <= 5 and answer == brute(parse(raw))
        verdicts.append(answer)
    assert verdicts == [True,False,False,False,True]
    print(f'{len(outputs)} files of {len(outputs[0])} bytes, addresses {marks}, verdicts {verdicts}')


if __name__ == '__main__':
    main()
