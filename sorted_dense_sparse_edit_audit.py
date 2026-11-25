"""Check the dense sorted core without allocating its exponential-size large examples."""


def digit_total(end):
    total, start, width = 0, 1, 1
    while start <= end:
        stop = min(end, 10*start - 1)
        total += (stop-start+1) * width
        start, width = 10*start, width+1
    return total


def pin_bytes(end, digits, center):
    return 4*(digit_total(end) + end*(2*digits+5)) + 8*end - 4*int(center <= end)


def extra_bytes(end, digits):
    return digit_total(end) + digit_total(end+1) - 1 + end*(digits+5)


def parameters(digits):
    top = 10**digits - 1
    center = 5*(top//9)
    marked = top//4
    header = f'p cnf {top} {4*(top-2)+marked}\n'.encode()
    total_bytes = len(header) + pin_bytes(top-2, digits, center) + extra_bytes(marked, digits) - 1
    return top, center, marked, header, total_bytes


def field_start(i, digits):
    _, center, _, header, _ = parameters(digits)
    return (len(header) + pin_bytes(i-1, digits, center) + extra_bytes(i-1, digits)
            + len(str(i)) + len(str(i+1)) + 2)


def small_file(q):
    top, center, marked, header, size = parameters(q)
    data = []
    for i in range(1, top-1):
        if i <= marked:
            data.append((i, i+1, center))
        first = i if i == center else -i
        data.extend((first, a, b) for a in (top-1, 1-top) for b in (top, -top))
    key = lambda c: tuple((abs(x), x < 0) for x in c)
    assert data == sorted(set(data), key=key)
    file = header + '\n'.join('%d %d %d 0' % c for c in data).encode()
    assert len(file) == size
    for i in range(1, marked+1):
        j = field_start(i, q)
        assert file[j:j+q] == b'5' * q
    return marked


def large_file(q):
    top, center, marked, _, size = parameters(q)
    width = 16*((((8*size+1).bit_length())+15)//16)
    step = width//8
    odd = width//(width & -width)
    rep = 0
    for count in range(1, odd+1):
        rep = 256*rep + 1
        if rep % odd == 0:
            break
    delta = rep << (8*(step-count))
    assert count <= step//2 and delta % width == 0 and (delta*delta) % (1 << width) == 0
    checked = 0
    for i in sorted({1, 2, 10**(q//2), marked//2, marked-1, marked}):
        start = field_start(i, q)
        aligned = ((start+1+step-1)//step)*step
        off = aligned - start
        assert 1 <= off and off+step <= q
        base = int.from_bytes(b'5'*step, 'little')
        assert aligned//step < base
        for d in range(3, 8):
            name = bytearray(b'5'*q)
            name[off+step-count:off+step] = bytes([48+d])*count
            target = int(name)
            assert i+1 < target < top-1 and (target == center) == (d == 5)
            value = int.from_bytes(name[off:off+step], 'little')
            assert value == base+(d-5)*delta
            checked += 1
    return checked


if __name__ == '__main__':
    fields = sum(small_file(q) for q in (2, 3, 4))
    edits = sum(large_file(q) for q in range(96, 241, 8))
    print(f'{fields} actual clause offsets and {edits} large-order aligned word edits checked')
