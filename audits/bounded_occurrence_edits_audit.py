"""Check bounded-occurrence DIMACS layouts and relations for nonidentical raw words."""

from collections import Counter
from itertools import product
from random import Random


def digit_sum(n):
    total, start, width = 0, 1, 1
    while start <= n:
        total += (min(n, 10*start-1) - start + 1)*width
        start, width = 10*start, width+1
    return total


def layout(q, m):
    v = 10**q - 1
    head = f"p cnf {10*v} {13*v+m}\n".encode()
    pin_bytes = 3*digit_sum(v) + (36*(q+1)+80)*v + 3*(v-m)
    extra = digit_sum(m) + digit_sum(3*m) - digit_sum(2*m) + (q+5)*m
    return head, len(head) + pin_bytes + extra - 1


def field_start(q, m, i):
    head, _ = layout(q, m)
    j = i-1
    return (len(head) + 4*digit_sum(j) + digit_sum(2*m+j)-digit_sum(2*m)
            + j*(7*q+29) + len(str(i))+len(str(2*m+i))+2)


def pin(s, first):
    groups, ds = [], []
    for j in range(3):
        a, b, d = (first+3*j+k for k in range(3))
        groups.append((s, a, b))
        groups.extend([(d, a, -b), (d, -a, b), (d, -a, -b)])
        ds.append(-d)
    return groups+[tuple(ds)]


def small_layout(q, marks):
    v, m = 10**q-1, len(marks)
    head, size = layout(q, m)
    clauses = []
    for j in range(1, v+1):
        clauses.extend(pin(j if j in marks else -j, v+9*(j-1)+1))
    clauses.extend((i, 2*m+i, a) for i, a in enumerate(marks, 1))
    key = lambda x: (abs(x), x < 0)
    clauses = sorted((tuple(sorted(c, key=key)) for c in clauses),
                     key=lambda c: tuple(map(key, c)))
    assert len(set(clauses)) == 13*v+m
    degree = Counter(abs(x) for c in clauses for x in c)
    assert len(degree) == 10*v and max(degree.values()) == 4
    blob = head + '\n'.join('%d %d %d 0' % c for c in clauses).encode()
    assert len(blob) == size
    for i, a in enumerate(marks, 1):
        start = field_start(q, m, i)
        assert blob[start:start+q] == str(a).encode()
    return len(blob)


def centered_name(q, left, right, number):
    pattern = [None]*q
    pattern[0], pattern[left], pattern[right] = '8', '5', '5'
    digits = iter(str(number).zfill(q-3))
    assert len(str(number)) <= q-3
    return ''.join(next(digits) if x is None else x for x in pattern)


def large_layout(q, width):
    v, m = 10**q-1, (10**q-1)//8192
    head, size = layout(q, m)
    assert 16*((((8*size+1).bit_length())+15)//16) == width
    W = width//8
    assert width & (width-1) == 0 and q >= 2*W
    used, words = set(), []
    for i in (list(range(1, 12)) + [m//3, m//2, m-1, m]):
        start = field_start(q, m, i)
        low = ((start+1+W-1)//W)*W-start
        high = low+W-1
        assert 1 <= low < high < q
        # Spread the free digits throughout the name, including the marked word.
        base = Random(q*1009+i).randrange(10**(q-3)//2)
        for trial in range(len(used)+1):
            name = centered_name(q, low, high, base+trial)
            variants = [name[:high]+str(k)+name[high+1:] for k in range(3, 8)]
            if not used.intersection(variants):
                break
        else:
            raise AssertionError("greedy choice failed")
        used.update(variants)
        center = int.from_bytes(name[low:high+1].encode(), 'little')
        assert center % 256 == center >> (width-8) == 53
        assert (start+low)//W < center
        for d, candidate in zip(range(-2, 3), variants):
            assert candidate[0] == '8' and 3*m < int(candidate) <= v
            raw = int.from_bytes(candidate[low:high+1].encode(), 'little')
            assert raw == center + (d << (width-8))
        words.append(center)
    assert len(set(words)) > 1 and len(used) == 5*len(words)
    return words


def opcode_checks(a, b, w):
    mod = 1 << w
    delta = 1 << (w-8)
    def bitwise(x, y, table):
        return ((~x & ~y if table & 1 else 0) |
                (~x & y if table & 2 else 0) |
                (x & ~y if table & 4 else 0) |
                (x & y if table & 8 else 0)) % mod
    def rotate(x, y):
        c = y % w
        return ((x << c) | (x >> (w-c))) % mod
    ops = [lambda x, y: (x+y) % mod, lambda x, y: (x-y) % mod,
           lambda x, y: (x*y) % mod, lambda x, y: x < y,
           lambda x, y: x == y, lambda x, y: x <= y,
           lambda x, y: (x << (y%w)) % mod, lambda x, y: x >> (y%w),
           lambda x, y: 0 if y>=w else (x << y)%mod, rotate]
    ops += [lambda x, y, t=t: bitwise(x, y, t) for t in range(16)]
    ds = range(-2, 3)
    for first, second in ((a,b),(b,a)):
        for op in ops:
            original = op(first, second)
            ok = {(i,j) for i in ds for j in ds
                  if op(first+i*delta, second+j*delta) == original}
            for relation in (ok, {(j,i) for i,j in ok}):
                assert (any((0,j) in relation for j in ds if j) or
                        all(any((i,j) in relation for j in ds) for i in ds))
    return 2*len(ops)


def frequent_word(q):
    v = 10**q - 1
    m = v//32
    head = f"p cnf {10*v} {13*v+m}\n".encode()
    size = (len(head) + 3*digit_sum(v) + v*(36*(q+1)+80) + 3*(v-m-q)
            + digit_sum(q+m)-digit_sum(q) + m*(2*q+5) - 1)
    w = 16*((((8*size+1).bit_length())+15)//16)
    W = w//8
    assert W <= q and W & (W-1) == 0
    left, right = (W-1)//2, W//2
    def separator(i):
        a = q+i
        pins = 3*digit_sum(a-1)+(a-1)*(6*(q+1)+18) - 3*(i-1)
        rows = digit_sum(a-1)-digit_sum(q)+(i-1)*(2*q+5)
        return len(head)+pins+rows+len(str(a))+1+q
    buckets = [[] for _ in range(W)]
    for i in range(1,m+1):
        t = ((separator(i)-left)*pow(3,-1,W)) % W
        buckets[t].append(i)
    t = max(range(W), key=lambda shift: len(buckets[shift]))
    assert len(buckets[t]) >= m//W
    second_pool = list(range(3*10**(q-1),4*10**(q-1)))
    third_pool = list(range(8*10**(q-1),9*10**(q-1)))
    seconds = [a for a in second_pool if str(a).endswith('5'*left)]
    thirds = [b for b in third_pool if str(b).startswith('8'*right)]
    hits = min(len(buckets[t]), len(seconds), len(thirds))
    special = dict(zip(buckets[t][:hits],zip(seconds[:hits],thirds[:hits])))
    free_u = iter(sorted(set(second_pool)-set(seconds[:hits])))
    free_v = iter(sorted(set(third_pool)-set(thirds[:hits])))
    clauses = [(q+i, *(special[i] if i in special else (next(free_u), next(free_v))))
               for i in range(1,m+1)]
    truth = set(range(q+1, q+m+1)) | set(range(1,t+1)) | set(range(q+m+1,q+m+1+q-t))
    for j in range(1,v+1):
        clauses.extend(pin(j if j in truth else -j, v+9*(j-1)+1))
    key = lambda x: (abs(x), x<0)
    clauses = sorted((tuple(sorted(c, key=key)) for c in clauses),
                     key=lambda c: tuple(map(key,c)))
    blob = head + '\n'.join('%d %d %d 0' % c for c in clauses).encode()
    assert len(blob)==size and len(set(clauses))==len(clauses)
    assert max(Counter(abs(x) for c in clauses for x in c).values())==4
    goal = b'5'*left + b' ' + b'8'*right
    for i in special:
        start = separator(i)-3*t-left
        assert start%W == 0 and blob[start:start+W] == goal
    return hits


def main():
    port = pin(1, 2)
    for setting in (False, True):
        ok = 0
        for private in product((False,True), repeat=9):
            bits = (False, setting) + private
            ok += all(any(bits[abs(x)] == (x>0) for x in c) for c in port)
        assert bool(ok) == setting

    repeats = frequent_word(4)
    small = [small_layout(2, [85]), small_layout(3, [805, 815, 825]),
             small_layout(4, [8055, 8155, 8255])]
    scales = set()
    checks = 0
    for q in range(25, 601):
        _, size = layout(q, (10**q-1)//8192)
        w = 16*((((8*size+1).bit_length())+15)//16)
        if w & (w-1) or w in scales or q < 2*(w//8):
            continue
        words = large_layout(q,w)
        checks += sum(opcode_checks(a,b,w) for a,b in zip(words,words[1:]))
        scales.add(w)
    assert len(scales) >= 3
    print(f"1,024 pin settings, {sum(small):,} bytes of actual proper files, "
          f"widths {sorted(scales)}, {checks:,} heterogeneous opcode pairs, "
          f"{repeats} guaranteed occurrences of one straddling word")


if __name__ == '__main__':
    main()
