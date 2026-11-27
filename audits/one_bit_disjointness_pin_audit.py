"""Check three dynamic Disjointness encodings on every two-by-two database."""

from itertools import product

from two_bit_warm_repair_audit import forced_model


class Builder:
    def __init__(self, pin_count):
        self.rows = []
        self.pin_positions = []
        self.next_id = 10 * (pin_count+1)
        for ids, values in [((1, 2, 3), (0, 0, 0)), ((4, 5, 6), (0, 1, 0))]:
            for bad in product((0, 1), repeat=3):
                if bad != values:
                    self.rows.append(tuple(-v if b else v for v, b in zip(ids, bad)))

    def pin(self, j):
        complement, flag = 10*j+2, 10*j+3
        self.pin_positions.append(len(self.rows))
        self.rows.extend([(complement, 1, 2), (flag, complement, 1), (-flag, -complement, 1)])
        return flag

    def gate(self, op, a, b):
        node = self.next_id
        self.next_id += 1
        if op == 'and':
            self.rows.extend([(-node, a, 1), (-node, b, 1), (-a, -b, node)])
        elif op == 'or':
            self.rows.extend([(node, -a, 1), (node, -b, 1), (a, b, -node)])
        elif op == 'xor':
            for x, y, z in product((0, 1), repeat=3):
                if z != x ^ y:
                    self.rows.append(tuple(-v if bit else v for v, bit in
                                           zip((a, b, node), (x, y, z))))
        else:
            raise ValueError(op)
        return node

    def tree(self, op, nodes):
        while len(nodes) > 1:
            merged = [self.gate(op, a, b) for a, b in zip(nodes[::2], nodes[1::2])]
            nodes = merged + (nodes[-1:] if len(nodes) % 2 else [])
        return nodes[0]

    def finish(self):
        used = {abs(lit) for row in self.rows for lit in row}
        for v in range(1, self.next_id):
            if v not in used:
                self.rows.append((-v, 1, 2))
        header = f'p cnf {self.next_id-1} {len(self.rows)}\n'
        lines = [f'{a} {b} {c} 0\n' for a, b, c in self.rows]
        position, offsets, marked = len(header), [], set(self.pin_positions)
        for i, line in enumerate(lines):
            if i in marked:
                offsets.append(position + line.index(' ') - 1)
            position += len(line)
        return (header + ''.join(lines)).encode(), offsets


def build(n, mode):
    count = 2*n + n*n
    f = Builder(count + (mode == 'parity'))
    xs = [f.pin(i+1) for i in range(n)]
    ys = [f.pin(n+j+1) for j in range(n)]
    es = [f.pin(2*n+i+1) for i in range(n*n)]
    balance = f.pin(count+1) if mode == 'parity' else None
    if mode == 'no_collision':
        for i, x in enumerate(xs):
            for j, y in enumerate(ys):
                f.rows.append((-x, -y, -es[n*j+i]))
    else:
        hits = []
        for j, y in enumerate(ys):
            terms = [f.gate('and', f.gate('and', x, y), es[n*j+i])
                     for i, x in enumerate(xs)]
            hits.append(f.tree('or', terms))
        if mode == 'collision':
            output = f.tree('or', hits)
        elif mode == 'parity':
            active_disjoint = f.tree('or', [f.gate('and', y, -h) for y,h in zip(ys,hits)])
            p = f.gate('xor', f.tree('xor', es), balance)
            p = f.gate('xor', p, f.tree('xor', xs))
            output = f.gate('xor', p, active_disjoint)
        else:
            raise ValueError(mode)
        f.rows.append((output, 1, 2))
    return f.finish()


def main():
    n = 2
    modes = ['no_collision', 'collision', 'parity']
    states = pairs = unique_links = parity_empty = collision_empty = 0
    setup = [0, 0, 0]
    for mode_index, mode in enumerate(modes):
        raw_base, offsets = build(n, mode)
        files, models = {}, {}
        for flags in range(1 << len(offsets)):
            x = flags & ((1 << n)-1)
            y = (flags >> n) & ((1 << n)-1)
            db = (flags >> (2*n)) & ((1 << (n*n))-1)
            balance = flags >> (2*n+n*n)
            active = [j for j in range(n) if y >> j & 1]
            intersects = [bool(x & (db >> (n*j))) for j in active]
            parity = (x.bit_count() + db.bit_count() + balance) % 2
            expected = {'no_collision':not any(intersects), 'collision':any(intersects),
                        'parity':bool(parity) ^ any(not v for v in intersects)}
            raw = bytearray(raw_base)
            for i, pos in enumerate(offsets):
                assert raw[pos] == ord('2')
                raw[pos] ^= flags >> i & 1
            result = forced_model(raw)
            assert (result is not None) == expected[mode]
            files[flags], models[flags] = bytes(raw), result
            states += 1
        for flags, raw in files.items():
            for i, pos in enumerate(offsets):
                if flags >> i & 1:
                    continue
                after = flags | (1 << i)
                assert raw[:pos] == files[after][:pos]
                assert raw[pos] ^ files[after][pos] == 1
                assert raw[pos+1:] == files[after][pos+1:]
                pairs += 1
                left, right = models[flags], models[after]
                if mode == 'no_collision' and left is not None and right is not None:
                    assert sum(left[v] != right[v] for v in left) == 2
                    unique_links += 1
                y = (flags >> n) & ((1 << n)-1)
                if not y and (i < n or i >= 2*n):
                    if mode == 'parity':
                        assert (left is None) != (right is None)
                        parity_empty += 1
                    if mode == 'collision':
                        assert left is None and right is None
                        collision_empty += 1
                if i >= 2*n and not (flags & ((1 << (2*n))-1)):
                    if mode == 'no_collision':
                        assert left is not None and right is not None
                    setup[mode_index] += 1
    print(f'{states} complete-file model counts; {pairs} single-physical-bit edges')
    print(f'{unique_links} unique-to-unique two-coordinate steps; '
          f'{collision_empty} negative empty-query steps; '
          f'{parity_empty} opposite-verdict empty-query steps')
    print('Blank-selector database-setup edges by mode:', setup)


if __name__ == '__main__':
    main()
