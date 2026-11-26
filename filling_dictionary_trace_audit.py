"""Check exact membership and the nodes touched by one edit on proper DIMACS files."""

from itertools import product


def fixture():
    base = bytearray(b"p cnf 4 8\n")
    positions = []
    for signs in product((False, True), repeat=3):
        tokens = [(b"-" if negative else b"") + str(name).encode()
                  for name, negative in zip((1, 4, 2), signs)]
        row = b" ".join(tokens) + b" 0\n"
        positions.append(len(base) + row.index(b"2"))
        base.extend(row)
    return bytes(base), positions


def fill(base, positions, bits):
    raw = bytearray(base)
    for i, pos in enumerate(positions):
        raw[pos] ^= (bits >> i) & 1  # ASCII 2 and 3 differ only in the low bit.
    return bytes(raw)


def sat(raw):
    header, *lines = raw.splitlines()
    assert header == b"p cnf 4 8" and len(lines) == 8
    clauses = []
    for line in lines:
        x, y, z, zero = map(int, line.split())
        assert zero == 0 and len({abs(x), abs(y), abs(z)}) == 3
        clauses.append((x, y, z))
    return any(all(any(((a >> (abs(lit)-1)) & 1) != (lit < 0) for lit in c) for c in clauses)
               for a in range(16))


def check_windows(files, verdicts, sites):
    header, body = files[0].split(b"\n", 1)
    header += b"\n"
    body_size = len(body) - 1
    stride = body_size + 64
    window_count = 5
    total_size = len(header) + window_count * stride + 1
    occupied_words = []
    for window in range(window_count):
        start = window * stride
        changed = {len(header) + start + (p - len(header)) for p in sites}
        words = {p // 16 for p in changed}
        assert all(words.isdisjoint(earlier) for earlier in occupied_words)
        occupied_words.append(words)
        for raw, expected in zip(files, verdicts):
            body = raw[len(header):-1]
            padded = header + b" " * start + body + b" " * (window_count*stride - start - body_size) + b"\n"
            assert len(padded) == total_size and sat(padded) == expected
            baseline = files[0][len(header):-1]
            relocated = {len(header) + start + j for j, (x, y) in enumerate(zip(baseline, body)) if x != y}
            assert relocated <= changed
    return len(files) * window_count


class Dictionary:
    def __init__(self, rows, width):
        self.count = 1 << (width - 1).bit_length()
        self.tables = [dict() for _ in range(2 * self.count)]
        self.answers = {}
        for parts, answer in rows:
            root, _ = self.evaluate(parts, insert=True)
            assert root not in self.answers
            self.answers[root] = answer

    def evaluate(self, parts, insert=False):
        """One record per node contains address operands and retrieved value."""
        parts = list(parts) + [0] * (self.count - len(parts))
        records = []
        values = [0] * (2 * self.count)
        for node in reversed(range(1, 2 * self.count)):
            if node >= self.count:
                key = parts[node - self.count]
            else:
                key = (values[2 * node], values[2 * node + 1])
            table = self.tables[node]
            if insert and key not in table:
                table[key] = len(table) + 1
            value = table.get(key, 0)
            values[node] = value
            records.append((node, key, value))
        return values[1], records


def main():
    base, sites = fixture()
    files = [fill(base, sites, bits) for bits in range(1 << len(sites))]
    verdicts = [sat(f) for f in files]
    assert not verdicts[0] and all(verdicts[1 << i] for i in range(8))
    relocated = check_windows(files, verdicts, sites)
    # Give each of the eight marked bytes its own protected half, and vary
    # the number of marked halves to exercise incomplete binary tree levels.
    checks = neighboring = opposite = 0
    for width in range(1, 9):
        capacity = 1 << width
        row_order = [0] + [1 << i for i in range(width)]
        row_order += [x for x in range(capacity) if x not in row_order]
        fields = [tuple(files[x][p] & 1 for p in sites[:width]) for x in range(capacity)]
        for k in sorted({v for v in (1, 3, 7, 11, 29, capacity) if v <= capacity}):
            members = set(row_order[:k])
            table = Dictionary([(fields[x], verdicts[x]) for x in row_order[:k]], width)
            traces = []
            for x in range(capacity):
                root, records = table.evaluate(fields[x])
                assert bool(root) == (x in members)
                if root:
                    assert table.answers[root] == verdicts[x]
                traces.append(records)
                checks += 1
            for x in members:
                for bit in range(width):
                    y = x ^ (1 << bit)
                    if y <= x or y not in members:
                        continue
                    node = table.count + bit
                    path = set()
                    while node:
                        path.add(node)
                        node //= 2
                    changed = {first[0] for first, second in zip(traces[x], traces[y])
                               if first != second}
                    assert changed <= path and len(changed) <= 1 + (width-1).bit_length()
                    neighboring += 1
                    opposite += verdicts[x] != verdicts[y]
    print(f"{len(files)} proper DIMACS files, {checks} exact membership tests, "
          f"{neighboring} listed one-bit pairs ({opposite} with opposite verdicts), "
          f"{relocated} relocated files")


if __name__ == "__main__":
    main()
