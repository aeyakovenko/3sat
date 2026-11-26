"""Audit binary SLP certificates for causal, fixed-width tape histories.

The audit's equality routine is exact and skips shared blocks. Its worst-case
running time can depend on expanded length. The fast general equality theorem
used by the manuscript is separate.
"""
from argparse import ArgumentParser
from functools import cache

START, END = "[", "]"


class SLP:
    def __init__(self):
        self.rules, self.length, self.index = [], [], {}

    def rule(self, item):
        if item not in self.index:
            self.index[item] = len(self.rules)
            self.rules.append(item)
            size = 1 if item[0] == "leaf" else self.length[item[1]] + self.length[item[2]]
            self.length.append(size)
        return self.index[item]

    def leaf(self, x):
        return self.rule(("leaf", x))

    def join(self, l, r):
        return self.rule(("join", l, r))

    def fold(self, items):
        if len(items) == 1:
            return items[0]
        mid = len(items)//2
        return self.join(self.fold(items[:mid]), self.fold(items[mid:]))

    def repeat(self, root, count):
        if count == 1:
            return root
        half = self.repeat(root, count//2)
        both = self.join(half, half)
        return self.join(both, root) if count % 2 else both

    def change(self, root, pos, val):
        a = self.rules[root]
        if a[0] == "leaf":
            return self.leaf(val)
        l, r = a[1:]
        if pos < self.length[l]:
            return self.join(self.change(l, pos, val), r)
        return self.join(l, self.change(r, pos-self.length[l], val))

    def section(self, root, lo, hi):
        if lo == 0 and hi == self.length[root]:
            return root
        _, l, r = self.rules[root]
        mid = self.length[l]
        if hi <= mid:
            return self.section(l, lo, hi)
        if lo >= mid:
            return self.section(r, lo-mid, hi-mid)
        return self.join(self.section(l, lo, mid), self.section(r, 0, hi-mid))

    def image(self, root, fn):
        @cache
        def visit(node):
            rule = self.rules[node]
            if rule[0] == "leaf":
                return self.leaf(fn(rule[1]))
            return self.join(visit(rule[1]), visit(rule[2]))
        return visit(root)

    def same_word(self, left, right):
        if self.length[left] != self.length[right]:
            return False
        a, b = [left], [right]
        while a:
            if a[-1] == b[-1]:
                a.pop()
                b.pop()
                continue
            size_l, size_r = self.length[a[-1]], self.length[b[-1]]
            if size_l == size_r == 1:
                return False
            for stack, split in [(a, size_l >= size_r), (b, size_r >= size_l)]:
                if split:
                    _, l, r = self.rules[stack.pop()]
                    stack.extend((r, l))
        return not b

    def leaves(self, root):
        stack = [root]
        while stack:
            rule = self.rules[stack.pop()]
            if rule[0] == "leaf":
                yield rule[1]
            else:
                stack.extend((rule[2], rule[1]))

    def summaries(self, root, atom, merge):
        @cache
        def visit(node):
            rule = self.rules[node]
            return atom(rule[1]) if rule[0] == "leaf" else merge(visit(rule[1]), visit(rule[2]))
        return visit(root)

    def windows(self, root, size):
        """Collect windows crossing each reachable binary production once."""
        found = set()
        productions = 0

        def merge(left, right):
            nonlocal productions
            productions += 1
            around = left[1] + right[0]
            found.update(around[p:p+size] for p in range(len(around)-size+1))
            return ((left[0]+right[0])[:size-1], (left[1]+right[1])[-(size-1):])

        self.summaries(root, lambda x: ((x,), (x,)), merge)
        assert len(found) <= productions*(size-1)
        return found, productions


def action(sym):
    ch, state = sym
    if not state:
        return ch, "", 0
    if state == "home" and ch == "L":
        return ch, "carry", 1
    if state == "carry":
        return {"0": ("1", "back", -1), "1": ("0", "carry", 1),
                "R": ("R", "accept", 0)}[ch]
    if state == "back":
        return (ch, "home", 0) if ch == "L" else (ch, "back", -1)
    if state == "accept" and ch == "R":
        return ch, "accept", 0
    raise ValueError(sym)


def initial(width, bits):
    return (("L", "home"),) + tuple((c, "") for c in "0"*bits+"R"+"."*(width-bits-2))


def tape_step(row):
    pos, = [i for i, sym in enumerate(row) if sym[1]]
    char, state, offset = action(row[pos])
    cells = list(row)
    cells[pos] = (char, "")
    assert 0 <= pos+offset < len(cells)
    cells[pos+offset] = (cells[pos+offset][0], state)
    return tuple(cells)


def counter(width, bits):
    row = initial(width, bits)
    rows, snapshots = [row], []
    while all(sym[1] != "accept" for sym in row):
        if row[0][1] == "home":
            snapshots.append(tuple(cell[0] for cell in row[1:1+bits]))
        row = tape_step(row)
        rows.append(row)
    assert len(rows)-1 == 5*((1 << bits)-1)-bits+2
    assert len(set(snapshots)) == 1 << bits
    return rows, snapshots


def valid_triple(l, c, r):
    if isinstance(c, str):
        return True
    old, new = c
    try:
        char, state, offset = action(old)
        incoming = [state] if state and offset == 0 else []
        if (l == START and offset == -1) or (r == END and offset == 1):
            return False
        for neighbor, direction in [(l, 1), (r, -1)]:
            if not isinstance(neighbor, str):
                _, st, mv = action(neighbor[0])
                if st and mv == direction:
                    incoming.append(st)
        return len(incoming) <= 1 and new == (char, incoming[0] if incoming else "")
    except (KeyError, ValueError):
        return False


def verify(g, root, w, h, first):
    stride = w+2
    if g.length[root] != stride*h:
        return (False,)*5
    header = lambda x: x if isinstance(x, str) else "."
    layout = g.fold([g.leaf(START), g.repeat(g.leaf("."), w), g.leaf(END)])
    marked = g.same_word(g.image(root, header), g.repeat(layout, h))
    if not marked:
        return (False,)*5
    triples, _ = g.windows(root, 3)
    local = all(valid_triple(*triple) for triple in triples)
    old, new = [g.image(root, lambda x, j=j: x if isinstance(x, str) else x[j]) for j in (0, 1)]
    upto = (h-1)*stride
    vertical = h == 1 or g.same_word(g.section(new, 0, upto), g.section(old, stride, h*stride))
    initial_ok = tuple(g.leaves(g.section(old, 0, stride))) == (START, *first, END)
    final = tuple(g.leaves(g.section(new, upto, h*stride)))[1:-1]
    accepted = any(cell[1] == "accept" for cell in final)
    return marked, local, vertical, initial_ok, accepted


def build(g, rows):
    old = tuple(zip(rows[0], rows[1]))
    core = g.fold([g.leaf(t) for t in old])
    parts = []
    for i, (a, b) in enumerate(zip(rows, rows[1:])):
        pairs = tuple(zip(a, b))
        changes = [j for j in range(len(a)) if old[j] != pairs[j]]
        assert i == 0 or len(changes) <= 4
        for j in changes:
            core = g.change(core, j, pairs[j])
        parts.append(g.fold([g.leaf(START), core, g.leaf(END)]))
        old = pairs
    return parts


def stack_rows(g, first, count):
    """Retain a grammar root and pop link in every immutable stack node."""
    def push(sym, previous, side):
        assert not sym[1]
        leaf = g.leaf((sym, sym))
        if previous is None:
            text = leaf
        else:
            text = g.join(previous[2], leaf) if side == "left" else g.join(leaf, previous[2])
        return sym, previous, text

    def piece(stack):
        return [] if stack is None else [stack[2]]

    left = right = None
    for c in reversed(first[1:]):
        right = push(c, right, "right")
    head = first[0]
    parts = []
    for _ in range(count):
        ch, st, direction = action(head)
        if direction == 1:
            neighbor, after, _ = right
            enters = (neighbor[0], st)
            mid = [g.leaf((head, (ch, ""))), g.leaf((neighbor, enters))]
            content = piece(left) + mid + piece(after)
            left, head, right = push((ch, ""), left, "left"), enters, after
        elif direction == -1:
            neighbor, before, _ = left
            enters = (neighbor[0], st)
            mid = [g.leaf((neighbor, enters)), g.leaf((head, (ch, "")))]
            content = piece(before) + mid + piece(right)
            left, head, right = before, enters, push((ch, ""), right, "right")
        else:
            enters = (ch, st)
            content = piece(left) + [g.leaf((head, enters))] + piece(right)
            head = enters
        parts.append(g.fold([g.leaf(START)] + content + [g.leaf(END)]))
    return parts


def positive(w, bits):
    rows, snapshots = counter(w, bits)
    g = SLP()
    parts = stack_rows(g, rows[0], len(rows))
    assert len(g.rules) <= 10*(w+len(rows))
    reference = build(g, rows+[rows[-1]])
    assert all(g.same_word(x, y) for x, y in zip(parts, reference))
    h = w**4
    active = len(rows)-1
    assert active < h
    root = g.join(g.fold(parts[:-1]), g.repeat(parts[-1], h-active))
    assert all(verify(g, root, w, h, rows[0]))
    project = lambda x: x if isinstance(x, str) else x[0][0]
    words, num = g.windows(g.image(root, project), bits)
    assert set(snapshots) <= words
    assert num < 12*(w+active)*(w.bit_length()+1) + 3*h.bit_length()
    # Every window contains exactly one L. Its position reveals the
    # alignment; its next bits identify the completed counter value.
    offsets = min(bits, w-bits)
    size = bits+2+offsets
    assert size <= w+2
    padded, productions = g.windows(g.image(root, project), size)
    recovered = {(v.index("L"), v[v.index("L")+1:v.index("L")+1+bits])
                 for v in padded if v.count("L") == 1}
    assert all((r, x) in recovered for r in range(offsets+1) for x in snapshots[1:])
    assert len(padded) >= (len(snapshots)-1)*(offsets+1)
    assert productions < 12*(w+active+h.bit_length())
    return active, num, (len(snapshots)-1)*(offsets+1), size


def high_bit_image(history, bit):
    """Apply one fixed letter-to-word map to each R pair of the old history."""
    def row_image(row):
        old_r, new_r = row[-1]
        assert old_r[0] == new_r[0] == "R"
        return row[:-1] + (((bit, old_r[1]), (bit, new_r[1])),
                            (("R", ""), ("R", "")))
    return [row_image(row) for row in history]


def morphic_counter(bits):
    # Streams prior to executing CARRY at the right sentinel have exactly
    # one final transition whose new head is on R and no earlier visit there.
    source = initial(2, 0)
    result = [tuple(zip(source, tape_step(source)))]
    for m in range(1, bits+1):
        base = (("L", ""),) + (("0", ""),)*(m-1)
        row = base + (("0", "carry"), ("R", ""))
        bridge = []
        while row[0][1] != "home":
            nxt = tape_step(row)
            bridge.append(tuple(zip(row, nxt)))
            row = nxt
        row = base + (("1", "carry"), ("R", ""))
        last = tuple(zip(row, tape_step(row)))
        result = high_bit_image(result, "0") + bridge + high_bit_image(result, "1") + [last]
        assert len(bridge) == m+1
    return result


def check_morphic_counter(max_bits):
    total = 0
    for bits in range(max_bits+1):
        w = 2*bits+5
        rows, _ = counter(w, bits)
        expected = (tuple(zip(a, b)) for a, b in zip(rows[:-2], rows[1:-1]))
        compact = morphic_counter(bits)
        assert len(compact) == len(rows)-2
        pad = (((".", ""), (".", "")),) * (w-bits-2)
        assert all(row+pad == true for row, true in zip(compact, expected))
        total += len(compact)
    return total


class RowGrammar:
    def __init__(self):
        self.rules = []

    def rule(self, operation, *args):
        self.rules.append((operation, *args))
        return len(self.rules)-1

    def sequence(self, block):
        if len(block) == 1:
            return block[0]
        middle = len(block)//2
        return self.rule("join", self.sequence(block[:middle]), self.sequence(block[middle:]))


def transform_cell(name, sym):
    if isinstance(sym, str):
        return (sym,)
    ch, state = sym
    if name in ("0", "1") and ch == "R":
        return ((name, state), ("R", ""))
    if name == "flip" and ch in "01":
        return (("1" if ch == "0" else "0", state),)
    if name == "double_zero" and ch == "0":
        return (sym, sym)
    return (sym,)


def transform_pair(name, pair):
    if isinstance(pair, str):
        return (pair,)
    a, b = (transform_cell(name, side) for side in pair)
    if len(a) != len(b):
        raise ValueError("unaligned substitution")
    return tuple(zip(a, b))


def morphic_dag(bits):
    gram = RowGrammar()
    base = initial(2, 0)
    root = gram.rule("row", tuple(zip(base, tape_step(base))))
    for m in range(1, bits+1):
        prefix = (("L", ""),) + (("0", ""),)*(m-1)
        row = prefix + (("0", "carry"), ("R", ""))
        bridge = []
        while row[0][1] != "home":
            nxt = tape_step(row)
            bridge.append(gram.rule("row", tuple(zip(row, nxt))))
            row = nxt
        row = prefix + (("1", "carry"), ("R", ""))
        last = gram.rule("row", tuple(zip(row, tape_step(row))))
        root = gram.sequence([gram.rule("map", "0", root), *bridge,
                              gram.rule("map", "1", root), last])
    return gram, root


def check_row_dag(gram, root, w, h, initial_row, final_row):
    # Reachability and occurrence counts suffice to check typed substitutions,
    # valid row counts, and the bound on all expanded intermediate lengths.
    from collections import Counter
    order = []
    seen = set()

    def visit(node):
        if node in seen:
            return
        seen.add(node)
        rule = gram.rules[node]
        kids = rule[1:] if rule[0] == "join" else rule[2:] if rule[0] == "map" else ()
        for child in kids:
            visit(child)
        order.append(node)

    visit(root)
    occ = {}
    for node in order:
        rule = gram.rules[node]
        if rule[0] == "row":
            bag = Counter((START, *rule[1], END))
        elif rule[0] == "join":
            bag = occ[rule[1]] + occ[rule[2]]
        else:
            bag = Counter()
            for symbol, count in occ[rule[2]].items():
                try:
                    expansion = transform_pair(rule[1], symbol)
                except ValueError:
                    return (False,)*4
                for out in expansion:
                    bag[out] += count
        if sum(bag.values()) > h*(w+2):
            return (False,)*4
        occ[node] = bag
    if occ[root][START] != h or sum(occ[root].values()) != h*(w+2):
        return (False,)*4

    g = SLP()

    def endpoint(node, side):
        spelling = {}
        for pair in occ[node]:
            cell = pair if isinstance(pair, str) else pair[side]
            spelling[cell] = g.leaf(cell)
        while gram.rules[node][0] != "row":
            rule = gram.rules[node]
            if rule[0] == "join":
                node = rule[side+1]
            else:
                name, node = rule[1:]
                letters = {pair if isinstance(pair, str) else pair[side] for pair in occ[node]}
                spelling = {a: g.fold([spelling[b] for b in transform_cell(name, a)])
                            for a in letters}
        return g.fold([spelling[START], *[spelling[pair[side]] for pair in gram.rules[node][1]],
                       spelling[END]])

    joins = [gram.rules[node] for node in order if gram.rules[node][0] == "join"]
    vertical = all(g.same_word(endpoint(l, 1), endpoint(r, 0)) for _, l, r in joins)
    ends_ok = (tuple(g.leaves(endpoint(root, 0))) == (START, *initial_row, END)
               and tuple(g.leaves(endpoint(root, 1))) == (START, *final_row, END))

    if all(gram.rules[n][0] != "map" or gram.rules[n][1] in ("0", "1") for n in order):
        # For high-bit insertions both endpoints are shared triples. Compare
        # every join by one equality of separator-delimited endpoint lists.
        split = {}
        comparisons = []
        def assemble(triple):
            left, tag, right = triple
            return g.fold([left, g.leaf(tag), right])
        for n in order:
            rule = gram.rules[n]
            if rule[0] == "row":
                for side in (0, 1):
                    word = [pair[side] for pair in rule[1]]
                    r, = [i for i, c in enumerate(word) if c[0] == "R"]
                    split[n, side] = (g.fold([g.leaf(START)] + [g.leaf(c) for c in word[:r]]),
                                      word[r], g.fold([g.leaf(c) for c in word[r+1:]] + [g.leaf(END)]))
            elif rule[0] == "join":
                _, l, r = rule
                comparisons.append((assemble(split[l, 1]), assemble(split[r, 0])))
                split[n, 0], split[n, 1] = split[l, 0], split[r, 1]
            else:
                for side in (0, 1):
                    left, (_, head), right = split[rule[2], side]
                    split[n, side] = g.join(left, g.leaf((rule[1], head))), ("R", ""), right
        if comparisons:
            lists = [g.fold([g.join(pair[side], g.leaf(";")) for pair in comparisons])
                     for side in (0, 1)]
            assert g.same_word(*lists) == vertical

    # (prefix of length 2, suffix of length 2, legal) is a finite monoid.
    # A local failure in a transformed row must be checked after substitution.
    empty = ((), (), True)

    def combine(a, b):
        side = a[1] + b[0]
        legal = a[2] and b[2] and all(valid_triple(*side[j:j+3]) for j in range(len(side)-2))
        return (a[0]+b[0])[:2], (a[1]+b[1])[-2:], legal

    def evaluate(symbols, valuation):
        accum = empty
        for symbol in symbols:
            accum = combine(accum, valuation[symbol])
        return accum

    @cache
    def monitor(node, table):
        # Tables use the insertion order of this specific node's Counter.
        val = dict(zip(occ[node], table))
        rule = gram.rules[node]
        if rule[0] == "row":
            return evaluate((START, *rule[1], END), val)
        if rule[0] == "join":
            return combine(*(monitor(k, tuple(val[a] for a in occ[k])) for k in rule[1:]))
        name, child = rule[1:]
        return monitor(child, tuple(evaluate(transform_pair(name, a), val) for a in occ[child]))

    local = monitor(root, tuple(((a,), (a,), True) for a in occ[root]))[2]
    return True, vertical, local, ends_ok


def row_dag_audit():
    honest = 0
    for m in range(1, 7):
        gram, root = morphic_dag(m)
        rows, _ = counter(m+2, m)
        initial_row, final_row = rows[0], rows[-2]
        h = len(rows)-2
        check = lambda node: check_row_dag(gram, node, m+2, h, initial_row, final_row)
        assert all(check(root))
        # The two interior mismatches occur only across a concatenation.
        _, left, right = gram.rules[root]
        assert check(gram.rule("join", right, left))[:3] == (True, False, True)
        # A flip has fully aligned projections and preserves all internal
        # joins, but violates the physical update on some transformed row.
        assert check(gram.rule("map", "flip", root))[:3] == (True, True, False)
        # Doubling all zeroes breaks synchronization on a write 0 -> 1.
        assert not check(gram.rule("map", "double_zero", root))[0]
        # Ill-typed unused nodes play no part in the reachable certificate.
        assert all(check(root))
        honest += h
    return honest


def mutations():
    w, bits = 5, 2
    rows, _ = counter(w, bits)
    g = SLP()
    parts = build(g, rows)
    base = g.fold(parts)
    h, s = len(parts), w+2
    check = lambda r: verify(g, r, w, h, rows[0])
    assert all(check(base))
    # Replace one transition by a different genuine transition.
    for i in range(1, h-1):
        mixed = parts[:i]+[parts[i+1]]+parts[i+1:]
        assert check(g.fold(mixed)) == (True, True, False, True, True)
    # Alter an internal config consistently on both occurrences; the vertical
    # projections still match, but two adjacent transitions acquire a tape write.
    for i in range(1, h):
        wrong = ("0", "")
        pos = (i-1)*s + w
        r = g.change(base, pos, (rows[i-1][-1], wrong))
        r = g.change(r, pos+s, (wrong, rows[i+1][-1]))
        assert check(r) == (True, False, True, True, True)
    assert check(g.change(base, w+1, START))[0] is False
    assert verify(g, g.fold(parts[1:]), w, h-1, rows[0]) == (True, True, True, False, True)
    assert verify(g, g.fold(parts[:-1]), w, h-1, rows[0]) == (True, True, True, True, False)
    return (h-2)+(h-1)+3


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--large", action="store_true", help="also check the million-row history")
    widths = (8, 16, 24, 32) if parser.parse_args().large else (8, 16, 24)
    for width in widths:
        m = 4*(width.bit_length()-1)-7
        steps, size, distinguishable, window = positive(width, m)
        print(f"width {width}, {1<<m} displayed words, {steps} active steps, "
              f"{width**4} checked steps, {size} projected binary productions, "
              f"at least {distinguishable} distinct length-{window} windows")
    print(f"{mutations()} local, vertical, frame, and endpoint mutations rejected")
    print(f"{check_morphic_counter(9)} transition rows reproduced by high-bit morphisms")
    print(f"{row_dag_audit()} rows verified with transformed local monitors and endpoint joins")
