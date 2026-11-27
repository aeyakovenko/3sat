"""Compile the packed code predicate to proper DIMACS and check its physical bits."""

import argparse
import subprocess
from dataclasses import dataclass
from itertools import product
from math import isqrt
from random import Random


def record_width(mode, records):
    h = (records + 1).bit_length() - 1
    if mode == 'H':
        return 7 * max(1, h // 112)
    return max(4, h // 16)


def block_syndrome(word):
    syndrome = 0
    for position in range(7):
        if word >> position & 1:
            syndrome ^= position + 1
    return syndrome


def greedy_distance(t):
    log_upper = (t + 1).bit_length()
    return max(3, isqrt(t // log_upper))


def greedy_words(t):
    distance = greedy_distance(t)
    chosen = []
    for word in range(1 << t):
        if all((word ^ other).bit_count() >= distance for other in chosen):
            chosen.append(word)
    return chosen


def accepted_table(mode, t):
    if mode == 'H':
        assert t % 7 == 0
        return {s for s in range(1 << t)
                if all(not block_syndrome(s >> offset) for offset in range(0, t, 7))}
    return set(greedy_words(t))


def clause(a, b, c):
    return f'{a} {b} {c} 0\n'.encode('ascii')


@dataclass
class Layout:
    mode: str
    k: int
    t: int
    digits: int
    prefix: bytes
    flags: list
    good: set

    def encode(self, values):
        assert len(values) == self.k
        return self.prefix + b''.join(clause(self.flags[s], 1, 2) for s in values)

    def digit_bit(self, record, position):
        record_bytes = len(clause(self.flags[0], 1, 2))
        byte_offset = len(self.prefix) + record * record_bytes + self.digits - position // 3
        return byte_offset, position % 3


def layout(mode, k):
    t = record_width(mode, k)
    digits = (t + 2) // 3
    flags = [int('1' + format(s, f'0{digits}o')) for s in range(1 << t)]
    flag_set = set(flags)
    good = accepted_table(mode, t)
    fixed = []
    for anchor in (1, 2):
        for left, right in product((3, -3), (4, -4)):
            fixed.append(clause(-anchor, left, right))
    for s, flag in enumerate(flags):
        fixed.append(clause(flag if s in good else -flag, 1, 2))
    for gap in range(5, flags[-1] + 1):
        if gap not in flag_set:
            fixed.append(clause(-1, gap, 3))
    header = f'c cutcode {mode} {k} {t}\np cnf {flags[-1]} {len(fixed) + k}\n'.encode('ascii')
    return Layout(mode, k, t, digits, header + b''.join(fixed), flags, good)


def dynamic_layout(k, allowed):
    """The leading ASCII 2/3 in each switch pins a flag or its complement."""
    t = record_width('H', k)
    digits = (t + 2) // 3
    suffixes = [format(s, f'0{digits}o') for s in range(1 << t)]
    flags = [int('2' + suffix) for suffix in suffixes]
    negatives = [int('3' + suffix) for suffix in suffixes]
    used = set(flags + negatives)
    fixed = []
    for anchor in (1, 2):
        for a, b in product((3, -3), (4, -4)):
            fixed.append(clause(-anchor, a, b))
    positions = []
    for s, (positive, negative) in enumerate(zip(flags, negatives)):
        fixed.append(clause(positive, negative, 1))
        fixed.append(clause(-positive, -negative, 1))
        positions.append(len(fixed))
        fixed.append(clause(positive if s in allowed else negative, 1, 2))
    fixed.extend(clause(-1, gap, 3) for gap in range(5, negatives[-1] + 1) if gap not in used)
    header = f'c cutcode D {k} {t}\np cnf {negatives[-1]} {len(fixed) + k}\n'.encode('ascii')
    offsets = [len(header)]
    for line in fixed:
        offsets.append(offsets[-1] + len(line))
    return (Layout('D', k, t, digits, header + b''.join(fixed), flags, set(allowed)),
            [offsets[index] for index in positions])


def parse(raw):
    rows = []
    variables = set()
    ceiling = count = None
    for line in raw.splitlines():
        fields = line.split()
        if fields[0] == b'c':
            continue
        if fields[0] == b'p':
            assert fields[1] == b'cnf'
            ceiling, count = map(int, fields[2:])
            continue
        a, b, c, end = map(int, fields)
        names = {abs(a), abs(b), abs(c)}
        assert end == 0 and len(names) == 3 and 0 not in names
        variables.update(names)
        rows.append((a, b, c))
    assert len(rows) == count and variables == set(range(1, ceiling + 1))
    return rows


def dpll(clauses):
    """Generic DPLL on the integers occurring in the physical file."""
    while clauses:
        units = {row[0] for row in clauses if len(row) == 1}
        if not units:
            break
        if any(-lit in units for lit in units):
            return False
        clauses = [tuple(lit for lit in row if -lit not in units)
                   for row in clauses if not any(lit in units for lit in row)]
        if any(not row for row in clauses):
            return False
    if not clauses:
        return True
    pivot = abs(min(clauses, key=len)[0])
    return dpll([(-pivot,), *clauses]) or dpll([(pivot,), *clauses])


def stripe_certifies_conflict(raw, template, rows, forbidden, first, last):
    """Check a contradictory complete body clause using its two local line boundaries."""
    if not raw.startswith(template.prefix):
        return False
    width = len(clause(template.flags[0], 1, 2))
    for position in range(first, last):
        begin = len(template.prefix) + position * width
        if raw[begin:begin + width] not in forbidden:
            continue
        if position == 0:
            return True
        previous = begin - width
        if raw[previous-1:previous] == b'\n' and raw[previous:begin] in rows:
            return True
    return False


def audit_rosters():
    template = layout('H', 7)
    rows = {clause(v, 1, 2) for v in template.flags}
    forbidden = {clause(v, 1, 2) for i, v in enumerate(template.flags) if i not in template.good}
    base = template.encode([0] * template.k)
    cases = 0
    for roster_size in range(1, template.k + 1):
        for i, j in product(range(template.k), range(template.t)):
            raw = bytearray(base)
            offset, bit = template.digit_bit(i, j)
            raw[offset] ^= 1 << bit
            raw = bytes(raw)
            for member in range(roster_size):
                first = member * template.k // roster_size
                last = (member + 1) * template.k // roster_size
                got = stripe_certifies_conflict(raw, template, rows, forbidden, first, last)
                assert got == (first <= i < last)
                cases += 1
    changed = bytearray(template.encode([0, 1, 0, 0, 0, 0, 0]))
    width = len(clause(template.flags[0], 1, 2))
    for offset, replacement in ((0, b'c'), (width-2, b'9'), (width-1, b' ')):
        decoy = changed.copy()
        decoy[len(template.prefix) + offset] = replacement[0]
        assert not stripe_certifies_conflict(bytes(decoy), template, rows, forbidden, 1, 2)
    assert not stripe_certifies_conflict(base, template, rows, forbidden, 0, template.k)
    print(f'{cases} individual stripe verdicts and three damaged preceding-line boundaries checked')


def audit(solver):
    audit_rosters()
    runs = edits = external = 0
    rng = Random(37)
    for mode in ('H', 'G'):
        single = layout(mode, 1)
        for word in range(1 << single.t):
            assert dpll(parse(single.encode([word]))) == (word in single.good)
            runs += 1
        many = layout(mode, 5)
        for _ in range(4):
            values = rng.choices(sorted(many.good), k=many.k)
            base = many.encode(values)
            assert dpll(parse(base))
            runs += 1
            offsets = set()
            for i in range(many.k):
                for j in range(many.t):
                    alternate = values.copy()
                    alternate[i] ^= 1 << j
                    opposite = many.encode(alternate)
                    where, bit = many.digit_bit(i, j)
                    expected = bytearray(base)
                    expected[where] ^= 1 << bit
                    assert opposite == expected
                    assert not dpll(parse(opposite))
                    offsets.add((where, bit))
                    edits += 1
                    runs += 1
            assert len(offsets) == many.k * many.t
            if solver:
                for raw, code in ((base, 10), (opposite, 20)):
                    result = subprocess.run([solver], input=raw, stdout=subprocess.DEVNULL, check=False)
                    assert result.returncode == code
                    external += 1
        for _ in range(20):
            values = [rng.randrange(1 << many.t) for _ in range(many.k)]
            assert dpll(parse(many.encode(values))) == all(s in many.good for s in values)
            runs += 1
    # All 16 allowed Hamming names occur in this positive list. Every
    # currently allowed table bit and every independently editable data bit is pivotal.
    dynamic_code = accepted_table('H', 7)
    table, switches = dynamic_layout(len(dynamic_code), dynamic_code)
    values = sorted(dynamic_code)
    base = table.encode(values)
    assert dpll(parse(base))
    dynamic_edits = 0
    for s in range(1 << table.t):
        neighbor = bytearray(base)
        neighbor[switches[s]] ^= 1
        assert dpll(parse(neighbor)) == (s not in dynamic_code)
        dynamic_edits += 1
    for i, j in product(range(table.k), range(table.t)):
        neighbor = bytearray(base)
        where, bit = table.digit_bit(i, j)
        neighbor[where] ^= 1 << bit
        assert not dpll(parse(neighbor))
        dynamic_edits += 1
    arbitrary = {s for s in range(128) if s % 3}
    other, _ = dynamic_layout(3, arbitrary)
    assert dpll(parse(other.encode([1, 2, 4])))
    assert not dpll(parse(other.encode([1, 2, 3])))
    print(f'{dynamic_edits} single-bit edits on one input with a variable table checked')
    for width in range(4, 12):
        code = greedy_words(width)
        distance = greedy_distance(width)
        assert all((left ^ right).bit_count() >= distance for j, left in enumerate(code) for right in code[:j])
        assert all(any((word ^ center).bit_count() < distance for center in code) for word in range(1 << width))
    print(f'{runs} physical DIMACS decisions; {edits} single-bit SAT/UNSAT neighbors; '
          f'{external} external solver checks; greedy covering checked at widths 4 through 11')


DIRECT_FENCE = b'-1 3 4 0\n'
DIRECT_GUARDS = b''.join(clause(-anchor, a, b) for anchor in (1, 2)
                         for a, b in product((3, -3), (4, -4)))


def direct_slot(suffix, allowed):
    pair = b'-2' + suffix + b' -3' + suffix + b' 1 0\n'
    pinned = (b'2' if allowed else b'3') + suffix + b' 1 2 0\n'
    return DIRECT_FENCE + pair + pinned


def pad_slot(block, stride):
    assert block.endswith(b'\n') and len(block) <= stride
    return block[:-1] + b' ' * (stride - len(block)) + b'\n'


def direct_address(suffix):
    return int.from_bytes(suffix, 'little') & int.from_bytes(b'\x07' * len(suffix), 'little')


def direct_geometry(k):
    t = record_width('G', k)
    digits = (t + 2) // 3
    last = format((1 << t) - 1, f'0{digits}o')
    highest = int('3' + last)
    slots = 1 << (8 * (digits - 1) + 3)
    slot_bytes = len(direct_slot(b'0' * digits, False))
    stride = 1 << (slot_bytes - 1).bit_length()
    rows = 8 + 3 * slots + highest - 4 + 2 * k
    head = f'c direct {k} {t}\np cnf {highest} {rows}\n'.encode() + DIRECT_GUARDS
    record = len(DIRECT_FENCE + b'2' + b'0' * digits + b' 1 2 0\n')
    return t, digits, highest, slots, stride, head, record


def direct_file(values, allowed):
    k = len(values)
    t, digits, highest, slots, stride, head, _ = direct_geometry(k)
    names = [format(s, f'0{digits}o').encode() for s in range(1 << t)]
    blocks = [pad_slot(3 * DIRECT_FENCE, stride)] * slots
    for s, suffix in enumerate(names):
        blocks[direct_address(suffix)] = pad_slot(direct_slot(suffix, s in allowed), stride)
    fillers = b''.join(clause(-1, name, 3) for name in range(5, highest + 1))
    records = b''.join(DIRECT_FENCE + b'2' + names[s] + b' 1 2 0\n' for s in values)
    return head + b''.join(blocks) + fillers + records


def direct_stripe_certifies(raw, member, roster):
    # This is exclusively the early-refutation test. False requests the complete solver.
    newline = raw.find(b'\n', 0, 16 * (1 + len(raw).bit_length()))
    if newline < 0:
        return False
    desc = raw[:newline].split()
    if len(desc) != 4 or desc[:2] != [b'c', b'direct'] or not desc[2].isdigit():
        return False
    k = int(desc[2])
    if not (1 <= k <= len(raw) and 0 <= member < roster <= k):
        return False
    t, digits, _, slots, stride, head, record = direct_geometry(k)
    start = len(raw) - k * record
    if start < len(head) + slots * stride or not raw.startswith(head):
        return False
    for i in range(member * k // roster, (member + 1) * k // roster):
        offset = start + i * record
        begin = offset + len(DIRECT_FENCE) + 1
        suffix = raw[begin:begin + digits]
        if any(c < 48 or c > 55 for c in suffix) or suffix[0] - 48 >= 1 << (t - 3 * (digits - 1)):
            continue
        expected = b'\n' + DIRECT_FENCE + b'2' + suffix + b' 1 2 0\n'
        if raw[offset - 1:offset + record] != expected:
            continue
        table = len(head) + direct_address(suffix) * stride
        negative = pad_slot(direct_slot(suffix, False), stride)
        if raw[table - 1:table + stride] == b'\n' + negative:
            return True
    return False


def audit_direct_table(solver=None):
    k = 5
    t, digits, _, _, stride, head, record = direct_geometry(k)
    keys = range(1 << t)
    # The second table has adjacent allowed keys; every tested verdict still comes from the input.
    tables = [set(greedy_words(t)), {s for s in keys if s % 3 != 1}]
    checks = 0
    for allowed in tables:
        base = [min(allowed)] * k
        for i, value in product(range(k), keys):
            values = base.copy()
            values[i] = value
            raw = direct_file(values, allowed)
            if i == 0:
                assert dpll(parse(raw)) == (value in allowed)
                if solver:
                    run = subprocess.run([solver], input=raw, stdout=subprocess.DEVNULL, check=False)
                    assert run.returncode == (10 if value in allowed else 20)
            for roster in range(1, k + 1):
                for member in range(roster):
                    owner = member * k // roster <= i < (member + 1) * k // roster
                    assert direct_stripe_certifies(raw, member, roster) == (owner and value not in allowed)
                    checks += 1
    forbidden = min(set(keys) - tables[0])
    suffix = format(forbidden, f'0{digits}o').encode()
    raw = direct_file([0, forbidden, 0, 0, 0], tables[0])
    data = len(raw) - (k - 1) * record
    slot = len(head) + direct_address(suffix) * stride
    # Damage the newline before either fence, either fence's zero, the pinned key or one guard.
    for offset in (data - 1, slot - 1, data + len(DIRECT_FENCE) - 2,
                   slot + len(DIRECT_FENCE) - 2, slot + len(DIRECT_FENCE) + 2, len(head) - 3):
        damaged = bytearray(raw)
        damaged[offset] = ord('c')
        assert not direct_stripe_certifies(bytes(damaged), 1, k)
    print(f'{checks} direct-address stripe verdicts, 32 full DPLL decisions and six damaged local checks')


if __name__ == '__main__':
    arg = argparse.ArgumentParser(description=__doc__)
    arg.add_argument('solver', nargs='?', help='optional DIMACS solver accepting stdin and returning 10/20')
    args = arg.parse_args()
    audit_direct_table(args.solver)
    audit(args.solver)
