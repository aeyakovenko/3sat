"""Check the digit sweep, its memory sources, and last-write interval certificates."""

from itertools import permutations, product


def build_buckets(values, base):
    width = max(1, (len(values) - 1).bit_length())
    digit_bits = base.bit_length() - 1
    digit_count = (width + digit_bits - 1) // digit_bits
    buckets = [[] for _ in range(base)]
    for i, x in enumerate(values):
        for j in range(digit_count):
            digit = (x >> (j * digit_bits)) & (base - 1)
            item = (i * digit_count + j) * 2
            buckets[digit].append(item)
            buckets[base - digit - 1].append(item + 1)
    return buckets


def sweep(left, right):
    written = set()
    transfers = 0
    masked_transfers = 0
    mismatch_known = False
    for left_items, right_items in zip(left, right, strict=True):
        for item in right_items:
            transfers += item in written
            # Once the decision is known this version reads a private zero.
            if not mismatch_known and item in written:
                masked_transfers += 1
                mismatch_known = True
        written.update(left_items)
    return transfers, masked_transfers


def check_sweep():
    trials = diagonals = 0
    for m in range(2, 6):
        inputs = list(permutations(range(m)))
        for base in (2, 4, 8):
            buckets = [build_buckets(x, base) for x in inputs]
            sizes = tuple(map(len, buckets[0]))
            assert all(tuple(map(len, other)) == sizes for other in buckets)
            for i, left in enumerate(buckets):
                for j, right in enumerate(buckets):
                    transfers, masked = sweep(left, right)
                    assert masked == int(i != j)
                    assert (transfers > 0) == (i != j)
                    # Exactly one directed comparison fires per unequal digit.
                    width = (m - 1).bit_length()
                    bits = base.bit_length() - 1
                    mismatches = sum(
                        ((a ^ b) >> shift) & (base - 1) != 0
                        for a, b in zip(inputs[i], inputs[j])
                        for shift in range(0, width, bits)
                    )
                    assert transfers == mismatches
                    trials += 1
                    diagonals += i == j
    return trials, diagonals


def audit_tree():
    checks = 0
    for q in range(1, 32):
        leaves = 1 << (q - 1).bit_length()
        for start in range(q + 1):
            for end in range(start, q + 1):
                left, right = start + leaves, end + leaves
                nodes = set()
                while left < right:
                    if left % 2:
                        nodes.add(left)
                        left += 1
                    if right % 2:
                        right -= 1
                        nodes.add(right)
                    left //= 2
                    right //= 2
                assert len(nodes) <= 2 * leaves.bit_length()
                for j in range(q):
                    ancestor = leaves + j
                    hits = 0
                    while ancestor:
                        hits += ancestor in nodes
                        ancestor //= 2
                    assert hits == int(start <= j < end)
                    checks += 1
    return checks


def audit_last_writer():
    # Exhaust one address, multiple writes per phase, and every foreign report.
    checks = 0
    for q in range(1, 6):
        phases = tuple(range(1, q + 1)) * 2
        phases = sorted(phases)
        j = q
        # The final slot is the load; all other slots may have written.
        for mask in product((False, True), repeat=len(phases) - 1):
            writes = [p for p, store in zip(phases, mask) if store]
            own = [p for p in writes if p % 2 == j % 2]
            foreign = [p for p in writes if p % 2 != j % 2]
            actual = max(writes, default=0)
            for report in [None, *range(1, j)]:
                if report is None:
                    source = max(own, default=0)
                    locally_valid = True
                else:
                    source = report
                    locally_valid = source in foreign and all(p < source for p in own)
                no_intervening_store = all(not (source < p < j) for p in foreign)
                accepted = locally_valid and no_intervening_store
                appropriate_mode = (report is None) == (actual == 0 or actual % 2 == j % 2)
                assert accepted == (appropriate_mode and source == actual)
                checks += 1
    return checks


if __name__ == "__main__":
    total, diagonals = check_sweep()
    print(f"{total} permutation pairs, including {diagonals} diagonal provenance checks")
    print(f"{audit_tree()} dyadic interval/point checks")
    print(f"{audit_last_writer()} exhaustive local last-writer certificate checks")
