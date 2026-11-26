"""Exhaust time-varying single-parity assertions on the nonlinear register."""


def parity(value):
    return value.bit_count() & 1


def trailing_zeros(value):
    return (value & -value).bit_length() - 1


def register_update(w, left, right, width):
    return ((w << 1) & ((1 << width) - 1)) | (parity(w & left) * parity(w & right))


def one_parity_classes(width):
    states = 1 << width
    universe = (1 << states) - 1
    classes = {(0, 0): universe}
    for normal in range(1, states):
        ones = sum(1 << x for x in range(states) if parity(normal & x))
        classes[normal, 1] = ones
        classes[normal, 0] = universe ^ ones
    return classes


def predecessor_classes(classes, transitions):
    # Build from actual state images; this computation uses no tap algebra.
    parents = {target: [] for target in classes}
    for source, members in classes.items():
        image = 0
        while members:
            low = members & -members
            image |= 1 << transitions[low.bit_length() - 1]
            members ^= low
        for target, allowed in classes.items():
            if not (image & ~allowed):
                parents[target].append(source)
    return parents


def predicted_classes(left, right, steps, endpoint):
    if steps == 0:
        return {(1, endpoint)}
    if endpoint:
        return set()
    shifts = steps - 1
    return {(normal >> shifts, bit)
            for normal, bit in ((left, 0), (right, 0), (left ^ right, 1))
            if shifts <= trailing_zeros(normal)}


def check_shape(width, left, right, exceptional=False):
    assert left.bit_length() == width and right.bit_length() < width
    assert not (left & right) and left.bit_count() >= 2 and right.bit_count() >= 2
    normals = (left, right, left ^ right)
    stripped = [entry >> trailing_zeros(entry) for entry in normals]
    safe = all(entry not in (1, (right << 1) | 1) for entry in stripped)
    assert safe != exceptional
    classes = one_parity_classes(width)
    transitions = [register_update(x, left, right, width) for x in range(1 << width)]
    parents = predecessor_classes(classes, transitions)
    candidates = [{(1, 0)}, {(1, 1)}]
    orbit = list(range(1 << width))
    initial_cases = 0
    actual_endpoints = [0, 0]
    first_mismatch = None
    for steps in range(2 * width + 1):
        for endpoint in (0, 1):
            predicted = predicted_classes(left, right, steps, endpoint)
            if predicted != candidates[endpoint]:
                if not exceptional:
                    raise AssertionError((width, left, right, steps, endpoint,
                                          predicted, candidates[endpoint]))
                if first_mismatch is None:
                    first_mismatch = steps
            covered = 0
            for plane in candidates[endpoint]:
                covered |= classes[plane]
            for seed, actual in enumerate(orbit):
                has_chain = bool((covered >> seed) & 1)
                if has_chain:
                    assert (actual & 1) == endpoint
                if not exceptional:
                    assert has_chain == any(parity(normal & seed) == bit
                                            for normal, bit in predicted)
                initial_cases += 1
        for actual in orbit:
            actual_endpoints[actual & 1] += 1
        candidates = [{source for target in planes for source in parents[target]}
                      for planes in candidates]
        orbit = [transitions[x] for x in orbit]
    assert all(actual_endpoints)
    if exceptional:
        assert first_mismatch is not None
        print(f"D={width}, exceptional taps {left:#x}/{right:#x}: a second "
              f"nonlinear predecessor is visible at horizon {first_mismatch}.")
    else:
        print(f"D={width}, taps {left:#x}/{right:#x}: {len(classes)} classes, "
              f"{initial_cases} seed/horizon/endpoint checks.")
    return initial_cases


if __name__ == "__main__":
    regular = [(5, 0b10001, 0b00110),
               (6, 0b100010, 0b001100),
               (7, 0b1000100, 0b0001010),
               (8, 0b10000010, 0b00011000),
               (9, 0b100001010, 0b000110100)]
    total = sum(check_shape(*shape) for shape in regular)
    check_shape(7, 0b1011000, 0b0000101, exceptional=True)
    print(f"{total} regular seed/horizon/endpoint checks passed.")
