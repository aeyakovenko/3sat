"""Exhaust the small instances from one-pass-sat-with-one-nonzero-work-read.md."""

from itertools import product
from math import lcm, prod
from random import Random


def equation(source, target, complement):
    image = -source if complement else source
    return [(-image, target), (image, -target)]


def binary_banks(left, right):
    assert len(left) == len(right)
    layers = 4 * len(left)
    anchor = 2 * (layers + 1) + 1
    helper = anchor + 1
    start = [(-anchor, -helper), (-anchor, helper), (anchor, -helper)]
    start += [(-1, anchor), (-2, anchor), (2 * layers + 1, anchor)]
    end = []

    for layer in range(layers):
        index, stage = divmod(layer, 4)
        swap = stage % 2 == 0
        bank = start if swap else end
        for lane in range(2):
            source_lane = lane ^ (left[index] if swap else 0)
            source = 2 * layer + source_lane + 1
            target = 2 * (layer + 1) + lane + 1
            flip = not swap and lane == 0 and right[index]
            bank.extend(equation(source, target, flip))

    return helper, start, end


def ternary_banks(last, left, right):
    anchors = (last + 1, last + 2, last + 3)
    guards = [tuple(-var if bit else var for var, bit in zip(anchors, bits))
              for bits in product((0, 1), repeat=3) if any(bits)]
    return (last + 3, guards + [clause + (anchors[0],) for clause in left],
            [clause + (anchors[0],) for clause in right])


def dimacs(records):
    return "".join(" ".join(map(str, clause)) + " 0\n" for clause in records)


def model_count(clauses, remaining):
    """Generic branch-and-propagate counter, independent of the wire construction."""
    while clauses:
        if any(not clause for clause in clauses):
            return 0
        unit = next((clause[0] for clause in clauses if len(clause) == 1), None)
        if unit is None:
            variable = abs(clauses[0][0])
            return sum(model_count(clauses + [(lit,)], remaining)
                       for lit in (variable, -variable))
        clauses = [tuple(lit for lit in clause if lit != -unit)
                   for clause in clauses if unit not in clause]
        remaining -= 1
    return 1 << remaining


def check_formulas():
    checked = 0
    for width in range(1, 5):
        controls = list(product((0, 1), repeat=width))
        for ternary in (False, True):
            prefixes, suffixes = {}, {}
            lengths = set()
            for x, y in product(controls, repeat=2):
                last, left, right = binary_banks(x, y)
                if ternary:
                    last, left, right = ternary_banks(last, left, right)
                clauses = left + right
                assert {abs(lit) for c in clauses for lit in c} == set(range(1, last + 1))
                assert all(len(set(map(abs, c))) == 2 + int(ternary) for c in clauses)
                assert model_count(clauses, last) == sum(a * b for a, b in zip(x, y)) % 2
                # Each bank must depend only on its public controls, including byte lengths.
                prefix = f"p cnf {last} {len(clauses)}\n" + dimacs(left)
                suffix = dimacs(right)
                assert prefixes.setdefault(x, prefix) == prefix
                assert suffixes.setdefault(y, suffix) == suffix
                lengths.add((len(prefix), len(suffix)))
                checked += 1
            assert len(lengths) == 1
    return checked


def occurrence_verifier(clauses, value_bits, modulus):
    marks = set()
    values = iter(value_bits)
    for clause in clauses:
        satisfied = False
        for lit in clause:
            label = abs(lit) % modulus if modulus else abs(lit)
            value = next(values)
            if (label, 1 - value) in marks:
                return False, 1
            marks.add((label, value))
            satisfied |= value == int(lit > 0)
        if not satisfied:
            return False, 0
    return True, 0


def check_work_reads():
    candidates = [(), (1,), (-1,), (3,), (-3,), (-1, 3), (1, -3), (3, 3)]
    path_count = 0
    rejected_hits = 0
    for size in range(3):
        for clauses in product(candidates, repeat=size):
            labels = sorted({abs(lit) for clause in clauses for lit in clause})
            for modulus in (0, 2, 3, 5):
                images = {name: name % modulus if modulus else name for name in labels}
                distinct = sorted(set(images.values()))
                expected = 0
                for assignment in product((0, 1), repeat=len(distinct)):
                    values = dict(zip(distinct, assignment))
                    expected += all(any(values[images[abs(lit)]] == (lit > 0) for lit in clause)
                                    for clause in clauses)
                accepts = 0
                for bits in product((0, 1), repeat=sum(map(len, clauses))):
                    result, hits = occurrence_verifier(clauses, bits, modulus)
                    assert hits <= 1 and (not result or hits == 0)
                    path_count += 1
                    rejected_hits += hits
                    # Full occurrence strings uniquely represent accepting paths.
                    # Some short rejecting paths can have several extensions.
                    accepts += result
                assert accepts == expected
    assert rejected_hits > 0
    return path_count


def check_small_moduli():
    examples = [
        [3, 9, 15, 21], [1, 1 + lcm(*range(2, 23))],
        [2**110 + 19, 3**98 + 6, 5**224 + 21], [10**700, 10**700 + 1], [],
    ]
    for names in examples:
        size = max(1, 8 * sum(len(str(name)) for name in names))
        pair_product = prod(abs(x - y) for i, x in enumerate(names) for y in names[:i])
        modulus = next(d for d in range(2, 16 * (size + 1)**2 + 1)
                       if pair_product % d)
        assert len({x % modulus for x in names}) == len(names)
        for name in names:
            remainder = 0
            for digit in "000" + str(name):
                value = 10 * remainder + int(digit)
                subtractions, remainder = divmod(value, modulus)
                assert subtractions <= 9
            assert remainder == name % modulus
    return len(examples)


def check_replay():
    """Vary store/read addresses with the actual accumulator to exercise replay."""
    rng = Random(515)
    discovered_cases = 0
    repeats = 0
    for _ in range(2000):
        program = [(rng.randrange(2), rng.randrange(4), rng.randrange(4))
                   for _ in range(28)]
        full, known = {}, {}
        native = simulated = 0
        genuine = set()
        for step, (writing, offset, payload) in enumerate(program):
            address = (offset + native) % 4
            assert address == (offset + simulated) % 4
            if writing:
                full[address] = (native + payload) % 4
                if address in known:
                    known[address] = (simulated + payload) % 4
                continue
            actual = full.get(address, 0)
            if actual:
                repeats += address in genuine
                genuine.add(address)
            if address in known:
                reply = known[address]
            else:
                # Known values must be reset to zero for each past-prefix replay.
                earlier = dict.fromkeys(known, 0)
                earlier_controller = reply = 0
                for past_store, past_offset, past_payload in program[:step]:
                    past_address = (earlier_controller + past_offset) % 4
                    if past_store:
                        value = (earlier_controller + past_payload) % 4
                        if past_address == address:
                            reply = value
                        if past_address in earlier:
                            earlier[past_address] = value
                    else:
                        old_reply = earlier.get(past_address, 0)
                        earlier_controller = (old_reply + past_payload) % 4
                assert earlier_controller == native
                if reply:
                    known[address] = reply
            assert actual == reply and set(known) == genuine
            native = (actual + payload) % 4
            simulated = (reply + payload) % 4
        discovered_cases += bool(genuine)
    assert discovered_cases and repeats
    return 2000


if __name__ == "__main__":
    formulas = check_formulas()
    paths = check_work_reads()
    moduli = check_small_moduli()
    programs = check_replay()
    print(f"{formulas} binary/ternary files, {paths} occurrence strings, "
          f"{moduli} modulus cases, {programs} adaptive-address replays")
