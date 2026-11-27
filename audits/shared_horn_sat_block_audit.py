"""Finite same-program check of a shared site selector and Horn chart decoder.

Each site receives the same site index y and seven arbitrary decoder bits.
Number the seven obligations cyclically starting at y, so site y itself
tests the terminal prohibition. This makes its read independently executable.
The small machine executes a local Boolean test, records the resulting flag,
then returns or stays quiet. The trace below includes its decoder reads.
SAT queries for a candidate chart of any site compile its test on the fixed
decoder data. This finite model does not time a RAM running its own SAT code.
"""

from dataclasses import dataclass
from functools import lru_cache
from itertools import product

from cnf_width_dictionary_audit import read_dimacs
from dense_model_mask_audit import full_models


START, READ0, READ1, QUIET, RETURN, LEFT, RIGHT = range(1, 8)
SITES = 7
SITE_BITS = (8, 9, 10)


@dataclass(frozen=True)
class Trace:
    reads: tuple
    locations: tuple

    @property
    def returned(self):
        return self.locations[-1] == RETURN


def execute(site, chosen, table):
    """All seven invocations use this code, including the chosen invocation."""
    reads = []

    def read(address):
        value = table[address - 1]
        reads.append((address, value))
        return value

    slot = (site - chosen) % SITES
    if slot == 0:
        flag = not read(RETURN)
    elif slot == 1:
        flag = read(START)
    elif slot == 2:
        # Site y reads RETURN and complements it. Test the implication
        # for that particular read without running any other invocation.
        flag = not read(START) or read(READ0 if read(RETURN) else READ1)
    elif slot == 3:
        flag = not read(READ0) or read(QUIET)
    elif slot == 4:
        flag = not read(READ1) or read(RETURN)
    else:
        flag = not read(LEFT if slot == 5 else RIGHT) or read(QUIET)
    path = (START, READ1, RETURN) if flag else (START, READ0, QUIET)
    return Trace(tuple(reads), path)


def obligations(flag):
    """Possible locations, initialized at start and excluding a final return."""
    return ((-RETURN,), (START,), (-START, READ1 if flag else READ0),
            (-READ0, QUIET), (-READ1, RETURN), (-LEFT, QUIET), (-RIGHT, QUIET))


def satisfies(clauses, bits):
    return all(any(bits[abs(lit) - 1] == (lit > 0) for lit in row) for row in clauses)


def chart_from_run(trace):
    return tuple(i in trace.locations for i in range(1, SITES + 1))


def dimacs(variables, clauses):
    lines = [f"p cnf {variables} {len(clauses)}"]
    lines.extend(" ".join([*map(str, row), "0"]) for row in clauses)
    return ("\n".join(lines) + "\n").encode()


@lru_cache(None)
def models(raw):
    rows = tuple(tuple(map(int, row)) for row in read_dimacs(raw))
    variables = int(raw.splitlines()[0].split()[2])
    return full_models(variables, rows)


def contradiction_for_site(site):
    # On the chosen run, the argument of its branch is NOT the raw RETURN
    # permission. Split the initialization implication into its two cases.
    slots = list((row,) for row in obligations(False))
    slots[2] = ((RETURN, -START, READ1), (-RETURN, -START, READ0))
    return tuple(row for physical in range(SITES)
                 for row in slots[(physical - site) % SITES])


def code_bits(site):
    return tuple(bool(site >> shift & 1) for shift in (2, 1, 0))


def disallow(site):
    return tuple(-var if bit else var for var, bit in zip(SITE_BITS, code_bits(site)))


@lru_cache(None)
def candidate_query(flags, prefix=(), omitted=0):
    # The two short descriptions mark LEFT or RIGHT. This restriction on
    # descriptions is intentionally outside the Horn validity obligations.
    rows = [(LEFT, RIGHT), (-LEFT, -RIGHT), disallow(7)]
    for site, flag in enumerate(flags):
        reject_site = disallow(site)
        rows.extend(reject_site + row for row in obligations(flag))
    rows.extend((var if bit else -var,) for var, bit in zip(SITE_BITS, prefix))
    if omitted:
        rows.append((-omitted,))
    return dimacs(10, rows)


@lru_cache(None)
def truthful_decode(flags):
    assert models(candidate_query(flags))
    prefix = ()
    for _ in SITE_BITS:
        zero_possible = bool(models(candidate_query(flags, prefix + (False,))))
        prefix += (not zero_possible,)
    site = sum(int(bit) << shift for bit, shift in zip(prefix, (2, 1, 0)))
    intersection = tuple(not models(candidate_query(flags, prefix, omitted=i))
                         for i in range(1, SITES + 1))
    return site, intersection


def fixed_point_file():
    # Connect independently encoded execution and SAT decoding through an
    # explicit seven-bit outcome bank. Neither half is a list of rejected
    # (selector, table) pairs. A model would be a consistent fixed point.
    flag_vars = tuple(range(11, 18))
    rows = {disallow(7)}
    tables = tuple(product((False, True), repeat=SITES))
    for site in range(SITES):
        for chosen in range(SITES):
            for table in tables:
                trace = execute(site, chosen, table)
                guard = tuple(-address if bit else address for address, bit in trace.reads)
                flag = flag_vars[site] if trace.returned else -flag_vars[site]
                rows.add(disallow(chosen) + guard + (flag,))
    for flags in tables:
        guard = tuple(-var if bit else var for var, bit in zip(flag_vars, flags))
        if all(flags):
            rows.add(guard)  # No short chart exists from which to decode.
            continue
        chosen, table = truthful_decode(flags)
        for var, bit in zip((*range(1, 8), *SITE_BITS), table + code_bits(chosen)):
            rows.add(guard + (var if bit else -var,))
    return dimacs(17, sorted(rows))


def main():
    bits = tuple(product((False, True), repeat=SITES))
    quiet_total = 0
    updates = {}
    pairs = set()
    for chosen in range(SITES):
        block = contradiction_for_site(chosen)
        assert not models(dimacs(SITES, block))
        for table in bits:
            runs = tuple(execute(z, chosen, table) for z in range(SITES))
            flags = tuple(t.returned for t in runs)
            assert runs[chosen].reads == ((RETURN, table[RETURN - 1]),)
            chart_rows = obligations(runs[chosen].returned)
            for z, trace in enumerate(runs):
                assert all(table[address - 1] == value for address, value in trace.reads)
                assert trace.returned == satisfies((chart_rows[(z - chosen) % SITES],), table)
                exact = chart_from_run(trace)
                assert satisfies(obligations(trace.returned), exact) == (not trace.returned)
            assert satisfies(block, table) == all(flags)
            assert not all(flags)
            quiet_total += flags.count(False)
            site, decoded = truthful_decode(flags)
            pairs.add(flags)
            assert site == flags.index(False)
            target = obligations(flags[site])
            direct = [r for r in bits if satisfies(target, r) and r[LEFT - 1] != r[RIGHT - 1]]
            encoded = {r[:SITES] for r in models(candidate_query(flags, code_bits(site)))}
            assert encoded == set(direct) and len(direct) == 2
            assert all(any(x and not y for x, y in zip(a, b))
                       for a, b in ((direct[0], direct[1]), (direct[1], direct[0])))
            assert decoded == tuple(all(row[i] for row in direct) for i in range(SITES))
            assert decoded == chart_from_run(runs[site]) and satisfies(target, decoded)
            # Moving the non-Horn format clause into validity breaks this step.
            assert all(satisfies(target + ((LEFT, RIGHT),), row) for row in direct)
            assert not satisfies(target + ((LEFT, RIGHT),), decoded)
            updates[chosen, table] = site, decoded
            assert (chosen, table) != (site, decoded)

    # Mutation controls on the all-return file. The core needs terminal
    # exclusion, initialization, the actual read case, and propagation to return.
    core = list(contradiction_for_site(0))
    for missing in ((-RETURN,), (START,), (RETURN, -START, READ1), (-READ1, RETURN)):
        reduced = core.copy()
        reduced.remove(missing)
        assert models(dimacs(SITES, reduced))
    # Independent permission replies let each single-site test pass. If
    # the selector itself varies by site, all can check just initialization.
    assert all(any(execute(z, 0, row).returned for row in bits) for z in range(SITES))
    all_true = (True,) * SITES
    assert all(execute(z, (z - 1) % SITES, all_true).returned for z in range(SITES))
    fixed_file = fixed_point_file()
    assert not models(fixed_file)

    quiet_chart = tuple(i in (START, READ0, QUIET) for i in range(1, SITES + 1))
    for chosen in range(SITES):
        quiet_sites = [z for z in range(SITES) if not execute(z, chosen, quiet_chart).returned]
        assert quiet_sites == [(chosen + 2) % SITES]
        assert updates[chosen, quiet_chart] == (quiet_sites[0], quiet_chart)

    cycles = set()
    for start in updates:
        sequence = []
        seen = {}
        state = start
        while state not in seen:
            seen[state] = len(sequence)
            sequence.append(state)
            state = updates[state]
        cycle = sequence[seen[state]:]
        cycles.add(min(tuple(cycle[i:] + cycle[:i]) for i in range(len(cycle))))
    assert all(len(cycle) > 1 for cycle in cycles)
    print(f"{len(updates)} arbitrary deterministic decoders, {len(updates) * SITES} site runs, "
          f"{quiet_total} quiet site runs")
    print(f"{len(pairs)} distinct outcome patterns; every short-chart intersection matched the actual quiet trace")
    print(f"{SITES} unsatisfiable all-return DIMACS blocks; four necessary-clause deletions made the block SAT")
    print(f"{len(cycles)} truthful-update cycles, lengths {sorted(len(c) for c in cycles)}; no fixed decoder")
    print(f"The combined execution/decoder fixed-point file has 17 variables, "
          f"{len(read_dimacs(fixed_file))} clauses and no model")
    print(f"{models.cache_info().currsize} distinct ordinary DIMACS queries solved")


if __name__ == "__main__":
    main()
