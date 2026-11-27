"""Exhaustive finite checks for retirement schedules on a rectangular signal matrix.

Rows are priority ranks, columns are chronological opportunities. A one is an
eligible, within-budget signal. Schedule entries name the stage awarded to a
rank, with None for a rank never awarded.
"""

from itertools import product


def entry(rank, stage, stages):
    return 1 << (rank * stages + stage)


def time_first(matrix, ranks, stages):
    assigned = [None] * ranks
    for stage in range(stages):
        for rank in range(ranks):
            if assigned[rank] is None and matrix & entry(rank, stage, stages):
                assigned[rank] = stage
                break
    return tuple(assigned)


def rank_first(matrix, ranks, stages):
    available = set(range(stages))
    assigned = []
    for rank in range(ranks):
        winner = next(
            (stage for stage in range(stages)
             if stage in available and matrix & entry(rank, stage, stages)),
            None,
        )
        assigned.append(winner)
        if winner is not None:
            available.remove(winner)
    return tuple(assigned)


def truncate_rows(matrix, ranks, stages):
    retained = 0
    for rank in range(ranks):
        signals = [stage for stage in range(stages) if matrix & entry(rank, stage, stages)]
        for stage in signals[:rank + 1]:
            retained |= entry(rank, stage, stages)
    return retained


def schedule_obligations(assigned, stages):
    owners = {stage: rank for rank, stage in enumerate(assigned) if stage is not None}
    required_one = required_zero = 0
    for rank, award in enumerate(assigned):
        if award is not None:
            required_one |= entry(rank, award, stages)
        before_award = stages if award is None else award
        for stage in range(before_award):
            owner = owners.get(stage)
            if owner is None or rank < owner:
                required_zero |= entry(rank, stage, stages)
    return required_one, required_zero


def all_schedules(ranks, stages):
    for assigned in product([None, *range(stages)], repeat=ranks):
        awarded = [t for t in assigned if t is not None]
        if len(awarded) == len(set(awarded)):
            yield assigned


def stage_sign(assigned, stage, colors):
    for rank, award in enumerate(assigned):
        if stage == award:
            return colors[rank]
    return 1


def submasks(mask):
    subset = mask
    while subset:
        yield subset
        subset = (subset - 1) & mask
    yield 0


def check_orders(ranks, stages):
    count = 1 << (ranks * stages)
    for matrix in range(count):
        schedule = time_first(matrix, ranks, stages)
        assert rank_first(matrix, ranks, stages) == schedule
        assert time_first(truncate_rows(matrix, ranks, stages), ranks, stages) == schedule
    return count


def check_partial_matrices(ranks, stages):
    cells = ranks * stages
    full = (1 << cells) - 1
    obligations = {schedule: schedule_obligations(schedule, stages)
                   for schedule in all_schedules(ranks, stages)}
    actual = [time_first(matrix, ranks, stages) for matrix in range(full + 1)]
    cases = 0
    for known in range(full + 1):
        unknown = full ^ known
        for ones in submasks(known):
            zeros = known ^ ones
            by_completion = {actual[ones | rest] for rest in submasks(unknown)}
            by_facts = {schedule for schedule, (need_one, need_zero) in obligations.items()
                        if not (need_one & zeros or need_zero & ones)}
            assert by_completion == by_facts
            cases += 1
    assert cases == 3 ** cells
    return cases


def check_certificates(ranks, stages):
    cells = ranks * stages
    full = (1 << cells) - 1
    obligations = {schedule: schedule_obligations(schedule, stages)
                   for schedule in all_schedules(ranks, stages)}
    schedule_of = [time_first(matrix, ranks, stages) for matrix in range(full + 1)]
    cases = 0
    for colors in product((0, 1), repeat=ranks):
        for stage in range(stages):
            true_sign = [stage_sign(schedule, stage, colors) for schedule in schedule_of]
            for matrix, sign in enumerate(true_sign):
                wrong_tables = [matrix ^ other for other, result in enumerate(true_sign)
                                if result != sign]
                conflicts = [
                    (need_one & (full ^ matrix)) | (need_zero & matrix)
                    for schedule, (need_one, need_zero) in obligations.items()
                    if stage_sign(schedule, stage, colors) != sign
                ]
                for queried in range(full + 1):
                    # Every adversarial completion is excluded exactly when the disclosed
                    # true entries contradict at least one necessity of every wrong schedule.
                    excludes_tables = all(changes & queried for changes in wrong_tables)
                    hits_schedules = all(conflict & queried for conflict in conflicts)
                    assert excludes_tables == hits_schedules
                    cases += 1
    return cases


def check_allowed_columns():
    ranks, stages = 2, 3
    columns = range(1 << ranks)
    options = [tuple(c for c in columns if mask & (1 << c))
               for mask in range(1 << len(columns))]
    checked = 0
    for allowed in product(options, repeat=stages):
        retired = {0}
        last_owners = set()
        for permitted in allowed:
            following = set()
            last_owners = set()
            for old in retired:
                for column in permitted:
                    free_signals = column & ~old
                    winner_bit = free_signals & -free_signals
                    following.add(old | winner_bit)
                    last_owners.add(winner_bit.bit_length() - 1)
            retired = following

        brute_retired, brute_owners = set(), set()
        for table in product(*allowed):
            matrix = sum(entry(r, t, stages) for t, column in enumerate(table)
                         for r in range(ranks) if column & (1 << r))
            schedule = time_first(matrix, ranks, stages)
            brute_retired.add(sum(1 << r for r, at in enumerate(schedule)
                                  if at is not None))
            brute_owners.add(next((r for r, at in enumerate(schedule)
                                   if at == stages - 1), -1))
        assert retired == brute_retired and last_owners == brute_owners
        checked += 1
    return checked


def check_pulses():
    # One immediate observed signal gives zero at the last stage. Any earlier
    # pulse on that row consumes its single award and changes the last sign.
    stages = 9
    final = stages - 1
    matrix = entry(0, final, stages)
    assert stage_sign(time_first(matrix, 1, stages), final, (0,)) == 0
    for earlier in range(final):
        changed = matrix | entry(0, earlier, stages)
        assert stage_sign(time_first(changed, 1, stages), final, (0,)) == 1
    # Removing the final positive matters too. No proper subset of this row
    # certifies the original zero.
    assert stage_sign(time_first(0, 1, stages), final, (0,)) == 1

    # An earlier signal on a competing rank can change whether a *different*
    # rank is selected at the target, without changing the target column.
    competing = matrix | entry(1, final, stages)
    for earlier in range(final):
        changed = competing | entry(0, earlier, stages)
        assert stage_sign(time_first(competing, 2, stages), final, (1, 0)) == 1
        assert stage_sign(time_first(changed, 2, stages), final, (1, 0)) == 0

    # The (rank + 1)-st signal can be essential when all earlier opportunities
    # are occupied by higher priorities.
    rank = 4
    tight = 0
    for earlier in range(rank):
        tight |= entry(earlier, earlier, stages)
    for stage in range(rank + 1):
        tight |= entry(rank, stage, stages)
    assert time_first(tight, rank + 1, stages)[rank] == rank
    assert time_first(tight ^ entry(rank, rank, stages), rank + 1, stages)[rank] is None

    # Once a rank's activation is part of the model, filter eligibility first.
    raw = entry(0, 0, stages) | entry(0, final, stages)
    eligible = entry(0, final, stages)
    assert truncate_rows(raw & eligible, 1, stages) == eligible
    assert truncate_rows(raw, 1, stages) & eligible == 0
    return 2 * final + 2


if __name__ == "__main__":
    orders = sum(check_orders(r, t) for r, t in ((1, 0), (0, 2), (2, 5), (3, 4), (4, 3)))
    partials = check_partial_matrices(3, 3)
    certificates = check_certificates(2, 3)
    columns = check_allowed_columns()
    pulses = check_pulses()
    print(f"{orders} complete signal matrices, {partials} partial matrices, "
          f"{certificates} signed disclosures, {columns} correlated-column charts, "
          f"and {pulses} single-entry pulses checked.")
