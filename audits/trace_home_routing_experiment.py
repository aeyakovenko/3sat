"""Exhaust the block-summary and home-mark semantics on a small native memory."""

from itertools import product


def direct_run(events):
    memory = [0, 0]
    for address, write, value in events:
        if write:
            memory[address] = value
        elif memory[address] != value:
            return False
    return True


def block_summaries(events):
    groups = {}
    for t, (address, write, value) in enumerate(events):
        key = (t // 2, address)
        if key in groups:
            incoming, previous = groups[key]
            if not write and value != previous:
                return None
        else:
            incoming = None if write else value
        groups[key] = incoming, value
    return groups


def possible_markings(groups, home):
    """Return feasible marked sets with and without the bracketing obligation."""
    if groups is None:
        return False, False
    private = [key for key in groups if key[0] == home[key[1]]]
    remote = {key for key in groups if key[0] != home[key[1]]}
    remote_addresses = {address for _, address in remote}
    exact = relaxed = False
    for flags in product((False, True), repeat=len(private)):
        marked = {key for key, flag in zip(private, flags) if flag}
        if len(marked) > len(remote):
            continue
        left_private = set(private) - marked
        if any(groups[key][0] == 1 for key in left_private):
            continue
        global_memory = [0, 0]
        for key in sorted(remote | marked):
            address = key[1]
            incoming, final = groups[key]
            if incoming is not None and incoming != global_memory[address]:
                break
            global_memory[address] = final
        else:
            relaxed = True
            if all(address not in remote_addresses for _, address in left_private):
                exact = True
    return exact, relaxed


def main():
    words = list(product(range(2), (False, True), range(2)))
    homes = [(0, 1), (1, 1), (2, 0)]
    cases = relaxed_errors = 0
    first_error = None
    for events in product(words, repeat=5):
        actual = direct_run(events)
        groups = block_summaries(events)
        for home in homes:
            exact, relaxed = possible_markings(groups, home)
            cases += 1
            assert exact == actual
            if relaxed and not actual:
                relaxed_errors += 1
                if first_error is None:
                    first_error = (home, events)
    assert first_error is not None
    print(f"Exact RAM verdict in all {cases} trace/home cases")
    print(f"Without the bracketing obligation: {relaxed_errors} false accepts")
    print(f"First false acceptance (home, timed events): {first_error}")


if __name__ == "__main__":
    main()
