"""Check the packing formula and the filters that attain it on short streams."""

from itertools import product


def pairings(positions):
    if not positions:
        yield ()
        return
    first, *rest = positions
    for index, second in enumerate(rest):
        for others in pairings(rest[:index] + rest[index + 1 :]):
            yield ((first, second),) + others


def live_masks(pairs):
    return [
        sum(1 << j for j, (first, last) in enumerate(pairs) if first <= cut < last)
        for cut in range(2 * len(pairs) - 1)
    ]


def optimal_packing(live, capacities, width):
    feasible = (
        subset
        for subset in range(1 << width)
        if all((subset & mask).bit_count() <= cap for mask, cap in zip(live, capacities))
    )
    return max(feasible, key=int.bit_count)


def minimum_cut_cost(live, capacities, width):
    # Enumerate cut choices, retaining the least charge for each union of hit intervals.
    profiles = {0: 0}
    for mask, cap in zip(live, capacities):
        next_profiles = profiles.copy()
        for hit, cost in profiles.items():
            combined = hit | mask
            new_cost = cost + cap
            if combined not in next_profiles or new_cost < next_profiles[combined]:
                next_profiles[combined] = new_cost
        profiles = next_profiles
    return min(cost + width - hit.bit_count() for hit, cost in profiles.items())


def check_menu(pairs, packed):
    fixed = [j for j in range(len(pairs)) if not (packed >> j) & 1]
    menus = [dict(zip(fixed, bits)) for bits in product(range(2), repeat=len(fixed))]
    positions = sorted((position, j) for j, pair in enumerate(pairs) for position in pair)
    counts = [0] * len(menus)
    for data in product(range(2), repeat=len(positions)):
        consistent = all(data[first] == data[last] for first, last in pairs)
        passed = 0
        for i, pins in enumerate(menus):
            memory = {}
            for (position, j), bit in zip(positions, data):
                if j in pins:
                    if bit != pins[j]:
                        break
                elif position == pairs[j][0]:
                    memory[j] = bit
                elif memory.pop(j) != bit:
                    break
            else:
                assert not memory
                counts[i] += 1
                passed += 1
        assert passed == int(consistent)
    assert all(count == 1 << packed.bit_count() for count in counts)


def main():
    layouts = profiles = menus = 0
    for width in range(1, 6):
        for pairs in pairings(list(range(2 * width))):
            layouts += 1
            live = live_masks(pairs)
            capacities = {tuple([s] * len(live)) for s in range(width + 1)}
            capacities.update(
                tuple((cut + offset) % (width + 1) for cut in range(len(live)))
                for offset in range(width + 1)
            )
            for caps in capacities:
                packed = optimal_packing(live, caps, width)
                assert packed.bit_count() == minimum_cut_cost(live, caps, width)
                profiles += 1
                if width <= 3:
                    check_menu(pairs, packed)
                    menus += 1
    print(f"{layouts} layouts, {profiles} capacity profiles, {menus} full menu checks")


if __name__ == "__main__":
    main()
