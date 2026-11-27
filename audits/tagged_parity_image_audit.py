"""Check the tagged image parity and the projection from list distinctness."""

from itertools import combinations, permutations, product


def zero_image_by_model_count(tags, payload, target, values):
    """Enumerate original graph models and record each feasible z only once."""
    size = len(tags)
    image = set()
    for assignment in range(1 << (size + values)):
        high = tuple((assignment >> j) & 1 for j in range(size))
        low = tuple((assignment >> (size + v)) & 1 for v in range(values))
        if all(high[j] == low[x] for j, x in zip(tags, payload)):
            image.add(tuple(high[j] ^ low[v] for j, v in enumerate(target)))
    return len(image) % 2


def signed_graph_sat(tags, payload, target, discrepancies, values):
    """Traverse the actual signed graph and detect a conflicting path parity."""
    size = len(tags)
    graph = [[] for _ in range(size + values)]
    edges = [(j, size + x, 0) for j, x in zip(tags, payload)]
    edges.extend((j, size + v, discrepancies[j]) for j, v in enumerate(target))
    for left, right, sign in edges:
        graph[left].append((right, sign))
        graph[right].append((left, sign))
    labels = [None] * len(graph)
    for root, value in enumerate(labels):
        if value is not None:
            continue
        labels[root] = 0
        stack = [root]
        while stack:
            vertex = stack.pop()
            for other, sign in graph[vertex]:
                required = labels[vertex] ^ sign
                if labels[other] is None:
                    labels[other] = required
                    stack.append(other)
                elif labels[other] != required:
                    return False
    return True


def check_tagged_images():
    checked = 0
    for size, values in [(1, 2), (2, 2), (3, 2)]:
        payloads = list(product(range(values), repeat=size))
        signs = list(product(range(2), repeat=size))
        for tags in product(range(size), repeat=size):
            for payload in payloads:
                for target in payloads:
                    expected = len(set(tags)) == size and all(
                        x == target[j] for j, x in zip(tags, payload)
                    )
                    parity = sum(
                        signed_graph_sat(tags, payload, target, z, values)
                        for z in signs
                    ) % 2
                    assert parity == zero_image_by_model_count(tags, payload, target, values)
                    assert parity == expected
                    checked += 1
    return checked


def check_sorted_pairs():
    alphabet = list(product(range(2), repeat=2))
    checked = 0
    for size in [1, 2, 3, 4]:
        target_lists = list(combinations(alphabet, size))
        valid_tags = list(permutations(range(size)))
        for words in product(alphabet, repeat=size):
            coefficient = 0
            for target in target_lists:
                for tags in valid_tags:
                    halves_match = all(
                        words[i][bank] == target[tags[i]][bank]
                        for i in range(size)
                        for bank in range(2)
                    )
                    coefficient += halves_match
            assert coefficient == (len(set(words)) == size)
            checked += 1
    return checked


def check_readout_classification():
    passing = []
    for a, b, c, d in product(range(2), repeat=4):
        table = (a, b, c, d)
        edge = set(table)
        path = {(table[2 * x + y], table[2 * y + z])
                for x, y, z in product(range(2), repeat=3)}
        if a == d and len(edge) % 2 == 0 and len(path) % 2 == 0:
            passing.append(table)
    assert passing == [(0, 1, 1, 0), (1, 0, 0, 1)]


if __name__ == "__main__":
    check_readout_classification()
    tagged = check_tagged_images()
    distinct = check_sorted_pairs()
    print(f"Verified {tagged} tagged parity images and {distinct} sorted-list coefficients.")
