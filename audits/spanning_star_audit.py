"""Compare two proposed spanning stars with independently computed optima."""

from itertools import product


def minimum_weight(vertex_count, edges):
    parents = list(range(vertex_count))

    def root(vertex):
        while parents[vertex] != vertex:
            parents[vertex] = parents[parents[vertex]]
            vertex = parents[vertex]
        return vertex

    weight = 0
    kept = 0
    for value, left, right in sorted(edges):
        a, b = root(left), root(right)
        if a != b:
            parents[a] = b
            weight += value
            kept += 1
    assert kept == vertex_count - 1
    return weight


def two_sided_edges(data, address, claim, maximum):
    size = len(data)
    spokes, chords = [], []
    for i, value in enumerate(data):
        spokes.extend([(value, 0, 1 + 2*i), (maximum-value, 0, 2 + 2*i)])
    for j, (index, value) in enumerate(zip(address, claim, strict=True)):
        leaf = 1 + 2*(size+j)
        spokes.extend([(0, 0, leaf), (0, 0, leaf+1)])
        chords.extend([(value, leaf, 1 + 2*index),
                       (maximum-value, leaf+1, 2 + 2*index)])
    return spokes, chords


def single_star_is_minimum(data, address, claim, strict):
    size = len(data)
    edges = [(4*value+2, 0, 1+i) for i, value in enumerate(data)]
    edges.extend((0, 0, 1+size+j) for j in range(size))
    edges.extend((4*value + (1 if tight else 3), 1+size+j, 1+index)
                 for j, (value, tight, index) in enumerate(zip(claim, strict, address, strict=True)))
    ranked = [(weight*(len(edges)+1)+i, left, right)
              for i, (weight, left, right) in enumerate(edges)]
    tree_weight = sum(weight for weight, _, _ in ranked[:2*size])
    return minimum_weight(2*size+1, ranked) == tree_weight


def audit(size, alphabet):
    maximum = alphabet - 1
    checked = 0
    for data in product(range(alphabet), repeat=size):
        witnesses = 0
        for address in product(range(size), repeat=size):
            for claim in product(range(alphabet), repeat=size):
                correct = all(data[i] == v for i, v in zip(address, claim, strict=True))
                spokes, chords = two_sided_edges(data, address, claim, maximum)
                edge_list = spokes + chords
                assert len({(a, b) for _, a, b in edge_list}) == len(edge_list)
                ranges = [[data[i]] for i in range(size)]
                for i, v in zip(address, claim, strict=True):
                    ranges[i].append(v)
                deficit = sum(max(values)-min(values) for values in ranges)
                optimum = minimum_weight(4*size+1, edge_list)
                assert optimum == size*maximum-deficit
                assert correct == (optimum == size*maximum)
                refined = [(v*(len(edge_list)+1)+k, a, b)
                           for k, (v, a, b) in enumerate(edge_list)]
                assert correct == (minimum_weight(4*size+1, refined)
                                   == sum(v for v, _, _ in refined[:len(spokes)]))
                signed = 0
                for strict in product([False, True], repeat=size):
                    if single_star_is_minimum(data, address, claim, strict):
                        signed += (-1)**sum(strict)
                assert signed == int(correct)
                if correct and all(a < b for a, b in zip(claim, claim[1:])):
                    witnesses += 1
                checked += 1
        assert witnesses == int(len(set(data)) == size)
    return checked


if __name__ == '__main__':
    cases = sum(audit(n, alphabet) for n, alphabet in [(1, 3), (2, 4), (3, 2), (3, 3)])
    print(f"Verified {cases:,} indexed tables and claim vectors against Kruskal.")
