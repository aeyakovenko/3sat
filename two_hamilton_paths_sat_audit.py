"""Reduce a simple graph to the identity path and one permuted path for 3-coloring.

The two closing edges may be added: the result is two edge-disjoint Hamilton
cycles. Run this file directly to check the projection and both connector cases.
"""

from dataclasses import dataclass, replace
from itertools import combinations, permutations, product


COLORS = range(3)
RED_BLOCK = (0, 1, 2, 3, 4, 5, 6)
BLUE_BLOCK = (0, 3, 5, 1, 4, 2, 6)


def path_edges(order):
    return zip(order, order[1:])


def cycle_edges(order):
    yield from path_edges(order)
    yield order[-1], order[0]


def proper(edges, coloring):
    return all(coloring[u] != coloring[v] for u, v in edges)


def neutral_colorings():
    """One extension for each ordered pair of prescribed end colors."""
    templates = ((0, 1, 2, 1, 0, 2, 0), (0, 1, 0, 1, 2, 0, 1))
    choices = {}
    edges = list(path_edges(RED_BLOCK)) + list(path_edges(BLUE_BLOCK))
    for template in templates:
        assert proper(edges, template)
        for rename in permutations(COLORS):
            extension = tuple(rename[color] for color in template)
            choices[extension[0], extension[6]] = extension
    assert len(choices) == 9
    return choices


NEUTRAL_COLORINGS = neutral_colorings()


@dataclass
class Encoding:
    red: list
    blue: list
    ports: list
    splitters: list
    first_block: int
    matching: list

    def permutation(self):
        """Relabel the red Hamilton path by 0,1,...,n-1; return the blue path."""
        red_position = [0] * len(self.red)
        for i, vertex in enumerate(self.red):
            red_position[vertex] = i
        return [red_position[vertex] for vertex in self.blue]

    def extend(self, source_colors):
        """Extend a proper source coloring, fixing its value at every incidence."""
        if not source_colors:
            source_colors = (0,)  # The empty input uses one isolated placeholder.
        colors = [-1] * len(self.red)
        for owner, port in enumerate(self.ports):
            colors[port] = source_colors[owner]
        for owner, u, v, data, tail in self.splitters:
            color = source_colors[owner]
            colors[data] = colors[tail] = color
            colors[u], colors[v] = (candidate for candidate in COLORS if candidate != color)

        # Internal paths of each connector block are filled only after its ends.
        start = self.first_block
        external = [[] for _ in colors]
        for order in (self.red, self.blue):
            for a, b in cycle_edges(order):
                if a >= start and b >= start and (a - start) // 7 == (b - start) // 7:
                    continue
                external[a].append(b)
                external[b].append(a)
        for base in range(start, len(colors), 7):
            for end in (base, base + 6):
                assert len(external[end]) == 2
                forbidden = {colors[v] for v in external[end]}
                colors[end] = next(c for c in COLORS if c not in forbidden)
        for base in range(start, len(colors), 7):
            colors[base:base + 7] = NEUTRAL_COLORINGS[colors[base], colors[base + 6]]
        return colors


def encode(vertex_count, edges):
    """Input vertices are 0 through vertex_count-1. Edges are unordered pairs."""
    if vertex_count < 0:
        raise ValueError("negative vertex count")
    incidence = [[] for _ in range(max(1, vertex_count))]
    by_lower = [[] for _ in incidence]
    edge_count = 0
    for a, b in edges:
        if not (0 <= a < vertex_count and 0 <= b < vertex_count) or a == b:
            raise ValueError("expected distinct source vertices in range")
        by_lower[min(a, b)].append(max(a, b))
        incidence[a].append(edge_count)
        incidence[b].append(edge_count)
        edge_count += 1
    last_lower = [-1] * len(incidence)
    for low, neighbors in enumerate(by_lower):
        for high in neighbors:
            if last_lower[high] == low:
                raise ValueError("expected a simple source graph")
            last_lower[high] = low

    red_parts, blue_parts, ports, splitters = [], [], [], []
    data_pairs = [[] for _ in range(edge_count)]
    fresh = 0
    for owner, incident in enumerate(incidence):
        ports.append(fresh)
        red, blue = [fresh], [fresh]
        fresh += 1
        for edge in incident:
            u, v, data, tail = range(fresh, fresh + 4)
            fresh += 4
            red.extend((u, v, tail))
            blue.extend((v, data, u, tail))
            data_pairs[edge].append(data)
            splitters.append((owner, u, v, data, tail))
        red_parts.append(red)
        blue_parts.append(blue)
    red_parts.extend(data_pairs)

    # Two seven-vertex blocks A,B in every red gap. In blue they occur B,A.
    first_block = fresh
    red, blue = [], []
    for i, part in enumerate(red_parts):
        red.extend(part)
        a = first_block + 14 * i
        for base in (a, a + 7):
            red.extend(base + j for j in RED_BLOCK)
    for i, part in enumerate(blue_parts):
        blue.extend(part)
        stop = len(red_parts) if i == len(blue_parts) - 1 else i + 1
        for gap in range(i, stop):
            a = first_block + 14 * gap
            for base in (a + 7, a):
                blue.extend(base + j for j in BLUE_BLOCK)
    return Encoding(red, blue, ports, splitters, first_block, data_pairs)


def switchable_edges(vertex_count, edges):
    """Return the base encoding and the two blue-array positions for each edge."""
    edges = list(edges)
    count = len(edges)
    private = [(vertex_count + 2*i, vertex_count + 2*i + 1) for i in range(count)]
    encoding = encode(vertex_count + 2 * count, edges + private)
    blue_position = [0] * len(encoding.blue)
    for i, vertex in enumerate(encoding.blue):
        blue_position[vertex] = i

    # The second matching endpoint comes from the larger-numbered source vertex.
    # Edge e and private edge count+e have no other data terminals in common.
    switches = [(blue_position[encoding.matching[i][1]],
                 blue_position[encoding.matching[count + i][1]]) for i in range(count)]
    return encoding, switches


def switched_order(order, switches, disabled):
    """Disable the listed edge indices by exchanging their disjoint entries."""
    result = list(order)
    for i in disabled:
        a, b = switches[i]
        result[a], result[b] = result[b], result[a]
    return result


def wheel_switch_audit():
    checks = 0
    for rim in (3, 5):
        edges = [(i, (i + 1) % rim) for i in range(rim)] + [(i, rim) for i in range(rim)]
        size, count = rim + 1, len(edges)
        base, switches = switchable_edges(size, edges)
        q = len(base.red)
        assert q == 163 * rim + 15
        assert len({position for pair in switches for position in pair}) == 2 * count
        base_pi = base.permutation()
        masks = range(1 << count) if rim == 3 else [0] + [1 << i for i in range(count)]
        for mask in masks:
            disabled = {i for i in range(count) if (mask >> i) & 1}
            pi = switched_order(base_pi, switches, disabled)
            blue = switched_order(base.blue, switches, disabled)
            positions = {j for i in disabled for j in switches[i]}
            assert positions == {j for j in range(q) if pi[j] != base_pi[j]}
            assert all((b - a) % q not in (1, q - 1) for a, b in cycle_edges(pi))

            # Recover which source owner is actually forced at every matching
            # endpoint from the modified blue slots and their flanking centers.
            new_at = dict(zip(base.blue, blue))
            splitters = [(owner, u, v, new_at[data], tail)
                         for owner, u, v, data, tail in base.splitters]
            owners = {data: owner for owner, _, _, data, _ in splitters}
            for i, (a, b) in enumerate(edges):
                a, b = min(a, b), max(a, b)
                shadow_a, shadow_b = size + 2*i, size + 2*i + 1
                expected = ((a, shadow_b), (shadow_a, b)) if i in disabled else (
                    (a, b), (shadow_a, shadow_b))
                actual = tuple(tuple(owners[x] for x in base.matching[j])
                               for j in (i, count + i))
                assert actual == expected

            retained = [edge for i, edge in enumerate(edges) if i not in disabled]
            witness = next((colors for colors in product(COLORS, repeat=size)
                            if proper(retained, colors)), None)
            assert (witness is not None) == bool(disabled)
            if witness is not None:
                colors = list(witness)
                for i, (a, b) in enumerate(edges):
                    if i in disabled:
                        colors.extend((next(c for c in COLORS if c != witness[max(a,b)]),
                                       next(c for c in COLORS if c != witness[min(a,b)])))
                    else:
                        colors.extend((0, 1))
                instance = replace(base, blue=blue, splitters=splitters)
                target = instance.extend(colors)
                assert instance.permutation() == pi
                assert proper(cycle_edges(base.red), target) and proper(cycle_edges(blue), target)
            checks += 1
    return checks


def audit():
    # Independently exhaust the splitter projection (a,b,data are its terminals).
    edges = list(path_edges((0, 1, 2, 4))) + list(path_edges((0, 2, 3, 1, 4)))
    terminal_rows = {(a, b, c) for a, u, v, c, b in product(COLORS, repeat=5)
                     if proper(edges, (a, u, v, c, b))}
    assert terminal_rows == {(color, color, color) for color in COLORS}

    graphs = extensions = 0
    for size in range(5):
        all_edges = list(combinations(range(size), 2))
        for mask in range(1 << len(all_edges)):
            edges = [e for i, e in enumerate(all_edges) if (mask >> i) & 1]
            encoding = encode(size, edges)
            pi = encoding.permutation()
            n = len(pi)
            assert n == 15 * max(1, size) + 22 * len(edges)
            assert sorted(pi) == list(range(n))
            assert all((b - a) % n not in (1, n - 1) for a, b in cycle_edges(pi))
            # The two deleted closing edges are connector edges.
            assert encoding.red[-1] >= encoding.first_block
            assert encoding.blue[-1] >= encoding.first_block
            for source in product(COLORS, repeat=size):
                if proper(edges, source):
                    colors = encoding.extend(source)
                    assert proper(cycle_edges(encoding.red), colors)
                    assert proper(cycle_edges(encoding.blue), colors)
                    assert tuple(colors[p] for p in encoding.ports[:size]) == source
                    extensions += 1
            graphs += 1
    return graphs, extensions


if __name__ == "__main__":
    graphs, extensions = audit()
    print(f"{graphs} labeled source graphs; {extensions} projected colorings extended.")
    print(f"{wheel_switch_audit()} wheel masks checked against their exact matching endpoints.")
    print("All splitter tuples and all nine ordered connector endpoint pairs verified.")
