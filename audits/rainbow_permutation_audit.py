"""Audit 3-CNF, undirected rainbow paths, and completed even permutation tables."""
from itertools import combinations, combinations_with_replacement, product
from random import Random


class Graph:
    def __init__(self):
        self.adjacency = []
        self.by_color = []
        self.true_branch_markers = {}

    def vertex(self):
        self.adjacency.append([])
        return len(self.adjacency) - 1

    def color(self):
        self.by_color.append([])
        return len(self.by_color) - 1

    def edge(self, start, end, color):
        self.adjacency[start].append((end, color))
        self.adjacency[end].append((start, color))
        self.by_color[color].append((start, end))

    def subdivide(self, start, end, original_color):
        a, b, c = (self.vertex() for _ in range(3))
        first_link = self.color()
        self.edge(start, a, first_link)
        self.edge(a, b, original_color)
        self.edge(b, c, self.color())
        self.edge(c, end, self.color())
        return first_link


def build(formula):
    graph = Graph()
    source = graph.vertex()
    junction = graph.vertex()
    graph.subdivide(source, junction, graph.color())  # also handles the empty CNF
    occurrences = [[graph.color() for _ in clause] for clause in formula]
    variables = sorted({abs(literal) for clause in formula for literal in clause})
    for variable in variables:
        slots = [(literal, color) for clause, colors in zip(formula, occurrences)
                 for literal, color in zip(clause, colors) if abs(literal) == variable]
        next_junction = graph.vertex()
        for value in (False, True):
            start = junction
            for index, (literal, occurrence_color) in enumerate(slots):
                end = next_junction if index + 1 == len(slots) else graph.vertex()
                false_literal = (literal > 0) != value
                marker = graph.subdivide(start, end, occurrence_color if false_literal else graph.color())
                if value and index == 0:
                    graph.true_branch_markers[variable] = (marker, junction)
                start = end
        junction = next_junction
    for colors in occurrences:
        next_junction = graph.vertex()
        for occurrence_color in colors:
            graph.subdivide(junction, next_junction, occurrence_color)
        junction = next_junction
    assert all(len(graph.by_color[color]) == 2 for colors in occurrences for color in colors)
    for pairs in graph.by_color:
        ends = [v for pair in pairs for v in pair]
        assert len(ends) == len(set(ends)) and 1 <= len(pairs) <= 2
    return graph, source, junction


def rainbow_path(graph, source, sink):
    path = []
    visited = {source}
    colors = set()

    def visit(at):
        if at == sink:
            return tuple(path)
        for target, color in graph.adjacency[at]:
            if target in visited or color in colors:
                continue
            visited.add(target)
            colors.add(color)
            path.append((at, target, color))
            found = visit(target)
            if found is not None:
                return found
            path.pop()
            colors.remove(color)
            visited.remove(target)
        return None

    return visit(source)


def satisfies(formula, assignment):
    return all(any(assignment[abs(lit)] == (lit > 0) for lit in clause) for clause in formula)


def satisfiable(formula):
    variables = sorted({abs(literal) for clause in formula for literal in clause})
    for bits in product((False, True), repeat=len(variables)):
        assignment = dict(zip(variables, bits))
        if satisfies(formula, assignment):
            return True
    return False


def even_permutation(table):
    if sorted(table) != list(range(len(table))):
        return False
    seen = set()
    number_of_cycles = 0
    for i in range(len(table)):
        if i in seen:
            continue
        number_of_cycles += 1
        j = i
        while j not in seen:
            seen.add(j)
            j = table[j]
    return (len(table) - number_of_cycles) % 2 == 0


def check_witness(formula, graph, source, sink, path, rng):
    vertex_count = len(graph.adjacency)
    closing_color = len(graph.by_color)
    tables = graph.by_color + [[(sink, source)]]
    spare = vertex_count + len(tables)
    size = 1 << (spare + 1).bit_length()  # valid addresses through spare + 1
    cycle = path + ((sink, source, closing_color),)
    assert len(path) % 4 == 0 and len(cycle) % 2 == 1
    assert len({a for a, _, _ in cycle}) == len(cycle)
    assert len({color for _, _, color in cycle}) == len(cycle)
    for j, (a, b, color) in enumerate(cycle):
        assert cycle[(j + 1) % len(cycle)][0] == b
        assert (a, b) in tables[color] or (b, a) in tables[color]

    # Build a native memory assignment by disjoint swaps of color-row and tail names.
    base = list(range(size))
    for tail, _, color in cycle:
        row = vertex_count + color
        base[row], base[tail] = base[tail], base[row]
    if len(cycle) % 2:
        base[spare], base[spare + 1] = base[spare + 1], base[spare]

    def check_completion(table):
        memory = [i ^ value for i, value in enumerate(table)]
        first, second = decode_tables(memory, vertex_count, tables)
        assert even_permutation(first) and even_permutation(second)
        closing_row = vertex_count + closing_color
        assert (closing_row ^ memory[closing_row]) == sink and second[closing_row] == source
        active = {(first[row], second[row], row - vertex_count) for row in range(size)
                  if first[row] != second[row]}
        assert active == set(cycle)
        # This extraction has no access to the rainbow path or its clause-branch choices.
        assignment = {var: first[vertex_count + marker] == articulation
                      for var, (marker, articulation) in graph.true_branch_markers.items()}
        assert satisfies(formula, assignment), (formula, assignment)

    check_completion(base)

    # Fix only the required color-row tails, then fill the other rows independently.
    varied = [None] * size
    for tail, _, color in cycle:
        varied[vertex_count + color] = tail
    remaining = sorted(set(range(size)) - {tail for tail, _, _ in cycle})
    rng.shuffle(remaining)
    for row in range(size):
        if varied[row] is None:
            varied[row] = remaining.pop()
    fixed_colors = {color for _, _, color in cycle}
    for color, pairs in enumerate(tables):
        if color in fixed_colors:
            continue
        forbidden = {v for pair in pairs for v in pair}
        row = vertex_count + color
        if varied[row] in forbidden:
            # Vertex rows are unrestricted and there are more of them than forbidden values.
            other = next(i for i in range(vertex_count) if varied[i] not in forbidden)
            varied[row], varied[other] = varied[other], varied[row]
    if not even_permutation(varied):
        varied[spare], varied[spare + 1] = varied[spare + 1], varied[spare]
    assert varied != base
    check_completion(varied)


def decode_tables(memory, vertex_count, tables):
    first = [i ^ value for i, value in enumerate(memory)]
    second = first.copy()
    for color, pairs in enumerate(tables):
        row = vertex_count + color
        swaps = {x: y for a, b in pairs for x, y in ((a, b), (b, a))}
        second[row] = swaps.get(first[row], first[row])
    return first, second


def cases():
    # Up to two unordered 3-clauses on two variables, with full literal multiplicity.
    clauses = list(combinations_with_replacement((-2, -1, 1, 2), 3))
    for length in range(3):
        yield from combinations_with_replacement(clauses, length)
    # All subfamilies of the signed units and padded binary clauses on two variables.
    binary = [(lit, lit, lit) for lit in (-2, -1, 1, 2)]
    binary += [(x, y, y) for x, y in product((-1, 1), (-2, 2))]
    for length in range(3, len(binary) + 1):
        yield from combinations(binary, length)
    # Every sign pattern on three distinct variables, then remove each blocking clause.
    blocked = tuple(tuple(sign * var for var, sign in enumerate(signs, start=1))
                    for signs in product((-1, 1), repeat=3))
    yield blocked
    for removed in range(len(blocked)):
        yield blocked[:removed] + blocked[removed + 1:]
    yield ((3, -1, 3), (-3, 2, 2), (1, -2, -2))


def main():
    positive = negative = 0
    rng = Random(823749)
    for formula in cases():
        expected = satisfiable(formula)
        graph, source, sink = build(formula)
        path = rainbow_path(graph, source, sink)
        assert (path is not None) == expected, formula
        if path is None:
            negative += 1
        else:
            check_witness(formula, graph, source, sink, path, rng)
            positive += 1
    print(f'{positive + negative} formulas, {positive} canonical plus {positive} randomized witnesses, '
          f'{2 * positive} extracted satisfying assignments, '
          f'{negative} unsatisfiable formulas with no rainbow path')


if __name__ == '__main__':
    main()
