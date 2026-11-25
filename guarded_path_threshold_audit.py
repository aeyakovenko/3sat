"""Exhaustive small checks for the guarded path projection and occurrence bound."""

from collections import Counter, defaultdict
from itertools import combinations_with_replacement


def holds(literal, assignment):
    value = bool(assignment & (1 << (abs(literal) - 1)))
    return value == (literal > 0)


def true_clause(clause, assignment):
    return any(holds(literal, assignment) for literal in clause)


def projected_components(clauses, retained):
    """Return (required path mask, retained clause) for each unmarked tree."""
    positions = defaultdict(list)
    for path, clause in enumerate(clauses):
        for literal in clause:
            if abs(literal) not in retained:
                positions[abs(literal)].append((path, literal))
    adjacent = [[] for _ in clauses]
    marked = set()
    for occurrences in positions.values():
        assert len(occurrences) <= 2
        if len(occurrences) == 2 and occurrences[0][1] == -occurrences[1][1]:
            first, second = (entry[0] for entry in occurrences)
            adjacent[first].append(second)
            adjacent[second].append(first)
        else:
            marked.update(path for path, _ in occurrences)
    seen = set()
    result = []
    for root in range(len(clauses)):
        if root in seen:
            continue
        component = []
        stack = [root]
        seen.add(root)
        while stack:
            vertex = stack.pop()
            component.append(vertex)
            for target in adjacent[vertex]:
                if target not in seen:
                    seen.add(target)
                    stack.append(target)
        if marked.intersection(component):
            continue
        if sum(len(adjacent[v]) for v in component) != 2 * (len(component) - 1):
            continue
        boundary = tuple(lit for v in component for lit in clauses[v] if abs(lit) in retained)
        result.append((sum(1 << v for v in component), boundary))
    return result


def families(max_width, max_paths):
    # Normalize order only; retain duplicate literals, tautologies and duplicate paths.
    rows = []
    for width in range(1, max_width + 1):
        rows.extend(combinations_with_replacement((-2, -1, 1, 2), width))
    for count in range(max_paths + 1):
        yield from combinations_with_replacement(rows, count)


def audit_projection():
    checked = 0
    for clauses in families(3, 3):
        counts = Counter(abs(lit) for clause in clauses for lit in clause)
        false_paths = [
            sum(1 << i for i, c in enumerate(clauses) if not true_clause(c, assignment))
            for assignment in range(4)
        ]
        for high_mask in range(4):
            retained = {j + 1 for j in range(2) if high_mask & (1 << j)}
            if any(n > 2 and var not in retained for var, n in counts.items()):
                continue
            components = projected_components(clauses, retained)
            for high in range(4):
                if high & ~high_mask:
                    continue
                failing = [mask for mask, c in components if not true_clause(c, high)]
                extensions = [false_paths[a] for a in range(4) if a & high_mask == high]
                for active in range(1 << len(clauses)):
                    expected = any(not (active & mask) for mask in extensions)
                    projected = all(active & mask != mask for mask in failing)
                    assert projected == expected, (clauses, high, active)
                    checked += 1
    return checked


def audit_physical_edges():
    checked = 0
    for clauses in families(2, 2):
        edges = []
        next_vertex = 2
        path_masks = []
        for i, clause in enumerate(clauses):
            vertices = [0, *range(next_vertex, next_vertex + len(clause) - 1), 1]
            next_vertex += len(clause) - 1
            mask = 0
            for j, lit in enumerate(clause):
                mask |= 1 << len(edges)
                edges.append((vertices[j], vertices[j + 1], -lit, (i + j) % 3))
            path_masks.append(mask)
        for availability in range(1 << len(edges)):
            for threshold in (-1, 0, 1, 2):
                below = sum(1 << i for i, edge in enumerate(edges) if edge[3] <= threshold)
                live = below & availability
                for assignment in range(4):
                    graph = [[] for _ in range(next_vertex)]
                    for i, (u, v, guard, _) in enumerate(edges):
                        if live & (1 << i) and holds(guard, assignment):
                            graph[u].append(v)
                    reachable = {0}
                    stack = [0]
                    while stack:
                        for target in graph[stack.pop()]:
                            if target not in reachable:
                                reachable.add(target)
                                stack.append(target)
                    expected = all(live & mask != mask or true_clause(clause, assignment)
                                   for mask, clause in zip(path_masks, clauses))
                    assert (1 not in reachable) == expected
                    checked += 1
    return checked


def audit_minimum_cost():
    checked = 0
    for clauses in families(2, 2):
        counts = Counter(abs(lit) for clause in clauses for lit in clause)
        path_costs = [min((i + 2 * j + 1) % 4 for j in range(len(clause)))
                      for i, clause in enumerate(clauses)]
        for mask in range(4):
            retained = {j+1 for j in range(2) if mask & (1 << j)}
            if any(n > 2 and v not in retained for v, n in counts.items()):
                continue
            components = projected_components(clauses, retained)
            for high in range(4):
                if high & ~mask:
                    continue
                for active in range(1 << len(clauses)):
                    # Assign all internal path vertices independently with the two terminals pinned.
                    best = float("inf")
                    internals = sum(len(c) - 1 for c in clauses)
                    for assignment in range(4):
                        if assignment & mask != high:
                            continue
                        for internal in range(1 << internals):
                            cost = 0
                            start = 0
                            for i, clause in enumerate(clauses):
                                values = [True, *(bool(internal & (1 << (start+j)))
                                                  for j in range(len(clause)-1)), False]
                                start += len(clause)-1
                                for j, lit in enumerate(clause):
                                    if (active & (1 << i) and holds(-lit, assignment)
                                            and values[j] and not values[j+1]):
                                        cost += (i + 2 * j + 1) % 4
                            best = min(best, cost)
                    projected = sum(min(c for i, c in enumerate(path_costs) if paths & (1 << i))
                                    for paths, clause in components
                                    if active & paths == paths and not true_clause(clause, high))
                    assert best == projected
                    checked += 1
    return checked


def split_variables(clauses):
    copies = defaultdict(list)
    out = []
    count = 0
    for clause in clauses:
        row = []
        for lit in clause:
            count += 1
            copies[abs(lit)].append(count)
            row.append(count if lit > 0 else -count)
        out.append(tuple(row))
    for group in copies.values():
        if len(group) > 1:
            out.extend((-x, y) for x, y in zip(group, group[1:] + group[:1]))
    return out, count


def audit_copy_cycles():
    checked = 0
    for clauses in families(3, 2):
        expanded, count = split_variables(clauses)
        frequency = Counter(abs(lit) for clause in expanded for lit in clause)
        assert max(frequency.values(), default=0) <= 3
        base = any(all(true_clause(c, a) for c in clauses) for a in range(4))
        split = any(all(true_clause(c, a) for c in expanded) for a in range(1 << count))
        assert split == base
        checked += 1
    return checked


def audit_threshold_changes():
    checked = 0
    for r in range(1, 7):
        clauses = []
        weights = []
        next_aux = r + 1
        for banned in range(1 << r):
            wide = [-(i+1) if banned & (1 << i) else i+1 for i in range(r)]
            while len(wide) > 3:
                clauses.append((*wide[:2], next_aux))
                weights.append(banned)
                wide = [-next_aux, *wide[2:]]
                next_aux += 1
            clauses.append(tuple(wide))
            weights.append(banned)
        components = projected_components(clauses, set(range(1, r+1)))
        assert len(components) == 1 << r
        for a in range(1 << r):
            first = min(max(w for i, w in enumerate(weights) if mask & (1 << i))
                        for mask, clause in components if not true_clause(clause, a))
            assert first == a
            checked += 1
    return checked


if __name__ == "__main__":
    print("Two selectors, at most three paths of width up to three:")
    print(f"  {audit_projection()} retained-assignment and active-subset comparisons")
    print("Two selectors, at most two paths of width up to two:")
    print(f"  {audit_physical_edges()} edge-availability, weight and assignment comparisons")
    print(f"  {audit_minimum_cost()} direct minimum edge-cost comparisons")
    print(f"  {audit_copy_cycles()} variable-copy cycle constructions at width up to three")
    print(f"  {audit_threshold_changes()} first-failure checks for one to six retained bits")
