"""Count the four-cube configurations for an exact literal-witness OR gadget."""

from functools import lru_cache
from itertools import combinations, product


# Ports 1,2,3. Auxiliaries 4,5,6,7 are s,x,y,z.
GADGET = (
    (1, 4, 5), (2, 4, 6), (3, 4, 7),
    (5, 6, 7), (-5, 6, 7), (5, -6, 7), (5, 6, -7),
    (-5, -6, -7), (-4, -5, -6), (-4, -5, -7), (-4, -6, -7),
)


def check_gadget():
    assert all(len({abs(lit) for lit in row}) == 3 for row in GADGET)
    assert [lit for row in GADGET for lit in row if abs(lit) <= 3] == [1, 2, 3]
    counts = []
    private = [0]*len(GADGET)
    for ports in range(8):
        models = 0
        for aux in range(16):
            assignment = ports | (aux << 3)
            rejects = [i for i, row in enumerate(GADGET)
                       if all(bool(assignment & (1 << (abs(lit)-1))) != (lit > 0)
                              for lit in row)]
            models += not rejects
            if not ports and len(rejects) == 1:
                private[rejects[0]] += 1
        counts.append(models)
    assert counts == [ports.bit_count() for ports in range(8)]
    assert private == [1]*len(GADGET)
    # Forbid all three-variable assignments except 111.
    extension_counts = [counts[7 ^ blocked] for blocked in range(7)]
    extensions = 1
    for value in extension_counts:
        extensions *= value
    assert sorted(extension_counts) == [1, 1, 1, 2, 2, 2, 3] and extensions == 24
    print(f"Boundary extension counts {counts}; zero-boundary deletion counts {private}")
    print(f"Single-solution seven-clause block has {extensions} extensions")


POINTS = tuple(range(16))
FULL = (1 << 16)-1


def bits(points):
    return sum(1 << v for v in points)


def cube_faces():
    faces = []
    for i, j in combinations(range(4), 2):
        coordinates = (1 << i) | (1 << j)
        for pattern in (0, 1 << i, 1 << j, coordinates):
            faces.append(bits(v for v in POINTS if (v & coordinates) == pattern))
    assert len(set(faces)) == 24
    return faces


@lru_cache(maxsize=None)
def perfect_matchings(remaining):
    """Always pair the first remaining vertex to avoid counting reorderings."""
    if not remaining:
        return ((),)
    x = (remaining & -remaining).bit_length()-1
    result = []
    for direction in range(4):
        y = x ^ (1 << direction)
        if remaining & (1 << y):
            edge = (1 << x) | (1 << y)
            for tail in perfect_matchings(remaining ^ edge):
                result.append((edge,)+tail)
    return tuple(result)


def seven_row_census():
    faces = cube_faces()
    mark_triples = face_choices = edge_covers = pairs = private = 0
    for marked in combinations(POINTS, 3):
        mark_triples += 1
        marks = bits(marked)
        # Each selected face meets the three models exactly in its own marker.
        choices = [[f for f in faces if (f & marks) == 1 << v] for v in marked]
        unions = [f | g | h for f, g, h in product(*choices)]
        face_choices += len(unions)

        # A seven-edge cover of the other thirteen vertices has one vertex
        # of degree two. Its two neighbors have degree one. The rest is matched.
        for center in POINTS:
            if center in marked:
                continue
            neighbors = [center ^ (1 << i) for i in range(4)]
            for left, right in combinations((v for v in neighbors if v not in marked), 2):
                leaves = (1 << left) | (1 << right)
                remaining = FULL ^ (marks | leaves | (1 << center))
                for matching in perfect_matchings(remaining):
                    edge_covers += 1
                    pairs += len(unions)
                    for union in unions:
                        # A boundary-zero private witness for a path edge must
                        # be its leaf. For a matching edge either endpoint works.
                        if not (union & leaves) and all((union & e) != e for e in matching):
                            private += 1
    assert (mark_triples, face_choices, edge_covers, pairs, private) == (
        560, 33376, 67200, 3086208, 0)
    print(f"Marked triples {mark_triples}; compatible face choices {face_choices}")
    print(f"Seven-edge covers {edge_covers}; pairs checked {pairs}; all rows private {private}")


if __name__ == "__main__":
    check_gadget()
    seven_row_census()
