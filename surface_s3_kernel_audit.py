"""Compile low-occurrence S3 equations and check the parametric surface test."""

from collections import Counter, defaultdict
from dataclasses import dataclass
from functools import cache
from itertools import permutations, product


GROUP = tuple(permutations(range(3)))
ELEMENTS = range(len(GROUP))
ONE = 0
MUL = tuple(tuple(GROUP.index(tuple(a[j] for j in b)) for b in GROUP) for a in GROUP)
INV = tuple(next(b for b in ELEMENTS if MUL[a][b] == ONE) for a in ELEMENTS)


def multiply(elements):
    result = ONE
    for element in elements:
        result = MUL[result][element]
    return result


def signed(element, sign):
    return element if sign == 1 else INV[element]


@cache
def conjugates(element):
    return frozenset(multiply((x, element, INV[x])) for x in ELEMENTS)


@cache
def set_product(left, right):
    return frozenset(MUL[x][y] for x in left for y in right)


IDENTITY_SET = frozenset({ONE})
COMMUTATORS = frozenset(multiply((x, y, INV[x], INV[y])) for x, y in product(ELEMENTS, repeat=2))
SQUARES = frozenset(MUL[x][x] for x in ELEMENTS)


@dataclass(frozen=True)
class Var:
    name: int
    sign: int = 1


# In an equation, a plain int is a fixed group element.
@dataclass(frozen=True)
class Piece:
    variable: Var
    following_constant: int


@dataclass(frozen=True)
class Component:
    static_product: frozenset
    boundaries: tuple


@dataclass(frozen=True)
class Kernel:
    static_ok: bool
    components: tuple

    def accepts(self, assignment):
        if not self.static_ok:
            return False
        for component in self.components:
            possible = component.static_product
            for boundary in component.boundaries:
                value = ONE
                for piece in boundary:
                    var = piece.variable
                    value = MUL[value][signed(assignment[var.name], var.sign)]
                    value = MUL[value][piece.following_constant]
                possible = set_product(possible, conjugates(value))
            if ONE not in possible:
                return False
        return True

    def sizes(self):
        boundaries = [b for c in self.components for b in c.boundaries]
        return len(self.components), len(boundaries), sum(map(len, boundaries))


def components(neighbors):
    label = [-1] * len(neighbors)
    groups = []
    for start in range(len(neighbors)):
        if label[start] != -1:
            continue
        label[start] = len(groups)
        group = [start]
        for node in group:
            for other in neighbors[node]:
                if label[other] == -1:
                    label[other] = label[start]
                    group.append(other)
        groups.append(group)
    return label, groups


def face_orientations(start, dual):
    orientation = {start: 1}
    faces = [start]
    orientable = True
    for face in faces:
        for other, transport in dual[face]:
            required = orientation[face] * transport
            if other not in orientation:
                orientation[other] = required
                faces.append(other)
            elif orientation[other] != required:
                orientable = False
    return faces, orientation, orientable


def compress_boundary(word):
    """Return a constant product or a cyclic list of variable-times-constant pieces."""
    start = next((i for i, term in enumerate(word) if isinstance(term, Var)), None)
    if start is None:
        return multiply(word)
    pieces = []
    variable = word[start]
    after = ONE
    for term in word[start + 1:] + word[:start]:
        if isinstance(term, Var):
            pieces.append(Piece(variable, after))
            variable, after = term, ONE
        else:
            after = MUL[after][term]
    pieces.append(Piece(variable, after))
    return tuple(pieces)


def compile_kernel(equations, exposed=()):
    """Keep exposed names and names used at least three times as parameters."""
    exposed = frozenset(exposed)
    words = [list(word) + [ONE] for word in equations]
    side_terms, owner, successor, face_sides = [], [], [], []
    occurrences = defaultdict(list)
    for face, word in enumerate(words):
        first = len(side_terms)
        sides = list(range(first, first + len(word)))
        face_sides.append(sides)
        for i, (side, term) in enumerate(zip(sides, word)):
            owner.append(face)
            side_terms.append(term)
            successor.append(sides[(i + 1) % len(sides)])
            if isinstance(term, Var):
                assert term.sign in (-1, 1)
                occurrences[term.name].append(side)

    dual = [[] for _ in words]
    corner_links = [[] for _ in side_terms]
    paired = set()
    free_faces = set()
    for name, sides in occurrences.items():
        if name in exposed:
            continue
        if len(sides) == 1:
            free_faces.add(owner[sides[0]])
        if len(sides) != 2:
            continue
        a, b = sides
        paired.update(sides)
        opposite = side_terms[a].sign != side_terms[b].sign
        transport = 1 if opposite else -1
        dual[owner[a]].append((owner[b], transport))
        dual[owner[b]].append((owner[a], transport))
        ends = (successor[b], b) if opposite else (b, successor[b])
        for u, v in zip((a, successor[a]), ends):
            corner_links[u].append(v)
            corner_links[v].append(u)

    vertex, vertices = components(corner_links)
    boundary_at = [[] for _ in vertices]
    for side in range(len(side_terms)):
        if side not in paired:
            boundary_at[vertex[side]].append((side, 1))
            boundary_at[vertex[successor[side]]].append((side, -1))

    compiled = []
    static_ok = True
    seen_faces, seen_sides = set(), set()
    for start in range(len(words)):
        if start in seen_faces:
            continue
        faces, orientation, orientable = face_orientations(start, dual)
        seen_faces.update(faces)
        if not free_faces.isdisjoint(faces):
            continue  # A singleton and a tree of internal variables solve this component.
        sides = [s for face in faces for s in face_sides[face]]
        n_vertices = len({vertex[s] for s in sides})
        n_edges = len(sides) - sum(s in paired for s in sides) // 2
        boundary_count = 0
        static_product = IDENTITY_SET
        variable_boundaries = []
        for side in sides:
            if side in paired or side in seen_sides:
                continue
            boundary_count += 1
            s, direction = side, orientation[owner[side]] if orientable else 1
            walk = []
            while True:
                assert s not in seen_sides
                seen_sides.add(s)
                term = side_terms[s]
                if isinstance(term, Var):
                    walk.append(Var(term.name, direction * term.sign))
                else:
                    walk.append(signed(term, direction))
                endpoint = vertex[successor[s] if direction == 1 else s]
                step = next(((e, d) for e, d in boundary_at[endpoint] if e not in seen_sides), None)
                if step is None:
                    break
                s, direction = step
                assert not orientable or direction == orientation[owner[s]]
            compressed = compress_boundary(walk)
            if isinstance(compressed, int):
                static_product = set_product(static_product, conjugates(compressed))
            else:
                variable_boundaries.append(compressed)

        defect = 2 - boundary_count - (n_vertices - n_edges + len(faces))
        assert defect >= 0 and (not orientable or defect % 2 == 0)
        factors = defect // 2 if orientable else defect
        for _ in range(factors):
            static_product = set_product(static_product, COMMUTATORS if orientable else SQUARES)
        if variable_boundaries:
            compiled.append(Component(static_product, tuple(variable_boundaries)))
        else:
            static_ok = static_ok and ONE in static_product
    return Kernel(static_ok, tuple(compiled))


def evaluate(word, assignment):
    return multiply(signed(assignment[t.name], t.sign) if isinstance(t, Var) else t for t in word)


def check_every_parameter(equations):
    uses = Counter(t.name for w in equations for t in w if isinstance(t, Var))
    names = tuple(uses)
    params = tuple(v for v in names if uses[v] >= 3)
    possible = set()
    for values in product(ELEMENTS, repeat=len(names)):
        assigned = dict(zip(names, values))
        if all(evaluate(word, assigned) == ONE for word in equations):
            possible.add(tuple(assigned[v] for v in params))
    kernel = compile_kernel(equations)
    nc, nb, np = kernel.sizes()
    assert nc <= nb <= np <= sum(uses[v] for v in params)
    for values in product(ELEMENTS, repeat=len(params)):
        assert kernel.accepts(dict(zip(params, values))) == (values in possible), (equations, values)
    return len(GROUP) ** len(params)


def quadratic_audit():
    def pairings(slots):
        if not slots:
            yield []
            return
        first, *rest = slots
        for i, second in enumerate(rest):
            for tail in pairings(rest[:i] + rest[i + 1:]):
                yield [(first, second)] + tail

    patterns = cases = 0
    for size in range(1, 4):
        for pairs in pairings(list(range(2 * size))):
            for signs in product((-1, 1), repeat=size):
                word = [None] * (2 * size)
                for v, ((a, b), sign) in enumerate(zip(pairs, signs)):
                    word[a], word[b] = Var(v), Var(v, sign)
                for cut in range(1, len(word) + 1):
                    faces = [word[:cut], word[cut:]] if cut < len(word) else [word]
                    attainable = {
                        tuple(evaluate(face, assignment) for face in faces)
                        for assignment in product(ELEMENTS, repeat=size)
                    }
                    patterns += 1
                    for rhs in product(ELEMENTS, repeat=len(faces)):
                        equations = [face + [INV[c]] for face, c in zip(faces, rhs)]
                        assert compile_kernel(equations).accepts({}) == (rhs in attainable)
                        cases += 1
    return patterns, cases


def parameter_audit():
    patterns = assignments = 0
    # Cubic variables can visit one, two, or three components. Internal loops
    # include both orientation signs. The fixed coefficients include noncentral values.
    for names in ((0, 0, 0, 1, 1), (0, 1, 0, 2, 1, 0, 2),
                  (0, 1, 0, 1, 0, 1), (0, 1, 2, 0, 1, 0)):
        repeats = [i for i, v in enumerate(names) if v in names[:i]]
        for choices in product((-1, 1), repeat=len(repeats)):
            signs = dict(zip(repeats, choices))
            slots = [Var(v, signs.get(i, 1)) for i, v in enumerate(names)]
            for i in range(1, len(slots) + 1):
                for j in range(i, len(slots) + 1):
                    chunks = [c for c in (slots[:i], slots[i:j], slots[j:]) if c]
                    equations = [c[:1] + [(i + k) % 6] + c[1:] + [(j + k) % 6]
                                 for k, c in enumerate(chunks)]
                    assignments += check_every_parameter(equations)
                    patterns += 1
    # Static infeasibility and a completely free component are independent of x.
    x = Var(0)
    for equations in (([x, x, x], [1]), ([x, x, Var(1, -1)], [x, Var(2)])):
        assignments += check_every_parameter(equations)
        patterns += 1
    return patterns, assignments


def unary_patch_audit():
    """One exposed occurrence and up to two occurrences of every interior name."""
    z, u, v = Var(0), Var(1), Var(2)
    ui, vi = Var(1, -1), Var(2, -1)
    seen = set()
    full = frozenset(ELEMENTS)
    expected = {frozenset(), full}
    for coset in (SQUARES, full - SQUARES):
        for mask in range(1 << len(coset)):
            expected.add(frozenset(a for j, a in enumerate(sorted(coset)) if mask & (1 << j)))
    assert len(expected) == 16

    def check(words):
        names = sorted({x.name for word in words for x in word if isinstance(x, Var) and x.name != z.name})
        kernel = compile_kernel(words, exposed=(0,))
        supported = set()
        for values in product(ELEMENTS, repeat=len(names) + 1):
            assignment = dict(zip([0] + names, values))
            if all(evaluate(word, assignment) == ONE for word in words):
                supported.add(assignment[0])
        table = frozenset(a for a in ELEMENTS if kernel.accepts({0: a}))
        assert table == supported and table in expected
        seen.add(table)

    check([[z, u]])                        # Free interior label.
    check([[z], [1]])                      # Impossible separate equation.
    for a, b in product(ELEMENTS, repeat=2):
        check([[z, a, u, b, ui]])
        check([[z, u, v, ui, vi, a, b]])
        check([[z, a, u], [ui, v, b, v]])
    assert seen == expected
    return len(seen)


def stress_compression():
    x = Var(0)

    def word(handles, pairs):
        letters = []
        for i in range(handles):
            a, b = 2 * i + 1, 2 * i + 2
            letters.extend((Var(a), Var(b), Var(a, -1), Var(b, -1)))
        return letters + [x, 1, INV[1]] + [2, INV[2]] * pairs + [x, x]

    short = word(1, 0)
    long = word(512, 4096)
    reference = compile_kernel([short])
    kernel = compile_kernel([long])
    assert kernel.sizes() == reference.sizes() == (1, 1, 3)
    # In S3 the commutator set is a subgroup, and adjacent inverse constants cancel.
    assert set_product(COMMUTATORS, COMMUTATORS) == COMMUTATORS
    for value in ELEMENTS:
        brute = any(evaluate(short, (value, a, b)) == ONE for a, b in product(ELEMENTS, repeat=2))
        assert kernel.accepts({0: value}) == reference.accepts({0: value}) == brute
    return len(long), kernel.sizes()


if __name__ == '__main__':
    print('Quadratic patterns and right-hand sides:', quadratic_audit())
    print('Marked patterns and parameter assignments:', parameter_audit())
    print('Distinct one-exposure feasibility tables:', unary_patch_audit())
    print('Large word terms and kernel sizes:', stress_compression())
