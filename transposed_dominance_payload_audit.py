"""Audit the geometry-only request list and its packed modular transpose."""
from bisect import bisect_left
from itertools import product
from random import Random

from offline_weighted_dominance_audit import Grid, rank1


class Lanes:
    def __init__(self, modulus):
        self.mod = modulus
        self.bits = (modulus-1).bit_length()
        self.mask = (1 << self.bits)-1

    def pack(self, values):
        return sum((v % self.mod) << (i*self.bits) for i, v in enumerate(values))

    def get(self, word, i):
        return (word >> (i*self.bits)) & self.mask

    def add_at(self, word, i, value):
        shift = i*self.bits
        old = self.get(word, i)
        return (word & ~(self.mask << shift)) | (((old+value) % self.mod) << shift)

    def plus(self, left, right, size):
        return self.pack(self.get(left,i)+self.get(right,i) for i in range(size))

    def split(self, word, mask, branch, size):
        return self.pack(self.get(word,i) for i in range(size) if mask >> i & 1 == branch)

    def merge(self, zero, one, mask, size):
        counts = [0, 0]
        out = []
        for i in range(size):
            b = (mask >> i) & 1
            out.append(self.get((zero,one)[b], counts[b]))
            counts[b] += 1
        return self.pack(out)

    def integrate(self, delta, size):
        cumulative = 0
        result = []
        for i in range(size):
            cumulative += self.get(delta,i)
            result.append(cumulative)
        return self.pack(result)


def x_nodes(grid, x):
    axis = grid.axis
    for dx in range(grid.h):
        if axis is None:
            return
        side = grid.step(x, dx)
        if side and axis.child[0] is not None:
            yield axis.child[0]
        axis = axis.child[side]
    if axis is not None:
        yield axis


def all_axes(axis):
    yield axis
    for child in axis.child:
        if child is not None:
            yield from all_axes(child)


def has_children(cell):
    return cell.heavy and cell.y[0] is not None


def requests(grid, x, y, t):
    """Emit one prefix per fully included node and individual boundary-light IDs."""
    for axis in x_nodes(grid, x):
        prefix = bisect_left(axis.times, t)
        cell = axis.root
        while has_children(cell):
            ones = rank1(cell.ybits, prefix)
            zeros = prefix-ones
            side = grid.step(y, cell.dy)
            if side:
                yield 'prefix', cell.y[0], zeros
            prefix = ones if side else zeros
            cell = cell.y[side]
        if cell.dy == grid.h:
            yield 'prefix', cell, prefix
        else:
            indices = axis.times if cell is axis.root else cell.points
            for idx in indices[:prefix]:
                if grid.points[idx][1] <= y:
                    yield 'point', idx, None


def apply(grid, queries, payload, lanes):
    word_at = {}
    def descend(cell, word):
        word_at[cell] = word
        if has_children(cell):
            for side in range(2):
                child = lanes.split(word, cell.ybits, side, cell.size)
                descend(cell.y[side],child)
    for axis in all_axes(grid.axis):
        descend(axis.root, lanes.pack(payload[i] for i in axis.times))

    answer = []
    for x,y,t in queries:
        total = 0
        for kind, target, r in requests(grid,x,y,t):
            if kind == 'point':
                total += payload[target]
            else:
                total += sum(lanes.get(word_at[target],i) for i in range(r))
        answer.append(total % lanes.mod)
    return answer


def transpose(grid, queries, weights, lanes):
    differences = {}
    result = [0]*len(grid.points)
    for (x,y,t), weight in zip(queries,weights):
        for kind, target, r in requests(grid,x,y,t):
            if kind == 'point':
                result[target] += weight
            elif r:
                delta = lanes.add_at(differences.get(target,0),0,weight)
                differences[target] = lanes.add_at(delta,r,-weight)
    def ascend(cell):
        local = lanes.integrate(differences.get(cell,0), cell.size)
        if not has_children(cell):
            return local
        returns = [ascend(child) for child in cell.y]
        merged = lanes.merge(*returns,cell.ybits,cell.size)
        return lanes.plus(local, merged, cell.size)
    for axis in all_axes(grid.axis):
        answer = ascend(axis.root)
        for j,idx in enumerate(axis.times):
            result[idx] += lanes.get(answer,j)
    return [x % lanes.mod for x in result]


def check(points, height, cutoff, queries, weights, payload, lanes):
    grid = Grid(points,height,cutoff)
    computed = apply(grid,queries,payload,lanes)
    rev = transpose(grid,queries,weights,lanes)
    matrix = [[int(i<t and a<=x and b<=y) for i,(a,b) in enumerate(points)]
              for x,y,t in queries]
    expected = [sum(m*p for m,p in zip(row,payload)) % lanes.mod for row in matrix]
    expected_rev = [sum(row[i]*w for row,w in zip(matrix,weights)) % lanes.mod
                    for i in range(len(points))]
    assert computed == expected
    assert rev == expected_rev
    assert (sum(a*b for a,b in zip(computed,weights))
            - sum(a*b for a,b in zip(payload,rev))) % lanes.mod == 0


def main():
    point_sets = 0
    rng = Random(423893)
    for height, size, nqueries in ((1,0,1),(1,1,7),(2,5,9),(3,37,40),(4,80,91)):
        side = 1 << height
        points = [(rng.randrange(side),rng.randrange(side)) for _ in range(size)]
        if size >= 5:
            points[-3:] = [points[0]]*3
        queries = [(rng.randrange(side),rng.randrange(side),rng.randrange(size+1))
                   for _ in range(nqueries)]
        queries.extend(((side-1,side-1,size),(0,0,0),(0,side-1,size)))
        for cutoff,mod in product((1,2,4,11,100), (2,3,4,5,8,13,16,257)):
            weights = [rng.randrange(-mod,mod) for _ in queries]
            payload = [rng.randrange(mod) for _ in points]
            check(points,height,cutoff,queries,weights,payload,Lanes(mod))
            point_sets += 1
    # Exhaust all binary original payloads and original update weights on one graph.
    points = [(1,1),(0,2),(1,1),(3,0)]
    queries = [(3,1,0),(1,2,2),(2,2,4),(3,0,4)]
    for payload, weights in product(product(range(2),repeat=4),repeat=2):
        check(points,2,2,queries,weights,payload,Lanes(2))
    print(f"{point_sets} modular geometries and 256 exhaustive binary payload/weight pairs passed both matrix products.")


if __name__ == '__main__':
    main()
