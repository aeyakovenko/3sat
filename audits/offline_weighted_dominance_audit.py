"""Compare the sparse prefix-grid construction and transcript signatures to direct sums."""
from bisect import bisect_left
from itertools import product
from random import Random


def packed(bits):
    return sum(bit << i for i, bit in enumerate(bits))


def next_bit(x, depth, height):
    return (x >> (height-1-depth)) & 1 if depth < height else 0


def rank1(word, prefix_size):
    return (word & ((1 << prefix_size)-1)).bit_count()


def filter_bits(bits, selector, branch, size):
    return packed((bits >> i) & 1 for i in range(size) if (selector >> i) & 1 == branch)


class Cell:
    def __init__(self, size, dy, parent, cutoff):
        self.size = size
        self.dy = dy
        self.parent = parent
        self.heavy = size >= cutoff
        self.x = [None, None]
        self.y = [None, None]
        self.points = []
        self.xbits = self.ybits = 0


class Axis:
    def __init__(self, times, root):
        self.times = times
        self.root = root
        self.child = [None, None]


class Grid:
    def __init__(self, points, height, cutoff):
        self.points = points
        self.h = height
        self.cutoff = cutoff
        times = list(range(len(points)))
        self.axis = Axis(times, self.base(times, 0, None))
        self.expand(self.axis, 0)
        for idx, (x, y) in enumerate(points):
            self.scatter(idx, x, y)

    def step(self, v, depth):
        return next_bit(v, depth, self.h)

    def base(self, times, dy, parent):
        cell = Cell(len(times), dy, parent, self.cutoff)
        if cell.heavy:
            cell.xbits = packed(self.step(self.points[i][0], 0) for i in times)
            if dy < self.h:
                cell.ybits = packed(self.step(self.points[i][1], dy) for i in times)
                for val in range(2):
                    sub = [i for i in times if self.step(self.points[i][1], dy) == val]
                    cell.y[val] = self.base(sub, dy+1, cell)
        return cell

    def refine(self, old, xbranch, parent, size, xbits, dy):
        new = Cell(size, dy, parent, self.cutoff)
        if not new.heavy:
            return new
        assert old is not None and old.heavy
        old.x[xbranch] = new
        new.xbits = xbits
        if dy < self.h:
            new.ybits = filter_bits(old.ybits, old.xbits, xbranch, old.size)
            for ybranch in range(2):
                ones = new.ybits.bit_count()
                count = ones if ybranch else size-ones
                bits = filter_bits(xbits, new.ybits, ybranch, size)
                new.y[ybranch] = self.refine(old.y[ybranch], xbranch, new, count, bits, dy+1)
        return new

    def expand(self, axis, dx):
        if dx == self.h:
            return
        for xbranch in range(2):
            times = [i for i in axis.times if self.step(self.points[i][0], dx) == xbranch]
            if not times:
                continue
            bits = packed(self.step(self.points[i][0], dx+1) for i in times)
            root = self.refine(axis.root, xbranch, None, len(times), bits, 0)
            axis.child[xbranch] = Axis(times, root)
            self.expand(axis.child[xbranch], dx+1)

    def scatter(self, idx, x, y):
        cell = self.axis.root
        if not cell.heavy:
            return
        while cell.dy < self.h:
            child = cell.y[self.step(y, cell.dy)]
            if not child.heavy:
                break
            cell = child
        for dx in range(self.h+1):
            if cell.dy < self.h:
                light = cell.y[self.step(y, cell.dy)]
                assert not light.heavy
                light.points.append(idx)
            if dx == self.h:
                break
            xbranch = self.step(x, dx)
            while cell is not None and cell.x[xbranch] is None:
                cell = cell.parent
            if cell is None:
                break
            cell = cell.x[xbranch]

    def count_y(self, axis, y, t):
        if axis is None:
            return 0
        prefix = bisect_left(axis.times, t)
        cell = axis.root
        if not cell.heavy:
            return sum(self.points[i][1] <= y for i in axis.times[:prefix])
        answer = 0
        while cell.dy < self.h and cell.heavy:
            ones = rank1(cell.ybits, prefix)
            zeros = prefix-ones
            branch = self.step(y, cell.dy)
            if branch:
                answer += zeros
            prefix = ones if branch else zeros
            cell = cell.y[branch]
        if cell.dy == self.h:
            return answer+prefix
        return answer + sum(self.points[i][1] <= y for i in cell.points[:prefix])

    def count(self, x, y, t):
        axis = self.axis
        answer = 0
        for dx in range(self.h):
            if axis is None:
                return answer
            direction = self.step(x, dx)
            if direction:
                answer += self.count_y(axis.child[0], y, t)
            axis = axis.child[direction]
        return answer+self.count_y(axis, y, t)


def check_grids():
    rng = Random(264)
    queries = 0
    for height in (1,2,3,4):
        side = 1 << height
        for size in (0, 1, 7, 25, 70):
            points = [(rng.randrange(side), rng.randrange(side)) for _ in range(size)]
            if size > 7:
                points[-5:] = [points[0]] * 5
            for cutoff in (1,2,4,9,100):
                grid = Grid(points, height, cutoff)
                for x,y,t in product(range(side),range(side),sorted({0,1,size//2,size})):
                    direct = sum(a <= x and b <= y for a,b in points[:t])
                    assert grid.count(x,y,t) == direct
                    queries += 1
    return queries


def check_signatures():
    updates = [(1,2,2,7), (3,1,1,2), (4,2,2,1)]  # t,x,y,weight
    data = [(0,1,1), (2,2,2), (5,2,2), (6,1,3), (7,2,1)]
    actual = [sum(w for t,x,y,w in updates if t < j and x <= a and y <= b)
              for j,a,b in data]
    cases = 0
    for error in product((-1,0,1), repeat=len(data)):
        claims = [a+e for a,e in zip(actual, error)]
        undetected = 0
        for mask in range(1 << len(data)):
            retained = [data[i] for i in reversed(range(len(data))) if mask >> i & 1]
            grid = Grid([(3-x,3-y) for _,x,y in retained], 2, 2)
            rhs = sum(w * grid.count(3-x,3-y,sum(j>t for j,_,_ in retained))
                      for t,x,y,w in updates)
            lhs = sum(c for i,c in enumerate(claims) if mask >> i & 1)
            undetected += lhs == rhs
            assert lhs-rhs == sum(e for i,e in enumerate(error) if mask >> i & 1)
        if any(error):
            assert undetected <= (1 << (len(data)-1))
        else:
            assert undetected == (1 << len(data))
        cases += 1
    for mask in range(1 << len(actual)):
        noisy = [v ^ ((mask >> i) & 1) for i,v in enumerate(actual)]
        signed = sum((1 if guess & 1 else -1)*(guess-truth)
                     for guess,truth in zip(noisy,actual))
        assert signed == mask.bit_count()
    return cases


if __name__ == '__main__':
    print(f"Verified {check_grids()} prefix-count queries and every mask on {check_signatures()} error vectors.")
