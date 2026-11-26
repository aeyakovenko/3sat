"""Exhaust small edge labelings for linear parity filters on equality partitions.

The default checks K7 using just matchings. With --large, the embedded C++17
accelerator exhausts K8 using every partition. No SAT solver is required.
"""

import argparse
import itertools
from functools import lru_cache
from pathlib import Path
import subprocess
import tempfile


def partitions(n):
    """Restricted-growth strings, with blocks ordered by first appearance."""
    def extend(word, blocks):
        if len(word) == n:
            yield tuple(word)
            return
        for label in range(blocks + 1):
            word.append(label)
            yield from extend(word, max(blocks, label + 1))
            word.pop()
    yield from extend([], 0)


def check_labels(n, labels):
    edges = list(itertools.combinations(range(n), 2))
    assert len(labels) == len(edges)
    tested = 0
    for partition in partitions(n):
        xor = 0
        nonempty = False
        for (i, j), weight in zip(edges, labels):
            if partition[i] == partition[j]:
                xor ^= weight
                nonempty = True
        assert bool(xor) == nonempty
        tested += nonempty
    return tested


def check_pinned_color_counts():
    """Cover surviving edges by intersecting color classes (stars or triangles)."""
    for n in range(3, 9):
        all_edges = list(itertools.combinations(range(n), 2))
        stars = [sum(1 << i for i, edge in enumerate(all_edges) if v in edge)
                 for v in range(n)]
        triangles = [sum(1 << i for i, (a, b) in enumerate(all_edges) if a in vs and b in vs)
                     for vs in itertools.combinations(range(n), 3)]
        classes = stars + triangles

        @lru_cache(None)
        def min_colors(uncovered):
            if not uncovered:
                return 0
            witness = uncovered & -uncovered
            return 1 + min(min_colors(uncovered & ~color) for color in classes if color & witness)

        for pinned in range(n + 1):
            surviving = sum(1 << i for i, (_, b) in enumerate(all_edges) if b >= pinned)
            assert min_colors(surviving) == min(n - pinned, n - 2)


def check_probes(dimension, probes):
    for word in range(1, 1 << dimension):
        excess = 0
        for p in probes:
            excess += 2 * ((p & word).bit_count() % 2) - 1
            if excess > 0:
                break
        else:
            raise AssertionError((dimension, probes, word))


def search_matchings(n, dimension):
    edges = list(itertools.combinations(range(n), 2))
    edge_ids = range(len(edges))
    others = [[] for _ in edges]
    for cardinality in range(2, n // 2 + 1):
        for selected in itertools.combinations(edge_ids, cardinality):
            if len({v for e in selected for v in edges[e]}) != 2 * cardinality:
                continue
            for e in selected:
                others[e].append(tuple(f for f in selected if f != e))
    labels = [0] * len(edges)
    # These disjoint edges are necessarily linearly independent. A change of
    # target-space basis sends their labels to the successive coordinate bits.
    for i in range(n // 2):
        labels[edges.index((2*i, 2*i+1))] = 1 << i
    visited = 0

    def search():
        nonlocal visited
        visited += 1
        choice = None
        for e in edge_ids:
            if labels[e]:
                continue
            allowed = (1 << (1 << dimension)) - 2  # All nonzero labels.
            for matching in others[e]:
                weight = 0
                for f in matching:
                    if not labels[f]:
                        break
                    weight ^= labels[f]
                else:
                    allowed &= ~(1 << weight)
            if not allowed:
                return False
            if choice is None or allowed.bit_count() < choice[0]:
                choice = (allowed.bit_count(), e, allowed)
        if choice is None:
            return True
        _, e, allowed = choice
        while allowed:
            bit = allowed & -allowed
            allowed -= bit
            labels[e] = bit.bit_length() - 1
            if search():
                return True
        labels[e] = 0
        return False

    return search(), visited


# The K8 accelerator performs the same minimum-remaining-values search with
# incremental constraint updates. Each partition row stores the XOR of its
# assigned labels and a 28-bit mask of its still unassigned internal edges.
ACCELERATOR = r'''
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <utility>
#include <vector>

using Bits = std::uint32_t;

struct Constraint {
    Bits unassigned;
    unsigned partial;
};

struct Restore {
    int edge;
    Bits old_domain;
};

class Exhaustion {
    int n, dimension;
    std::vector<std::pair<int,int>> edges;
    std::vector<int> assigned;
    std::vector<Bits> domains;
    std::vector<Constraint> rows;
    std::vector<std::vector<int>> containing;

    void partitions(std::vector<int>& word, int blocks) {
        if (int(word.size()) < n) {
            for (int b = 0; b <= blocks; ++b) {
                word.push_back(b);
                partitions(word, std::max(blocks, b + 1));
                word.pop_back();
            }
            return;
        }
        Bits mask = 0;
        for (int e = 0; e < int(edges.size()); ++e) {
            auto [v, w] = edges[e];
            if (word[v] == word[w]) mask |= Bits(1) << e;
        }
        if (mask == 0) return;
        int row = int(rows.size());
        rows.push_back({mask, 0});
        for (int e = 0; e < int(edges.size()); ++e)
            if ((mask >> e) & 1) containing[e].push_back(row);
    }

public:
    std::uint64_t visited = 0;
    Exhaustion(int vertices, int rank) : n(vertices), dimension(rank) {
        for (int a = 0; a < n; ++a)
            for (int b = a+1; b < n; ++b) edges.emplace_back(a,b);
        for (auto [a,b] : edges) {
            assigned.push_back(0);
            // Unit matching constraints exclude label zero; the displayed
            // disjoint matching may be fixed to coordinate vectors.
            Bits all_nonzero = (Bits(1) << (1u << dimension)) - 2;
            bool fixed = (a % 2 == 0 && b == a+1);
            domains.push_back(fixed ? Bits(1) << (1u << (a/2)) : all_nonzero);
        }
        containing.resize(edges.size());
        std::vector<int> empty;
        partitions(empty, 0);
    }

    std::size_t row_count() const { return rows.size(); }

    bool search() {
        ++visited;
        int e = -1, best = 100;
        for (int f = 0; f < int(edges.size()); ++f) {
            if (assigned[f]) continue;
            int choices = __builtin_popcount(domains[f]);
            if (choices < best) {
                best = choices;
                e = f;
            }
        }
        if (e < 0) return true;
        Bits domain = domains[e];
        while (domain) {
            unsigned value = __builtin_ctz(domain);
            domain &= domain-1;
            assigned[e] = value;
            bool viable = true;
            std::vector<Restore> restore;
            for (int j : containing[e]) {
                auto& row = rows[j];
                row.unassigned ^= Bits(1) << e;
                row.partial ^= value;
                if (!row.unassigned) {
                    if (!row.partial) viable = false;
                } else if ((row.unassigned & (row.unassigned-1)) == 0) {
                    // This last label must differ from the previous XOR.
                    int f = __builtin_ctz(row.unassigned);
                    Bits forbidden = Bits(1) << row.partial;
                    if (domains[f] & forbidden) {
                        restore.push_back({f, domains[f]});
                        domains[f] &= ~forbidden;
                        if (domains[f] == 0) viable = false;
                    }
                }
            }
            if (viable && search()) return true;
            for (auto it = restore.rbegin(); it != restore.rend(); ++it)
                domains[it->edge] = it->old_domain;
            for (int j : containing[e]) {
                rows[j].unassigned ^= Bits(1) << e;
                rows[j].partial ^= value;
            }
            assigned[e] = 0;
        }
        return false;
    }
};

int main() {
    // Positive control uses the same code and propagates all partition rows.
    Exhaustion small(6, 3);
    if (small.row_count() != 202 || !small.search()) return 1;
    Exhaustion target(8, 4);
    if (target.row_count() != 4139 || target.search()) return 1;
    std::cout << target.row_count() << " nontrivial K8 partitions, "
              << target.visited << " search nodes, no four-bit labeling\n";
}
'''


def exhaustive_k8(compiler):
    with tempfile.TemporaryDirectory() as directory:
        base = Path(directory)
        source, binary = base / 'collision.cpp', base / 'collision'
        source.write_text(ACCELERATOR)
        subprocess.run([compiler, '-std=c++17', '-O3', str(source), '-o', str(binary)],
                       check=True)
        subprocess.run([str(binary)], check=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--large', action='store_true', help='exhaust all K8 assignments')
    parser.add_argument('--cxx', default='c++')
    args = parser.parse_args()
    check_pinned_color_counts()
    # Edge order is lexicographic on the two zero-based endpoints.
    six = [1, 2, 2, 3, 4, 1, 1, 3, 4, 2, 3, 4, 3, 4, 4]
    assert check_labels(6, six) == 202
    for n, endpoints in [(5, [2,1,3,3,0]), (7, [8,4,2,1,3,3,0]),
                         (8, [16,8,4,2,1,3,3,0])]:
        check_labels(n, [endpoints[i] for i, _ in itertools.combinations(range(n), 2)])
    check_probes(3, [1, 2, 4, 6, 6])
    check_probes(4, [1, 2, 4, 8, 14, 6, 8, 14, 14])
    check_probes(5, [1, 2, 2, 4, 8, 16, 28, 12, 20, 12, 20, 24, 24, 24, 24])
    possible, nodes = search_matchings(7, 3)
    assert not possible
    print(f'K5 through K8 upper witnesses valid, K7 three-bit matching search exhausted in {nodes} nodes',
          flush=True)
    if args.large:
        exhaustive_k8(args.cxx)
