// Maximum size of the intersection of an affine space in F_2^12 with the
// graph of 2-by-2 binary matrix multiplication. Build with g++ -O3 -std=c++17.
//
// Project an affine section to its A coordinates and denote this affine image
// by P. At each A in P the allowed (B,C)'s form a translate of one common
// linear space V. Their intersection with graph(B -> AB) is empty or a coset
// of V intersect graph(B -> AB). P x V attains every fiber upper bound at
// once (all fibers contain zero). Translating A by A0 and C by A0 B is an
// affine automorphism preserving the graph; it sends P x V to P0 x V' with
// P0 linear and V' linear of the same dimension. Thus enumerating linear
// P0 in F_2^4 and V' in F_2^8 suffices in every codimension.

#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <utility>
#include <vector>

struct Space {
    int dimension = 0;
    std::array<int, 8> basis{};
    std::array<int, 256> elements{};
};

// Every subspace has a unique row-reduced basis. For a pivot at bit j, the
// nonpivot entries strictly to its right are the only entries of the row
// that may vary.
template <class Visitor>
void visit_spaces(int width, Visitor visit) {
    for (int pivots = 0; pivots < (1 << width); ++pivots) {
        Space space;
        std::vector<std::pair<int, int>> free_entries;
        for (int j = 0; j < width; ++j) {
            if (!(pivots & (1 << j))) continue;
            int row = space.dimension++;
            space.basis[row] = 1 << j;
            for (int col = j + 1; col < width; ++col) {
                if (!(pivots & (1 << col))) free_entries.emplace_back(row, col);
            }
        }
        const auto pivot_rows = space.basis;
        for (int choice = 0; choice < (1 << free_entries.size()); ++choice) {
            space.basis = pivot_rows;
            for (std::size_t j = 0; j < free_entries.size(); ++j) {
                if (choice & (1 << j)) {
                    auto [row, col] = free_entries[j];
                    space.basis[row] |= 1 << col;
                }
            }
            for (int i = 0; i < space.dimension; ++i) {
                for (int t = 0; t < (1 << i); ++t) {
                    space.elements[(1 << i) + t] = space.elements[t] ^ space.basis[i];
                }
            }
            visit(space);
        }
    }
}

int matrix_product(int a, int b) {
    int c = 0;
    for (int i = 0; i < 2; ++i) {
        for (int j = 0; j < 2; ++j) {
            int entry = 0;
            for (int k = 0; k < 2; ++k) {
                entry ^= ((a >> (2 * i + k)) & 1) & ((b >> (2 * k + j)) & 1);
            }
            c |= entry << (2 * i + j);
        }
    }
    return c;
}

// Check codimensions one and two in the full ambient space without using
// the fiber reduction. A coset indicator is a sum of two or four characters.
void check_low_codimensions(const std::array<int, 13>& best) {
    std::array<int, 4096> walsh{};
    for (int a = 0; a < 16; ++a) {
        for (int b = 0; b < 16; ++b) {
            int point = a | (b << 4) | (matrix_product(a, b) << 8);
            ++walsh[point];
        }
    }
    for (int stride = 1; stride < 4096; stride *= 2) {
        for (int base = 0; base < 4096; base += 2 * stride) {
            for (int j = base; j < base + stride; ++j) {
                int x = walsh[j], y = walsh[j + stride];
                walsh[j] = x + y;
                walsh[j + stride] = x - y;
            }
        }
    }
    int one = 0, two = 0;
    for (int u = 1; u < 4096; ++u) {
        one = std::max(one, (walsh[0] + std::abs(walsh[u])) / 2);
        for (int v = u + 1; v < 4096; ++v) {
            if ((u ^ v) <= v) continue;  // one basis per triple of nonzero normals
            for (int sign : {-1, 1}) {
                int other = std::abs(walsh[v] + sign * walsh[u ^ v]);
                two = std::max(two, (walsh[0] + sign * walsh[u] + other) / 4);
            }
        }
    }
    assert(one == best[1] && two == best[2]);
}

int main() {
    std::vector<Space> projections;
    visit_spaces(4, [&](const Space& p) { projections.push_back(p); });
    std::array<std::array<int, 16>, 16> graph_fibers{};
    for (int a = 0; a < 16; ++a) {
        for (int b = 0; b < 16; ++b) graph_fibers[a][b] = b | (matrix_product(a, b) << 4);
    }
    std::array<int, 13> best{};
    std::uint64_t fiber_count = 0;
    visit_spaces(8, [&](const Space& v) {
        ++fiber_count;
        std::array<unsigned char, 256> member{};
        for (int i = 0; i < (1 << v.dimension); ++i) member[v.elements[i]] = 1;
        std::array<int, 16> weights{};
        for (int a = 0; a < 16; ++a) {
            for (int p : graph_fibers[a]) weights[a] += member[p];
        }
        for (const Space& p : projections) {
            int count = 0;
            for (int i = 0; i < (1 << p.dimension); ++i) count += weights[p.elements[i]];
            int codimension = 12 - p.dimension - v.dimension;
            best[codimension] = std::max(best[codimension], count);
        }
    });
    assert(projections.size() == 67 && fiber_count == 417199);
    check_low_codimensions(best);
    assert(best[0] == 256);
    for (int h = 8; h <= 12; ++h) assert(best[h] == (1 << (12 - h)));
    std::cout << projections.size() << " projection spaces x " << fiber_count
              << " fiber spaces = " << projections.size() * fiber_count << " pairs\n";
    std::cout << "codimension  maximum graph points\n";
    for (int h = 0; h <= 12; ++h) std::cout << h << "  " << best[h] << '\n';
}
