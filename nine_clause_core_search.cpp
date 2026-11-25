// Count labeled minimally unsatisfiable proper 3-CNFs with nine clauses.
// Build with c++ -O3 -std=c++17 nine_clause_core_search.cpp -o nine_cores.
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <vector>

using Bits = std::uint64_t;

template<unsigned bits>
struct Set {
    std::array<Bits, (bits+63)/64> words{};
    bool contains(unsigned point) const {
        return (words[point / 64] >> (point % 64)) & 1;
    }
    void add(unsigned point) { words[point / 64] |= Bits{1} << (point % 64); }
    void remove(unsigned point) { words[point / 64] &= ~(Bits{1} << (point % 64)); }
    Set minus(const Set& other) const {
        Set result;
        for (unsigned i = 0; i < words.size(); ++i) result.words[i] = words[i] & ~other.words[i];
        return result;
    }
    Set either(const Set& other) const {
        Set result;
        for (unsigned i = 0; i < words.size(); ++i) result.words[i] = words[i] | other.words[i];
        return result;
    }
    bool has_outside(const Set& other) const {
        for (unsigned i = 0; i < words.size(); ++i)
            if (words[i] & ~other.words[i]) return true;
        return false;
    }
    unsigned first() const {
        for (unsigned i = 0; i < words.size(); ++i)
            if (words[i]) return 64*i + __builtin_ctzll(words[i]);
        return bits;
    }
    unsigned count() const {
        unsigned result = 0;
        for (Bits limb : words) result += __builtin_popcountll(limb);
        return result;
    }
};

template<unsigned v>
struct Search {
    static constexpr unsigned assignments = 1u << v;
    static constexpr unsigned face_size = assignments / 8;
    using Face = Set<assignments>;
    using Allowed = Set<8*v*(v-1)*(v-2)/6>;
    struct Clause { unsigned variables; unsigned pattern; Face face; };
    Face cube;
    std::vector<Clause> clauses;
    std::array<std::vector<unsigned>, assignments> incident;
    std::array<unsigned, 9> path{};
    std::array<Bits, 10> nodes{};
    std::array<Bits, v+1> by_variables{};
    std::array<Bits, v+1> with_degree_two{};
    std::array<Bits, 10> by_max_multiplicity{};
    std::map<decltype(Face{}.words), bool> geometries;
    std::array<Bits, v+1> skew{};
    Bits leaves = 0;

    void prepare_geometries() {
        for (const auto& clause : clauses) geometries.emplace(clause.face.words, false);
        for (unsigned axes = 0; axes < assignments; ++axes) {
            if (__builtin_popcount(axes) != 4) continue;
            for (unsigned fixed = 1; fixed < assignments; fixed <<= 1) {
                if (!(axes & fixed)) continue;
                unsigned flip = axes ^ fixed;
                for (unsigned pattern = 0; pattern < assignments; ++pattern) {
                    if ((pattern & ~axes) || pattern >= (pattern ^ flip)) continue;
                    Face doubled;
                    for (unsigned x = 0; x < assignments; ++x)
                        if ((x & axes) == pattern || (x & axes) == (pattern ^ flip))
                            doubled.add(x);
                    bool fresh = geometries.emplace(doubled.words, true).second;
                    assert(fresh);
                }
            }
        }
    }

    Search() {
        for (unsigned x = 0; x < assignments; ++x) cube.add(x);
        for (unsigned support = 1; support < assignments; ++support) {
            if (__builtin_popcount(support) != 3) continue;
            for (unsigned value = 0; value < assignments; ++value) {
                if (value & ~support) continue;
                Face face;
                for (unsigned x = 0; x < assignments; ++x)
                    if ((x & support) == value) face.add(x);
                unsigned id = clauses.size();
                clauses.push_back({support, value, face});
                for (unsigned x = 0; x < assignments; ++x)
                    if (face.contains(x)) incident[x].push_back(id);
            }
        }
    }

    void record(Face multiply_covered) {
        // Independently verify a spread of leaves from the raw input literals.
        if (!(leaves++ % 4096)) {
            std::array<bool, 9> private_point{};
            for (unsigned x = 0; x < assignments; ++x) {
                unsigned count = 0, last = 0;
                for (unsigned k = 0; k < path.size(); ++k) {
                    const auto& clause = clauses[path[k]];
                    if ((x & clause.variables) == clause.pattern) { ++count; last = k; }
                }
                assert(count > 0);
                if (count == 1) private_point[last] = true;
            }
            for (bool has_witness : private_point) assert(has_witness);
        }
        unsigned support = 0;
        std::array<unsigned, v> uses{};
        for (auto i : path) {
            support |= clauses[i].variables;
            for (unsigned j = 0; j < v; ++j) uses[j] += (clauses[i].variables >> j) & 1;
        }
        unsigned used = __builtin_popcount(support);
        ++by_variables[used];
        auto geometry = geometries.find(multiply_covered.words);
        assert(geometry != geometries.end());
        if (geometry->second) ++skew[used];
        bool degree_two = false;
        for (auto count : uses) degree_two |= count == 2;
        if (degree_two) ++with_degree_two[used];
        unsigned max_load = 1;
        for (unsigned point = multiply_covered.first(); point < assignments; point = multiply_covered.first()) {
            multiply_covered.remove(point);
            unsigned load = 0;
            for (auto i : path) load += clauses[i].face.contains(point);
            if (load > max_load) max_load = load;
        }
        ++by_max_multiplicity[max_load];
    }

    void visit(unsigned used, Face uncovered, Face multiple, Allowed allowed) {
        ++nodes[used];
        unsigned pivot = uncovered.first();
        if (pivot == assignments) {
            if (used == 9) record(multiple);
            return;
        }
        if (used == 9) return;
        unsigned uncovered_count = uncovered.count();
        assert(uncovered_count <= (9-used)*face_size);
        unsigned overlap_budget = (9-used)*face_size - uncovered_count;
        for (unsigned i : incident[pivot]) {
            if (!allowed.contains(i)) continue;
            // Earliest included candidate covering the pivot owns this subtree.
            allowed.remove(i);
            const Face& face = clauses[i].face;
            Face overlap = face.minus(uncovered);
            if (overlap.count() > overlap_budget) continue;
            Face new_multiple = multiple.either(overlap);
            bool all_private = true;
            for (unsigned j = 0; j < used; ++j) {
                if (!clauses[path[j]].face.has_outside(new_multiple)) {
                    all_private = false;
                    break;
                }
            }
            if (!all_private) continue;
            path[used] = i;
            visit(used + 1, uncovered.minus(face), new_multiple, allowed);
        }
    }

    void run() {
        prepare_geometries();
        Allowed allowed;
        for (unsigned i = 1; i < clauses.size(); ++i) allowed.add(i);
        path[0] = 0;
        visit(1, cube.minus(clauses[0].face), Face{}, allowed);
        auto labeled = [&](Bits fixed_count) {
            Bits pairs = fixed_count * clauses.size();
            assert(pairs % 9 == 0);
            return pairs / 9;
        };
        Bits all_fixed = 0;
        for (auto x : by_variables) all_fixed += x;
        std::cout << "v=" << v << ", fixed-clause cores " << all_fixed
                  << ", all labeled cores " << labeled(all_fixed) << "\n";
        for (unsigned j = 0; j <= v; ++j)
            if (by_variables[j])
                std::cout << "  uses " << j << " variables: " << labeled(by_variables[j])
                          << " (some variable occurs twice: " << labeled(with_degree_two[j])
                          << ", four-coordinate doubled set: " << labeled(skew[j]) << ")\n";
        std::cout << "  peak coverage multiplicity:";
        for (unsigned j = 1; j <= 9; ++j)
            if (by_max_multiplicity[j]) std::cout << ' ' << j << '=' << labeled(by_max_multiplicity[j]);
        std::cout << "\n  visited nodes by selected count:";
        for (unsigned j = 1; j <= 9; ++j) std::cout << ' ' << nodes[j];
        std::cout << '\n';
        if constexpr (v == 4) assert(labeled(all_fixed) == 9408);
    }
};

int main(int argc, char** argv) {
    int v = argc > 1 ? std::atoi(argv[1]) : 5;
    if (v == 4) Search<4>{}.run();
    else if (v == 5) Search<5>{}.run();
    else if (v == 6) Search<6>{}.run();
    else if (v == 7) Search<7>{}.run();
    else if (v == 8) Search<8>{}.run();
    else { std::cerr << "usage: nine_cores 4|5|6|7|8\n"; return 2; }
}
