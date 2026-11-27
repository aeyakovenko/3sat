// Exhaust every labeled nine-clause subset on four variables and independently
// enumerate the singular extensions of the eight sign patterns on a triple.
#include <array>
#include <algorithm>
#include <cstdlib>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>
using Mask = std::uint32_t;

struct Clause {
    unsigned support;
    unsigned values;
    unsigned forbidden;
};

struct Census {
    std::vector<Clause> clauses;
    std::set<Mask> lifts;
    std::vector<Mask> matchings;
    std::array<unsigned,9> distance{};
    std::array<Mask,9> example{};
    std::array<unsigned,9> selected{};
    std::uint64_t total = 0, unsat = 0, minimal = 0, generated = 0;
    Mask escape = 0;

    unsigned locate(unsigned s, unsigned a) const {
        for (unsigned i = 0; i < clauses.size(); ++i)
            if (clauses[i].support == s && clauses[i].values == (a & s)) return i;
        std::abort();
    }

    void build() {
        for (unsigned miss = 0; miss < 4; ++miss) {
            unsigned s = 15 ^ (1u << miss);
            for (unsigned a = 0; a < 16; ++a) if ((a & s) == a) {
                unsigned f = 0;
                for (unsigned x = 0; x < 16; ++x)
                    if ((x & s) == a) f |= 1u << x;
                clauses.push_back({s, a, f});
            }
        }
        for (unsigned newbit = 1; newbit <= 8; newbit <<= 1) {
            unsigned old = 15 ^ newbit;
            for (unsigned a = 0; a < 16; ++a) if ((a & old) == a) {
                Mask rest = 0;
                for (unsigned i = 0; i < 32; ++i)
                    if (clauses[i].support == old && clauses[i].values != a) rest |= Mask(1) << i;
                for (unsigned shared = 1; shared <= 8; shared <<= 1) if (old & shared) {
                    for (unsigned left = 1; left <= 8; left <<= 1) if ((old & left) && left != shared) {
                        unsigned right = old ^ shared ^ left;
                        unsigned u = locate(shared | left | newbit, a);
                        unsigned v = locate(shared | right | newbit, a | newbit);
                        lifts.insert(rest | (Mask(1) << u) | (Mask(1) << v));
                    }
                }
            }
        }
    }

    void matching(unsigned open, Mask chosen) {
        if (!open) {
            matchings.push_back(chosen);
            return;
        }
        unsigned first = open & (0u - open);
        for (unsigned i = 0; i < 32; ++i) {
            unsigned f = clauses[i].forbidden;
            if ((f & first) && (open & f) == f)
                matching(open ^ f, chosen | (Mask(1) << i));
        }
    }

    void visit(unsigned start, unsigned used, unsigned covered, unsigned multiple, Mask formula) {
        if (used < 9) {
            for (unsigned i = start; i + (9 - used) <= 32; ++i) {
                selected[used] = i;
                unsigned f = clauses[i].forbidden;
                visit(i + 1, used + 1, covered | f, multiple | (covered & f), formula | (Mask(1) << i));
            }
            return;
        }
        ++total;
        if (covered != 65535) return;
        ++unsat;
        for (auto i : selected)
            if (!(clauses[i].forbidden & ~multiple)) return;
        ++minimal;
        unsigned best = 8;
        for (auto parent : matchings)
            best = std::min(best, unsigned(__builtin_popcount(parent & ~formula)));
        ++distance[best];
        if (!example[best]) example[best] = formula;
        std::array<unsigned,4> uses{};
        for (auto i : selected)
            for (unsigned j = 0; j < 4; ++j)
                uses[j] += (clauses[i].support >> j) & 1;
        bool sparse = false;
        for (auto u : uses) sparse |= u == 2;
        bool is_lift = lifts.count(formula);
        assert(is_lift == sparse);
        generated += is_lift;
        if (!is_lift && !escape) escape = formula;
    }
};

int main() {
    Census c;
    c.build();
    c.matching(65535,0);
    assert(c.matchings.size() == 272);
    c.visit(0,0,0,0,0);
    assert(c.total == 28048800 && c.unsat == 15936 && c.minimal == 9408);
    assert(c.lifts.size() == 192 && c.generated == 192 && c.escape);
    std::cout << "nine-clause sets " << c.total << ", UNSAT " << c.unsat << ", minimal "
              << c.minimal << ", generated " << c.generated << ", missed "
              << c.minimal - c.generated << "\nfirst missed (support:pattern):";
    for (unsigned i = 0; i < 32; ++i)
        if ((c.escape >> i) & 1) std::cout << ' ' << c.clauses[i].support << ':' << c.clauses[i].values;
    std::cout << "\nminimum replacements from any eight-clause four-variable core:";
    for (unsigned j = 0; j < c.distance.size(); ++j)
        if (c.distance[j]) std::cout << ' ' << j << ':' << c.distance[j];
    std::cout << '\n';
}
