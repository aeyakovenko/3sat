// c++ -O3 -std=c++17 eight_bit_store_controls.cpp -o /tmp/eight-bit-store
#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>
#include <set>
#include <vector>

using std::array;
using std::vector;

struct Input { int words, essential; bool sat; };
struct Load { int reg, address; };
struct Palette { array<Load, 2> loads; int address, payload; };
struct State { int memory, r = 0, s = 0, read = 0, written = 0; };
struct Graph { array<array<int, 2>, 5> next; int start; };
using Paths = array<std::set<vector<int>>, 2>;

bool satisfiable(int words) {
    int positive = words & 15, negative = words >> 4;
    return !(positive & negative) && negative != 15;
}

vector<Input> catalogue() {
    vector<Input> inputs;
    for (int u = 0; u < 256; ++u) {
        int essential = 0;
        for (int cell = 0; cell < 3; ++cell)
            for (int v = 0; v < (cell == 2 ? 4 : 8); ++v) {
                int pos = 3 * cell;
                int mutant = (u & ~(7 << pos)) | (v << pos);
                if (satisfiable(mutant) != satisfiable(u)) essential |= 1 << cell;
            }
        inputs.push_back({u, essential, satisfiable(u)});
    }
    assert(std::count_if(inputs.begin(), inputs.end(), [](Input x) {
        return x.sat && x.essential == 7;
    }) == 17);
    std::stable_sort(inputs.begin(), inputs.end(), [](Input x, Input y) {
        return (x.essential == 7) > (y.essential == 7);
    });
    return inputs;
}

int operand(int code, const State& state) {
    if (code < 8) return code;
    return code == 8 ? state.r : state.s;
}

void execute(int site, const Palette& palette, State& state) {
    if (site < 2) {
        const auto load = palette.loads[site];
        int address = operand(load.address, state);
        int value = (state.memory >> (3 * address)) & 7;
        if (load.reg == 0) state.r = value;
        else state.s = value;
        if (!(state.written & (1 << address))) state.read |= 1 << address;
    } else {
        int address = operand(palette.address, state);
        int value = operand(palette.payload, state);
        state.memory = (state.memory & ~(7 << (3 * address))) | (value << (3 * address));
        state.written |= 1 << address;
    }
}

// Relax the control graph to an arbitrary data sequence with enough steps
// left for the comparisons separating revisits and the final verdict.
bool can_read(const Palette& palette, int needed, State state, int length, array<int, 3> counts) {
    if ((state.read & needed) == needed) return true;
    if (state.written & ~state.read & needed) return false;
    for (int site = 0; site < 3; ++site) {
        auto visits = counts;
        ++visits[site];
        if (length + 1 + *std::max_element(visits.begin(), visits.end()) > 8) continue;
        auto after = state;
        execute(site, palette, after);
        if (after.r == state.r && after.s == state.s && after.memory == state.memory &&
            after.read == state.read) continue;
        if (can_read(palette, needed, after, length + 1, visits)) return true;
    }
    return false;
}

vector<Palette> filter_palettes(const vector<Input>& inputs) {
    vector<Palette> survivors;
    int count = 0;
    for (int dest = 0; dest < 2; ++dest) {
        int choices = 9 + dest; // eight literals and either one or two live registers
        for (int a = 0; a < choices; ++a) for (int b = 0; b < choices; ++b) {
            if (a < 8 && b < 8) continue;
            if (dest == 0 && b < a) continue; // identical destinations, exchange the LOAD names
            for (int addr = 0; addr < choices; ++addr) for (int value = 0; value < choices; ++value) {
                Palette palette{{Load{0, a}, Load{dest, b}}, addr, value};
                ++count;
                if (std::all_of(inputs.begin(), inputs.end(), [&](Input x) {
                    return can_read(palette, x.essential, State{x.words}, 0, {});
                })) survivors.push_back(palette);
            }
        }
    }
    assert(count == 4329 && survivors.size() == 12);
    std::cout << count << " palettes, " << survivors.size() << " pass unrestricted data paths\n";
    return survivors;
}

void enumerate_paths(const Graph& g, int pc, int left, Paths& out, vector<int>& data) {
    if (pc >= 5) { out[pc == 5].insert(data); return; }
    if (left == 0) return;
    if (pc < 3) {
        data.push_back(pc);
        enumerate_paths(g, g.next[pc][0], left - 1, out, data);
        data.pop_back();
    } else {
        for (int child : g.next[pc]) enumerate_paths(g, child, left - 1, out, data);
    }
}

bool possible(const Palette& palette, const Paths& paths, Input x) {
    for (const auto& path : paths[x.sat]) {
        State state{x.words};
        for (int site : path) execute(site, palette, state);
        if ((state.read & x.essential) == x.essential) return true;
    }
    return false;
}

int main() {
    auto inputs = catalogue();
    auto palettes = filter_palettes(inputs);
    Graph g{};
    int graphs = 0, pairs = 0;
    for (int edges = 0; edges < 125; ++edges) {
        int code = edges;
        for (int i = 0; i < 3; ++i, code /= 5) g.next[i] = {code % 5, code % 5};
        for (int a = 0; a < 7; ++a) for (int b = a + 1; b < 7; ++b)
        for (int c = 0; c < 7; ++c) for (int d = c + 1; d < 7; ++d) {
            g.next[3] = {a, b}; g.next[4] = {c, d};
            for (g.start = 0; g.start < 5; ++g.start) {
                int pc = g.start;
                for (int i = 0; i < 5 && pc < 3; ++i) pc = g.next[pc][0];
                if (pc != 3) continue; // name the first reachable comparison site 3
                Paths paths;
                vector<int> data;
                enumerate_paths(g, g.start, 8, paths, data);
                if (paths[0].empty() || paths[1].empty()) continue;
                if (std::none_of(paths[1].begin(), paths[1].end(), [](const auto& path) {
                    return std::count_if(path.begin(), path.end(), [](int site) { return site < 2; }) >= 3;
                })) continue;
                ++graphs;
                for (const auto& p : palettes)
                    if (std::all_of(inputs.begin(), inputs.end(), [&](Input x) {
                        return possible(p, paths, x);
                    })) ++pairs;
            }
        }
    }
    assert(graphs == 734 && pairs == 0);
    std::cout << graphs << " control graphs, " << pairs << " feasible graph/palette pairs\n";
}
