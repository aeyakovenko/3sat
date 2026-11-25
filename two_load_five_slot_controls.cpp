// Read the aliased data palettes from two_load_five_slot_audit.py --emit-palettes.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>

using std::array;
using std::vector;

struct Palette {
    array<int,16> unary;
    array<int,2> dest, address;
};

struct Graph {
    array<array<int,2>,5> next;
    int start;
};

using Predicate = array<std::uint8_t,256>;
using Memory = array<int,4>;

vector<Palette> read_palettes() {
    vector<Palette> result;
    Palette palette{};
    while (std::cin >> palette.unary[0]) {
        for (int i = 1; i < 16; ++i) std::cin >> palette.unary[i];
        for (int i = 0; i < 2; ++i) std::cin >> palette.dest[i] >> palette.address[i];
        if (!std::cin) return {};
        result.push_back(palette);
    }
    return result;
}

int operand(int code, int r, int s) {
    return code < 16 ? code : (code == 16 ? r : s);
}

int signed_word(int x) { return (x + 8) % 16 - 8; }

vector<Predicate> predicates() {
    std::set<Predicate> distinct;
    for (int a = 0; a < 18; ++a) for (int b = 0; b < 18; ++b)
        for (int cmp = 0; cmp < 3; ++cmp) for (int neg = 0; neg < 2; ++neg) {
            Predicate table{};
            for (int r = 0; r < 16; ++r) for (int s = 0; s < 16; ++s) {
                int x = operand(a, r, s), y = operand(b, r, s);
                bool outcome = cmp == 0 ? x == y : cmp == 1 ? x < y : signed_word(x) < signed_word(y);
                table[16*r+s] = outcome != bool(neg);
            }
            distinct.insert(table);
        }
    return {distinct.begin(), distinct.end()};
}

void yes_paths(const Graph& graph, int pc, int steps, vector<int>& data,
               int loads, std::set<vector<int>>& paths) {
    if (pc >= 5) {
        if (pc == 5 && loads >= 4) paths.insert(data);
        return;
    }
    if (steps == 0) return;
    if (pc < 3) {
        data.push_back(pc);
        yes_paths(graph, graph.next[pc][0], steps-1, data, loads + (pc < 2), paths);
        data.pop_back();
    } else {
        for (int next : graph.next[pc])
            yes_paths(graph, next, steps-1, data, loads, paths);
    }
}

int data_step(int site, const Palette& palette, const Memory& memory, array<int,2>& regs) {
    if (site == 2) {
        regs[0] = palette.unary[regs[0]];
        return 0;
    }
    int arg = palette.address[site];
    int address = arg >= 5 ? regs[arg-5] : arg;
    regs[palette.dest[site]] = address < 4 ? memory[address] : 0;
    return address < 4 ? 1 << address : 0;
}

bool can_read_all(const std::set<vector<int>>& paths, const Palette& palette, const Memory& memory) {
    for (const auto& path : paths) {
        int seen = 0;
        array<int,2> regs{};
        for (int site : path) seen |= data_step(site, palette, memory, regs);
        if (seen == 15) return true;
    }
    return false;
}

bool correct(const Graph& graph, const Palette& palette, const Predicate& first,
             const Predicate& second, const Memory& memory) {
    bool target = !(memory[0] & memory[2]) && !(memory[1] & memory[3]) &&
                  (memory[2] != 15 || memory[3] != 15);
    int pc = graph.start;
    array<int,2> regs{};
    for (int t = 0; t < 16 && pc < 5; ++t) {
        int edge = 0;
        if (pc < 3) data_step(pc, palette, memory, regs);
        else edge = (pc == 3 ? first : second)[16*regs[0]+regs[1]];
        pc = graph.next[pc][edge];
    }
    return pc == (target ? 5 : 6);
}

struct Census {
    vector<Palette> palettes;
    vector<Predicate> tests = predicates();
    vector<Memory> positive, fixtures;
    std::uint64_t graphs = 0, pairs = 0, programs = 0, survivors = 0;

    explicit Census(vector<Palette> p) : palettes(p) {
        for (int x = 1; x < 16; ++x) for (int y = 1; y < 16; ++y) if (!(x & y)) {
            Memory base{x,x,y,y};
            positive.push_back(base);
            fixtures.push_back(base);
            for (int j = 0; j < 4; ++j) {
                Memory mutant = base;
                mutant[j] = 15;
                fixtures.push_back(mutant);
            }
        }
        fixtures.push_back({7,9,3,0});
    }

    void examine(const Graph& graph) {
        // The first conditional met before any branch choice may be named site 3.
        int pc = graph.start;
        for (int t = 0; t < 6 && pc < 3; ++t) pc = graph.next[pc][0];
        if (pc != 3) return;
        int reached = 1 << graph.start, before;
        do {
            before = reached;
            for (int i = 0; i < 5; ++i) if ((reached >> i) & 1)
                for (int next : graph.next[i]) reached |= 1 << next;
        } while (reached != before);
        if ((reached & 96) != 96) return;

        std::set<vector<int>> paths;
        vector<int> sequence;
        yes_paths(graph, graph.start, 16, sequence, 0, paths);
        if (paths.empty()) return;
        ++graphs;
        for (const auto& palette : palettes) {
            if (!std::all_of(positive.begin(), positive.end(), [&](const Memory& x) {
                    return can_read_all(paths, palette, x);
                })) continue;
            ++pairs;
            for (const auto& first : tests) for (const auto& second : tests) {
                ++programs;
                if (std::all_of(fixtures.begin(), fixtures.end(), [&](const Memory& x) {
                        return correct(graph, palette, first, second, x);
                    })) ++survivors;
            }
        }
    }

    void run() {
        Graph graph{};
        for (int destinations = 0; destinations < 125; ++destinations) {
            int digits = destinations;
            for (int i = 0; i < 3; ++i, digits /= 5)
                graph.next[i] = {digits % 5, digits % 5};
            for (int a = 0; a < 7; ++a) for (int b = a+1; b < 7; ++b)
                for (int c = 0; c < 7; ++c) for (int d = c+1; d < 7; ++d) {
                    graph.next[3] = {a,b};
                    graph.next[4] = {c,d};
                    for (graph.start = 0; graph.start < 5; ++graph.start) examine(graph);
                }
        }
    }
};

int main() {
    Census census(read_palettes());
    if (census.palettes.size() != 31) return 1;
    census.run();
    std::cout << census.graphs << " control graphs, " << census.pairs << " graph/palette pairs, "
              << census.tests.size() << " predicates, " << census.programs << " realizations, "
              << census.survivors << " survivors on " << census.fixtures.size() << " fixtures\n";
    return !(census.graphs == 1584 && census.pairs == 579 && census.tests.size() == 176 &&
             census.programs == 17935104 && census.survivors == 0 && census.fixtures.size() == 251);
}
