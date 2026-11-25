// Full dense eight-bit, three-bit-word census for two LOADs and one ALU.
#include <algorithm>
#include <array>
#include <bitset>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <set>
#include <vector>
namespace eight_bit {
using std::array;
using std::bitset;
using std::map;
using std::set;
using std::vector;
using Graph = array<array<int, 2>, 5>;
using Lookup = array<std::uint8_t, 512>;
int signed_value(int x) { return (x + 4) % 8 - 4; }
int arithmetic_shift(int x, int count) {
  int n = signed_value(x), divisor = 1 << count;
  return n >= 0 ? n / divisor : -((-n + divisor - 1) / divisor);
}
int operation(int opcode, int a, int b) {
  switch (opcode) {
  case 0:
    return a & b;
  case 1:
    return a | b;
  case 2:
    return a ^ b;
  case 3:
    return a + b;
  case 4:
    return a - b;
  case 5:
    return a * b;
  case 6:
    return a << b;
  case 7:
    return a >> b;
  case 8:
    return arithmetic_shift(a, b);
  case 9:
    return a << (b % 3);
  case 10:
    return a >> (b % 3);
  case 11:
    return arithmetic_shift(a, b % 3);
  case 12:
    return (a << (b % 3)) | (a >> (3 - b % 3));
  case 13:
    return (a >> (b % 3)) | (a << (3 - b % 3));
  case 14:
    return a == b;
  case 15:
    return a < b;
  case 16:
    return signed_value(a) < signed_value(b);
  case 17:
    return a != b;
  case 18:
    return a >= b;
  default:
    return signed_value(a) >= signed_value(b);
  }
}
int source(int operand, int state) {
  return operand < 8 ? operand : (state >> (3 * (operand - 8))) & 7;
}
bool sat(int memory) {
  int a = memory & 7, b = (memory >> 3) & 7, c = memory >> 6;
  int positive = a + 8 * (b % 2), negative = b / 2 + 4 * c;
  return !(positive & negative) && negative != 15;
}
struct Path {
  int sequence;
  bool answer;
};
struct Candidate {
  Graph g;
  int start;
};
struct Pattern {
  vector<int> data;
  array<bitset<1024>, 2> graphs;
};
vector<Pattern> patterns;
map<vector<int>, int> sequence_ids;
vector<Candidate> graphs;
void paths(const Graph &g, int pc, int steps, vector<int> &seq,
           vector<Path> &out) {
  if (pc >= 5) {
    auto it = sequence_ids.find(seq);
    if (it == sequence_ids.end()) {
      int id = patterns.size();
      it = sequence_ids.emplace(seq, id).first;
      patterns.push_back({seq, {}});
    }
    out.push_back({it->second, pc == 5});
    return;
  }
  if (!steps)
    return;
  if (pc < 3) {
    seq.push_back(pc);
    paths(g, g[pc][0], steps - 1, seq, out);
    seq.pop_back();
  } else
    for (int target : g[pc])
      paths(g, target, steps - 1, seq, out);
}
void make_graphs() {
  Graph g{};
  for (int q = 0; q < 125; q++) {
    for (int i = 0, t = q; i < 3; i++, t /= 5)
      g[i] = {t % 5, t % 5};
    for (int a = 0; a < 7; a++)
      for (int b = a + 1; b < 7; b++)
        for (int c = 0; c < 7; c++)
          for (int d = c + 1; d < 7; d++) {
            g[3] = {a, b};
            g[4] = {c, d};
            for (int start = 0; start < 5; start++) {
              int pc = start;
              for (int z = 0; z < 6 && pc < 3; z++)
                pc = g[pc][0];
              if (pc != 3)
                continue;
              int reach = 1 << start, before;
              do {
                before = reach;
                for (int i = 0; i < 5; i++)
                  if (reach >> i & 1)
                    for (int j : g[i])
                      reach |= 1 << j;
              } while (before != reach);
              if ((reach & 96) != 96)
                continue;
              vector<Path> p;
              vector<int> seq;
              paths(g, start, 8, seq, p);
              if (!std::any_of(p.begin(), p.end(), [](auto &r) {
                    return r.answer &&
                           std::count_if(patterns[r.sequence].data.begin(),
                                         patterns[r.sequence].data.end(),
                                         [](int x) { return x < 2; }) >= 3;
                  }))
                continue;
              int idx = graphs.size();
              assert(idx < 1024);
              graphs.push_back({g, start});
              for (auto &t : p)
                patterns[t.sequence].graphs[t.answer].set(idx);
            }
          }
  }
}
// Input word i is compulsory if changing only that word can flip the verdict.
int required[256]{};
vector<int> inputs;
void make_trials() {
  for (int m = 0; m < 256; m++)
    for (int i = 0; i < 3; i++)
      for (int n = 0; n < (i == 2 ? 4 : 8); n++)
        if (sat(m) != sat((m & ~(7 << (3 * i))) | (n << (3 * i))))
          required[m] |= 1 << i;
  for (int i = 0; i < 256; i++)
    inputs.push_back(i);
  // Order affects only when a failing trial is found.
  std::sort(inputs.begin(), inputs.end(), [](int a, int b) {
    return bitset<3>(required[a]).count() > bitset<3>(required[b]).count();
  });
}
struct Palette {
  int addresses[2], destinations[3];
  const Lookup *function;
};
int data_step(const Palette &p, int site, int mem, int &z) {
  int v, see = 0;
  if (site == 2)
    v = (*p.function)[z];
  else {
    int a = p.addresses[site] < 4 ? p.addresses[site]
                                  : (z >> (3 * (p.addresses[site] - 4))) & 7;
    v = a < 3 ? (mem >> (3 * a)) & 7 : 0;
    if (a < 3)
      see = 1 << a;
  }
  int k = p.destinations[site] * 3;
  z = (z & ~(7 << k)) | (v << k);
  return see;
}
vector<Lookup> comparison_tables(int r) {
  int states = 1 << (3 * r);
  set<Lookup> distinct;
  for (int i = 0; i < 8 + r; i++)
    for (int j = 0; j < 8 + r; j++)
      for (int o = 14; o < 20; o++) {
        Lookup l{};
        for (int z = 0; z < states; z++)
          l[z] = operation(o, source(i, z), source(j, z));
        distinct.insert(l);
      }
  return {distinct.begin(), distinct.end()};
}
bool works(const Palette &p, const Candidate &c, const Lookup &u,
           const Lookup &v, int m) {
  int pc = c.start, z = 0;
  for (int t = 0; t < 8 && pc < 5; t++) {
    int take = 0;
    if (pc < 3)
      data_step(p, pc, m, z);
    else
      take = (pc == 3 ? u : v)[z];
    pc = c.g[pc][take];
  }
  return pc == (sat(m) ? 5 : 6);
}

// Permit independent branch choices per input during this necessary-condition
// filter.
bitset<1024> filter(const Palette &p) {
  bitset<1024> keep;
  for (int i = 0; i < (int)graphs.size(); i++)
    keep.set(i);
  for (int m : inputs) {
    int need = required[m], ans = sat(m);
    if (!need)
      continue;
    bitset<1024> ok;
    for (auto &pat : patterns) {
      if ((pat.graphs[ans] & keep).none())
        continue;
      int z = 0, see = 0;
      for (int j : pat.data)
        see |= data_step(p, j, m, z);
      if ((see & need) == need)
        ok |= pat.graphs[ans];
    }
    keep &= ok;
    if (keep.none())
      break;
  }
  return keep;
}
void run_alias(int idx) {
  long long total = 0, survivors = 0, pairs = 0, programs = 0;
  int alias[5][3] = {{0, 0, 0}, {0, 0, 1}, {0, 1, 0}, {0, 1, 1}, {0, 1, 2}};
  auto d = alias[idx];
  int r = *std::max_element(d, d + 3) + 1, states = 1 << (3 * r);
  set<Lookup> fns;
  for (int a = 0; a < 8 + r; a++)
    for (int b = 0; b < 8 + r; b++)
      for (int opi = 0; opi < 20; opi++) {
        Lookup l{};
        for (int z = 0; z < states; z++)
          l[z] = operation(opi, source(a, z), source(b, z)) & 7;
        fns.insert(l);
      }
  vector<Lookup> luts(fns.begin(), fns.end());
  auto preds = comparison_tables(r);
  for (int a = 0; a < 4 + r; a++)
    for (int b = 0; b < 4 + r; b++) {
      if (a < 4 && b < 4)
        continue;
      for (int function_index = 0; function_index < (int)luts.size();
           function_index++) {
        Palette p{{a, b}, {d[0], d[1], d[2]}, &luts[function_index]};
        total++;
        auto k = filter(p);
        if (k.any()) {
          survivors++;
          pairs += k.count();
        }
        for (int gi = 0; gi < (int)graphs.size(); gi++) {
          if (!k[gi])
            continue;
          for (const auto &u : preds)
            for (const auto &v : preds) {
              ++programs;
              bool correct =
                  std::all_of(inputs.begin(), inputs.end(), [&](int input) {
                    return works(p, graphs[gi], u, v, input);
                  });
              if (correct) {
                std::fprintf(stderr, "Unexpected fitting program in alias %d\n",
                             idx);
                std::abort();
              }
            }
        }
      }
    }
  static const long long checks[] = {124416, 8576000, 3014400, 3014400,
                                     35552880};
  assert(programs == checks[idx]);
  std::printf(
      "alias %d: %lld data palettes, %lld live, %lld graph/palette pairs, "
      "%zu predicates, %lld realizations, no solutions\n",
      idx, total, survivors, pairs, preds.size(), programs);
}

// Three distinct original LOADs and one spare data instruction before a
// terminal comparison.
namespace acyclic {
using Word = std::array<uint8_t, 256>;
using Mem = std::array<Word, 8>;
std::array<Word, 12> reg{};
Word target{};
int base = 4 + 8 * 4 + 64 * 2;
long long paths = 0, win = 0;
int other;
void finish(int nr) {
  paths++;
  for (int i = 0; i < nr; i++)
    for (int j = 0; j < i; j++)
      for (int code = 14; code < 17; code++)
        for (bool swap : {false, true}) {
          int a = swap ? j : i, b = swap ? i : j;
          int expectation = operation(code, reg[a][base], reg[b][base]);
          bool ok = true;
          for (int x = 0; x < 256 && ok; x++)
            ok = ((operation(code, reg[a][x], reg[b][x]) == expectation) ==
                  bool(target[x]));
          if (ok)
            win++;
        }
}
void walk(int nr, int seen, bool extra, const Mem &mem, int writes) {
  if (seen == 7 && extra) {
    finish(nr);
    return;
  }
  if (nr < 8 || nr >= static_cast<int>(reg.size()))
    std::abort();
  if (seen != 7) {
    for (int i = 0; i < nr; i++) {
      int a = reg[i][base];
      if (a >= 3 || ((seen | writes) >> a & 1))
        continue;
      for (int x = 0; x < 256; x++)
        reg[nr][x] = mem[reg[i][x]][x];
      walk(nr + 1, seen | (1 << a), extra, mem, writes);
    }
  }
  if (!extra) {
    if (other == 0) {
      for (int i = 0; i < nr; i++)
        for (int j = 0; j < nr; j++)
          for (int code = 0; code < 20; code++) {
            for (int x = 0; x < 256; x++)
              reg[nr][x] = operation(code, reg[i][x], reg[j][x]) & 7;
            if (std::find(reg.begin(), reg.begin() + nr, reg[nr]) !=
                reg.begin() + nr)
              continue;
            walk(nr + 1, seen, true, mem, writes);
          }
    } else {
      for (int i = 0; i < nr; i++)
        for (int j = 0; j < nr; j++) {
          Mem changed = mem;
          for (int x = 0; x < 256; x++)
            changed[reg[i][x]][x] = reg[j][x];
          if (changed == mem)
            continue;
          walk(nr, seen, true, changed, writes | (1 << reg[i][base]));
        }
    }
  }
}
void run() {
  Mem mem{};
  for (int i = 0; i < 8; i++)
    reg[i].fill(i);
  for (int x = 0; x < 256; x++) {
    mem[0][x] = x & 7;
    mem[1][x] = (x >> 3) & 7;
    mem[2][x] = x >> 6;
    target[x] = sat(x);
  }
  for (other = 0; other <= 1; other++) {
    paths = 0;
    win = 0;
    walk(8, 0, false, mem, 0);
    std::printf("%s paths %lld, solutions %lld\n", other ? "STORE" : "ALU",
                paths, win);
    if (win || paths != (other ? 1728 : 10978))
      std::abort();
  }
}

} // namespace acyclic
} // namespace eight_bit
int main() {
  using namespace eight_bit;
  make_graphs();
  make_trials();
  assert(graphs.size() == 734);
  for (int alias = 0; alias < 5; ++alias)
    run_alias(alias);
  acyclic::run();
}
