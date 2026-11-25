// Exhaust five-slot four-bit RAM programs having one LOAD, one STORE and one
// ALU. g++ -std=c++17 -O3 one_load_one_store_five_slots.cpp -o /tmp/store-slots
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>
using Mem = std::uint64_t;
using Table = std::array<std::uint8_t, 256>;
int word(int id, int l, int u) { return id < 16 ? id : id == 16 ? l : u; }
#include "five_slot_stopping_rules.hpp"
// Dirty bits mark original cells overwritten since entry; used bits count reads
// before that.
struct Data {
  Mem mem;
  unsigned l, u, dirty, used;
  bool operator==(const Data &other) const {
    return mem == other.mem && l == other.l && u == other.u &&
           dirty == other.dirty && used == other.used;
  }
};
struct Program {
  const Table &tab;
  int addr, val;
  std::array<int, 3> code;
  int period;
  bool pre, same, self;
  void store(Data &s) const {
    int a = word(addr, s.l, s.u), b = word(val, s.l, s.u);
    s.mem = (s.mem & ~(Mem{15} << (4 * a))) | (Mem(b) << (4 * a));
    if (a < 4)
      s.dirty |= 1u << a;
  }
  void step(Data &s, int pos) const {
    switch (code[pos]) {
    case 0: {
      unsigned a = self ? s.l : s.u;
      if (a < 4 && !(s.dirty & (1u << a)))
        s.used |= 1u << a;
      s.l = (s.mem >> (4 * a)) & 15;
      break;
    }
    case 1:
      if (same)
        s.l = tab[s.l];
      else
        s.u = tab[s.l + 16 * s.u];
      break;
    case 2:
      store(s);
      break;
    }
  }
  Data start(Mem input) const {
    Data s{input, 0, 0, 0, 0};
    if (pre)
      store(s);
    return s;
  }
  // Brent repetition at a fixed phase, including memory and both tracking
  // masks.
  bool reads(Mem input) const {
    Data s = start(input), old = s;
    std::uint64_t power = 1, count = 0;
    while (true) {
      for (int t = 0; t < period; ++t)
        step(s, t);
      if (s.used == 15)
        return true;
      if (s == old)
        return false;
      if (++count == power) {
        old = s;
        count = 0;
        power *= 2;
      }
    }
  }
  // A repeated observation cannot become the first available exit.
  std::vector<unsigned short> observations(Mem input) const {
    std::array<bool, 768> seen{};
    std::vector<unsigned short> out;
    Data s = start(input), old = s;
    std::uint64_t power = 1, count = 0;
    while (true) {
      for (int t = 0; t < period; ++t) {
        step(s, t);
        unsigned z = t * 256 + s.l + 16 * s.u;
        if (!seen[z]) {
          seen[z] = true;
          out.push_back(z);
        }
      }
      if (s == old)
        return out;
      if (++count == power) {
        old = s;
        count = 0;
        power *= 2;
      }
    }
  }
};
void audit(int mode) {
  bool same = mode == 0, self = mode < 2;
  int range = same ? 17 : 18;
  std::set<Table> tabs;
  for (int a = 0; a < range; a++)
    for (int b = 0; b < range; b++)
      for (int op = 0; op < 20; op++) {
        Table t{};
        for (int z = 0; z < (same ? 16 : 256); z++)
          t[z] =
              operation(op, word(a, z % 16, z / 16), word(b, z % 16, z / 16)) &
              15;
        tabs.insert(t);
      }
  std::vector<Trial> high, tiny;
  for (int p = 4; p < 16; p++)
    for (int q = 4; q < 16; q++)
      for (int n = 4; n < 16; n++)
        for (int m = 4; m < 16; m++)
          if (!(p & n) && !(q & m))
            high.push_back(challenge(p, q, n, m));
  for (int p = 0; p < 2; p++)
    for (int q = 0; q < 2; q++)
      for (int n = 0; n < 2; n++)
        for (int m = 0; m < 2; m++)
          tiny.push_back(challenge(p, q, n, m));
  assert(high.size() == 324 && tiny.size() == 16);
  // A cyclic address counter reads all four original cells on the sparse
  // witnesses. The stronger stopping model can compute a nonconstant property
  // of those cells.
  Table counter{};
  for (unsigned z = 0; z < 256; ++z)
    counter[z] = ((z >> 4) + 1) & 15;
  Program scan{counter, 15, 0, {0, 1, 2}, 2, true, false, false};
  for (auto row : high)
    assert(scan.reads(row.input));
  auto easy = tiny;
  for (auto &row : easy)
    row.answer = (row.input & 1) != 0;
  assert(fits_stopping_rule<768>(scan, easy));
  assert(!fits_stopping_rule<768>(scan, tiny));
  unsigned ncase = 0, nread = 0, ntiny = 0;
  for (const auto &tab : tabs)
    for (int a = 0; a < range; a++)
      for (int b = 0; b < range; b++) {
        std::array<int, 3> order = {0, 1, 2};
        do {
          for (int pre = 0; pre <= 1; pre++) {
            if (pre && order[2] != 2)
              continue;
            Program g{tab, a, b, order, pre ? 2 : 3, bool(pre), same, self};
            ncase++;
            bool ok = true;
            for (auto row : high)
              if (!g.reads(row.input)) {
                ok = false;
                break;
              }
            if (!ok)
              continue;
            nread++;
            if (fits_stopping_rule<768>(g, tiny))
              ++ntiny;
          }
        } while (std::next_permutation(order.begin(), order.end()));
      }
  static const char *names[] = {"same register",
                                "separate, self-addressed LOAD",
                                "separate, ALU-addressed LOAD"};
  const std::array<unsigned, 3> cases{682040, 1573344, 1573344},
      read_capable{0, 10, 14740};
  assert(ncase == cases[mode] && nread == read_capable[mode] && ntiny == 0);
  std::cout << names[mode] << ": " << tabs.size() << " tables, " << ncase
            << " schedules, " << nread << " pass reads, " << ntiny
            << " fit binary verdicts\n";
}
int main() {
  for (int mode = 0; mode < 3; ++mode)
    audit(mode);
}
