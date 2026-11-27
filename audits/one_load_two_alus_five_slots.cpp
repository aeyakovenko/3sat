// Exhaust the five static slots with one LOAD and two ALUs on a four-word
// catalog. g++ -std=c++17 -O3 one_load_two_alus_five_slots.cpp -o /tmp/two-alus
#include "five_slot_stopping_rules.hpp"
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <set>
#include <vector>
using LUT = std::array<uint8_t, 4096>;
int source(int id, int z) { return id < 16 ? id : (z >> (4 * (id - 16))) & 15; }
std::vector<Trial> high, tiny, low, medium;
struct Prog {
  const LUT *ab[2];
  int dst[2], addr;
  std::array<int, 3> order;
  int period, init;
  inline int apply(int z, int step, unsigned mem, int *used) const {
    int op = order[step];
    if (op == 0) {
      int a = (z >> (4 * addr)) & 15;
      if (used && a < 4)
        *used |= 1 << a;
      return (z & ~15) | (a < 4 ? ((mem >> (4 * a)) & 15) : 0);
    }
    int pos = 4 * dst[op - 1];
    return (z & ~(15 << pos)) | ((*ab[op - 1])[z] << pos);
  }
  bool reads(unsigned mem) const {
    int z = init, old = z, t = 1, c = 0, used = 0;
    for (;;) {
      for (int s = 0; s < period; s++)
        z = apply(z, s, mem, &used);
      if (used == 15)
        return true;
      if (z == old)
        return false;
      if (++c == t) {
        old = z;
        c = 0;
        t *= 2;
      }
    }
  }
  std::vector<unsigned short> observations(unsigned mem) const {
    static uint64_t seen[12288] = {}, epoch = 0;
    ++epoch;
    std::vector<unsigned short> ids;
    int z = init, old = z, t = 1, c = 0;
    for (;;) {
      for (int s = 0; s < period; s++) {
        z = apply(z, s, mem, nullptr);
        int tag = s * 4096 + z;
        if (seen[tag] != epoch) {
          ids.push_back(tag);
          seen[tag] = epoch;
        }
      }
      if (z == old)
        return ids;
      if (++c == t) {
        old = z;
        c = 0;
        t *= 2;
      }
    }
  }
};
void audit(int idx) {
  std::array<std::array<int, 2>, 5> writes{
      {{0, 0}, {0, 1}, {1, 0}, {1, 1}, {1, 2}}};
  int a = writes[idx][0], b = writes[idx][1], nr = std::max(a, b) + 1,
      words = 1 << (4 * nr);
  std::set<LUT> all;
  for (int x = 0; x < 16 + nr; x++)
    for (int y = 0; y < 16 + nr; y++)
      for (int op = 0; op < 20; op++) {
        LUT t{};
        for (int z = 0; z < words; z++)
          t[z] = operation(op, source(x, z), source(y, z)) & 15;
        all.insert(t);
      }
  std::vector<LUT> tabs(all.begin(), all.end());
  std::vector<std::array<int, 3>> dirs;
  std::array<int, 3> order{0, 1, 2};
  do {
    dirs.push_back(order);
  } while (std::next_permutation(order.begin(), order.end()));
  unsigned nc = 0, rd = 0, bi = 0, lw = 0, me = 0;
  auto run = [&](const Prog &g) {
    nc++;
    for (auto row : high)
      if (!g.reads(row.input))
        return;
    rd++;
    if (!fits_stopping_rule<12288>(g, tiny))
      return;
    bi++;
    if (!fits_stopping_rule<12288>(g, low))
      return;
    lw++;
    if (!fits_stopping_rule<12288>(g, medium))
      return;
    me++;
  };
  // Designate the two ALU sites; with a distinct second one-shot ALU, any
  // immediate register value is allowed.
  for (int addr = 0; addr < nr; addr++) {
    if (addr != a && addr != b)
      continue;
    for (auto &f : tabs)
      for (auto &h : tabs)
        for (auto ord : dirs)
          run({{&f, &h}, {a, b}, addr, ord, 3, 0});
    for (int pre = 0; pre < 2; pre++)
      for (int val = 0; val < 16; val++)
        for (auto &tb : tabs) {
          int repeat =
              2 - pre; // pre=0 => site 1 is initialized, site 2 repeats
          int initial = val << (4 * (pre ? b : a));
          std::array<int, 3> x{0, repeat, 0}, y{repeat, 0, 0};
          for (auto o : {x, y})
            run({{&tb, &tb}, {a, b}, addr, o, 2, initial});
        }
  }
  const std::array<unsigned, 5> cases = {541030, 4499084, 4499084, 2249542,
                                         10997504};
  const std::array<unsigned, 5> touched = {0, 37248, 37248, 4620, 112608};
  const std::array<unsigned, 5> bin_fit = {0, 11, 11, 0, 982};
  const std::array<unsigned, 5> low_fit = {0, 0, 0, 0, 24};
  assert(nc == cases[idx] && rd == touched[idx] && bi == bin_fit[idx] &&
         lw == low_fit[idx] && me == 0);
  std::cout << "alias " << a << b << " tables " << tabs.size() << " cases "
            << nc << " required_reads " << rd << " binary " << bi << " low "
            << lw << " medium " << me << std::endl;
}
int main() {
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
  for (int p = 0; p < 4; p++)
    for (int q = 0; q < 4; q++)
      for (int n = 0; n < 4; n++)
        for (int m = 0; m < 4; m++)
          low.push_back(challenge(p, q, n, m));
  for (int p : {0, 1, 2, 4, 5, 8, 9, 15})
    for (int q : {1, 2, 4, 5, 8})
      for (int n : {0, 1, 2, 4, 8, 9})
        for (int m : {0, 1, 2, 4, 8, 9})
          medium.push_back(challenge(p, q, n, m));
  assert(high.size() == 324 && tiny.size() == 16 && low.size() == 256 &&
         medium.size() == 1440);
  LUT increment{}, zero{};
  for (int z = 0; z < 4096; ++z)
    increment[z] = ((z >> 4) + 1) & 15;
  const Prog scan{{&increment, &zero}, {1, 2}, 1, {0, 1, 2}, 3, 0};
  for (auto row : high)
    assert(scan.reads(row.input));
  auto first_bit = tiny;
  for (auto &row : first_bit)
    row.answer = row.input & 1;
  assert(fits_stopping_rule<12288>(scan, first_bit));
  assert(!fits_stopping_rule<12288>(scan, tiny));
  for (int idx = 0; idx < 5; ++idx)
    audit(idx);
}
