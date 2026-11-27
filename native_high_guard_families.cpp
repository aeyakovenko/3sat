// Compare two native guards on the 64 complementary targets and every
// rejecting input with words 4..11. 'lookup' closes one computed register
// under read-only indirect loads; 'stores' excludes an arbitrary subset of
// the four original addresses for a computed store address.
#include "native_four_bit_planes.hpp"
#include <algorithm>
#include <bit>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

constexpr int blocks = 60; // 64 target lanes, 3,772 negative lanes and four
                           // duplicate padding lanes.
using Table = std::array<Word, blocks>;
using MaskTable = std::array<Mask, blocks>;
using Registers = std::array<Table, 24>;
constexpr Mask all = ~Mask(0);
template <class T> struct TableHash {
  std::size_t operator()(const T &t) const {
    size_t hash = 1;
    for (const auto &x : t) {
      size_t part;
      if constexpr (std::is_same_v<typename T::value_type, Word>)
        part = Hash{}(x);
      else
        part = x;
      hash ^= part + 0x9e3779b97f4a7c15ULL + (hash << 6) + (hash >> 2);
    }
    return hash;
  }
};
Registers input() {
  std::vector<int> files;
  for (int p = 4; p < 12; ++p)
    for (int q = 4; q < 12; ++q)
      files.push_back(p * 4096 + q * 256 + (15 - p) * 16 + 15 - q);
  for (int p = 4; p < 12; ++p)
    for (int q = 4; q < 12; ++q)
      for (int m = 4; m < 12; ++m)
        for (int n = 4; n < 12; ++n)
          if ((p & m) || (q & n))
            files.push_back(p * 4096 + q * 256 + m * 16 + n);
  if (files.size() != 64 + 3772)
    throw std::runtime_error("wrong suite size");
  while (files.size() < blocks * 64)
    files.push_back(files.back());
  Registers reg{};
  for (int i = 0; i < blocks * 64; ++i)
    for (int r = 0; r < 20; ++r) {
      int v = r < 16 ? r : (files[i] >> (12 - 4 * (r - 16))) & 15;
      for (int bit = 0; bit < 4; ++bit)
        reg[r][i / 64][bit] |= Mask((v >> bit) & 1) << (i % 64);
    }
  return reg;
}
void close_reads(Registers &reg) {
  for (int r = 20; r < 23; ++r)
    for (int i = 0; i < blocks; ++i) {
      Word out{};
      for (int addr = 0; addr < 4; ++addr) {
        Mask hit = equal(reg[r][i], reg[addr][i], all);
        for (int bit = 0; bit < 4; ++bit)
          out[bit] |= hit & reg[16 + addr][i][bit];
      }
      reg[r + 1][i] = out;
    }
}
bool has_pair(const Registers &reg, int available, const MaskTable &allowed,
              int threshold, std::uint64_t &counter) {
  std::vector<MaskTable> guards;
  std::unordered_set<MaskTable, TableHash<MaskTable>> distinct;
  for (int a = 0; a < available; ++a)
    for (int b = a; b < available; ++b) {
      std::array<std::array<Mask, 5>, blocks> outcomes;
      for (int i = 0; i < blocks; ++i)
        outcomes[i] = tests(reg[a][i], reg[b][i], all);
      for (int k = 0; k < 5; ++k)
        for (int inverse = 0; inverse < 2; ++inverse) {
          Mask bias = inverse ? all : 0;
          if (std::popcount((outcomes[0][k] ^ bias) & allowed[0]) < threshold)
            continue;
          MaskTable mask;
          for (int i = 0; i < blocks; ++i)
            mask[i] = (outcomes[i][k] ^ bias) & allowed[i];
          if (distinct.insert(mask).second)
            guards.push_back(mask);
        }
    }
  for (int a = 0; a < (int)guards.size(); ++a)
    for (int b = a; b < (int)guards.size(); ++b) {
      ++counter;
      const auto &x = guards[a], &y = guards[b];
      if ((x[1] & y[1]) || std::popcount(x[0] & y[0]) < threshold)
        continue;
      bool sound = true;
      for (int i = 2; i < blocks; ++i)
        if (x[i] & y[i]) {
          sound = false;
          break;
        }
      if (sound)
        return true;
    }
  return false;
}
int main(int argc, char **args) {
  if (argc != 2)
    throw std::runtime_error("choose lookup, equal, or stores");
  std::string mode = args[1];
  bool lookup = mode == "lookup";
  bool equals = mode == "equal";
  if (!lookup && !equals && mode != "stores")
    throw std::runtime_error("unknown family");
  int threshold = (lookup || equals) ? 9 : 17;
  Registers reg = input();
  std::unordered_set<Table, TableHash<Table>> seen;
  std::uint64_t pairs = 0;
  for (int a = 0; a < 20; ++a)
    for (int b = 0; b < 20; ++b)
      for (int f = 0; f < 20; ++f) {
        for (int i = 0; i < blocks; ++i)
          reg[20][i] = operation(f, reg[a][i], reg[b][i], all);
        if (!seen.insert(reg[20]).second)
          continue;
        if (lookup)
          close_reads(reg);
        for (int excluded = 0; excluded < (lookup ? 1 : (equals ? 4 : 16));
             ++excluded) {
          MaskTable allowed;
          allowed.fill(all);
          for (int i = 0; i < blocks; ++i)
            for (int addr = 0; addr < 4; ++addr)
              if (!equals && ((excluded >> addr) & 1))
                allowed[i] &= ~equal(reg[20][i], reg[addr][i], all);
          if (equals)
            for (int i = 0; i < blocks; ++i)
              allowed[i] = equal(reg[20][i], reg[excluded][i], all);
          if (has_pair(reg, lookup ? 24 : 21, allowed, threshold, pairs))
            throw std::runtime_error("a pair survives on the negative suite");
        }
      }
  std::cout << mode << ": " << seen.size() << " arithmetic tables, " << pairs
            << " guard pairs, support below " << threshold << "\n";
}
