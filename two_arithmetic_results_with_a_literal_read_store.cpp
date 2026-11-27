// Two ALUs, one store and fixed literal input reads. Find the minimum set J
// of original addresses that would have to mask every negative comparison.
#include "native_four_bit_planes.hpp"
#include <algorithm>
#include <bit>
#include <iostream>
#include <random>
#include <stdexcept>
#include <unordered_set>
#include <vector>
constexpr Mask all = ~Mask(0);
constexpr int fast = 3;
using Reg = std::array<Word, 22>;
using Key = std::array<Word, fast>;
template <class T> struct TH {
  size_t operator()(const T &x) const {
    size_t h = 1;
    for (auto &w : x)
      h ^= Hash{}(w) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    return h;
  }
};
std::vector<Reg> input;
int negcount = 0;
long long second_count = 0, full_count = 0, blocks = 0;
int val(int c, int j) { return c >> (12 - 4 * j) & 15; }
void prep() {
  std::vector<int> rows, n;
  for (int p = 4; p < 12; ++p)
    for (int q = 4; q < 12; ++q)
      rows.push_back(p * 4096 + q * 256 + (15 - p) * 16 + 15 - q);
  for (int p = 4; p < 16; ++p)
    for (int q = 4; q < 16; ++q)
      for (int m = 4; m < 16; ++m)
        for (int z = 4; z < 16; ++z)
          if ((p & m) || (q & z))
            n.push_back(p * 4096 + q * 256 + m * 16 + z);
  negcount = n.size();
  std::mt19937 g(100943);
  std::shuffle(n.begin(), n.end(), g);
  rows.insert(rows.end(), n.begin(), n.end());
  while (rows.size() % 64)
    rows.push_back(rows.back());
  input.resize(rows.size() / 64);
  for (int i = 0; i < (int)rows.size(); ++i)
    for (int r = 0; r < 20; ++r) {
      int v = r < 16 ? r : val(rows[i], r - 16);
      for (int k = 0; k < 4; ++k)
        input[i / 64][r][k] |= Mask(v >> k & 1) << (i % 64);
    }
}
bool comm(int f) {
  return f == And || f == Or || f == Xor || f == Add || f == Mul || f == Eq ||
         f == Ne;
}
std::vector<Node> opts(int m) {
  std::vector<Node> v;
  for (int a = 0; a < m; ++a)
    for (int b = 0; b < m; ++b)
      for (int f = 0; f < 20; ++f)
        if (a <= b || !comm(f))
          v.push_back({f, a, b});
  return v;
}
Word eval(const Reg &r, Node n) { return operation(n.op, r[n.a], r[n.b], all); }
using Hits = std::array<Mask, 4>;
Hits hits(const Reg &r, int addr) {
  Hits h;
  for (int j = 0; j < 4; ++j)
    h[j] = equal(r[addr], r[j], all);
  return h;
}
bool cover(Mask p, const Hits &h, int &ban) {
  Mask unionlow = h[0] | h[1] | h[2] | h[3];
  if (p & ~unionlow)
    return false;
  for (int k = 0; k < 4; ++k)
    if (p & h[k])
      ban |= 1 << k;
  return true;
}
int support(Mask p, const Hits &h, int ban) {
  for (int j = 0; j < 4; ++j)
    if (ban >> j & 1)
      p &= ~h[j];
  return std::popcount(p);
}
int main(int argc, char **argv) {
  int lo = argc > 1 ? atoi(argv[1]) : 0, hi = argc > 2 ? atoi(argv[2]) : 99999;
  prep();
  auto first = opts(20), second = opts(21);
  std::unordered_set<std::vector<Word>, TH<std::vector<Word>>> seen;
  for (auto one : first) {
    std::vector<Word> word;
    for (auto &r : input)
      word.push_back(eval(r, one));
    if (!seen.insert(word).second)
      continue;
    int idx = seen.size() - 1;
    if (idx < lo || idx >= hi)
      continue;
    for (int i = 0; i < (int)input.size(); ++i)
      input[i][20] = word[i];
    std::unordered_set<Key, TH<Key>> excluded;
    for (auto two : second) {
      Key key;
      for (int i = 0; i < fast; ++i)
        key[i] = eval(input[i], two);
      if (excluded.contains(key))
        continue;
      ++second_count;
      int filled = fast;
      std::array<std::array<Hits, 2>, fast> h;
      for (int i = 0; i < fast; ++i) {
        input[i][21] = key[i];
        for (int who = 0; who < 2; ++who)
          h[i][who] = hits(input[i], 20 + who);
      }
      bool candidate = false;
      for (int a = 0; a < 22; ++a)
        for (int b = a; b < 22; ++b) {
          std::array<std::array<Mask, 5>, fast> t;
          for (int i = 0; i < fast; ++i)
            t[i] = tests(input[i][a], input[i][b], all);
          for (int k = 0; k < 5; ++k)
            for (int inv = 0; inv < 2; ++inv) {
              Mask flip = inv ? all : 0, pos = t[0][k] ^ flip;
              if (std::popcount(pos) < 37)
                continue;
              for (int who = 0; who < 2; ++who) {
                if (!who && b != 21)
                  continue;
                int ban = 0;
                if (!cover(t[1][k] ^ flip, h[1][who], ban) ||
                    !cover(t[2][k] ^ flip, h[2][who], ban) ||
                    support(pos, h[0][who], ban) < 37)
                  continue;
                candidate = true;
                ++full_count;
                bool ok = true;
                for (int i = fast; i < (int)input.size(); ++i) {
                  auto &r = input[i];
                  if (i >= filled) {
                    r[21] = eval(r, two);
                    ++filled;
                    ++blocks;
                  }
                  Mask passed = tests(r[a], r[b], all)[k] ^ flip;
                  if (!cover(passed, hits(r, 20 + who), ban) ||
                      support(pos, h[0][who], ban) < 37) {
                    ok = false;
                    break;
                  }
                }
                if (ok) {
                  std::cout
                      << "HIGH PATH operations " << one.op << "," << one.a
                      << "," << one.b << " " << two.op << "," << two.a << ","
                      << two.b << " guard " << a << "," << b << "," << k << ","
                      << inv << " store=" << who << " avoided=" << ban
                      << " support=" << support(pos, h[0][who], ban) << "\n";
                  return 1;
                }
              }
            }
        }
      if (!candidate)
        excluded.insert(key);
    }
  }
  std::cout << "range " << lo << ".." << hi << " / " << seen.size()
            << " second " << second_count << " candidates " << full_count
            << " extended blocks " << blocks << " high negatives " << negcount
            << "\n";
}
