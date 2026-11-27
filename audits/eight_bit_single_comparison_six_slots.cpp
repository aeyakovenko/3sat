// A fixed 32-input test for every native data prefix of at most five sites.
// Requires GCC or Clang vector extensions. Compile in C++20 mode.
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <unordered_set>

#include <algorithm>
using Byte = unsigned char;
using V = Byte __attribute__((vector_size(32)));
using S = signed char __attribute__((vector_size(32)));
struct Row {
  V x;
  bool operator==(const Row &b) const { return !std::memcmp(&x, &b.x, 32); }
};
struct Hash {
  size_t operator()(const Row &a) const {
    uint64_t b[4];
    std::memcpy(b, &a, 32);
    return (b[0] + b[1] * 0x9e3779b97f4a7c15ULL) ^
           (b[2] * 0xc2b2ae3d27d4eb4fULL + b[3] * 0x27d4eb2f165667c5ULL);
  }
};
using Mem = std::array<Row, 8>;
Row reg[16], truth;
int inputs[32];
long long prefixes[6]{}, checks = 0, solutions = 0;
bool satisfiable(int x) {
  int p = x & 15, m = x >> 4;
  return !(p & m) && m != 15;
}
Row alu(int i, Row x, Row y) {
  V a = x.x, b = y.x, c = b % 3, as = a ^ 4, bs = b ^ 4;
  S ss = (S)((a ^ 4) - 4);
  V v;
  switch (i) {
  case 0:
    v = a & b;
    break;
  case 1:
    v = a | b;
    break;
  case 2:
    v = a ^ b;
    break;
  case 3:
    v = a + b;
    break;
  case 4:
    v = a - b;
    break;
  case 5:
    v = a * b;
    break;
  case 6:
    v = a << b;
    break;
  case 7:
    v = a >> b;
    break;
  case 8:
    v = (V)(ss >> b);
    break;
  case 9:
    v = a << c;
    break;
  case 10:
    v = a >> c;
    break;
  case 11:
    v = (V)(ss >> c);
    break;
  case 12:
    v = (a << c) | (a >> (3 - c));
    break;
  case 13:
    v = (a >> c) | (a << (3 - c));
    break;
  case 14:
    v = (a == b) & 1;
    break;
  case 15:
    v = (a < b) & 1;
    break;
  case 16:
    v = (as < bs) & 1;
    break;
  case 17:
    v = (a != b) & 1;
    break;
  case 18:
    v = (a >= b) & 1;
    break;
  default:
    v = (as >= bs) & 1;
  }
  return {v & 7};
}
// All writable results can use a previously unused register.
bool contains(int n, Row v) { return std::find(reg, reg + n, v) != reg + n; }
// A fixed branch may assign either verdict to its true successor.
bool test(V p) {
  Row fold{p ^ (p[0] ^ truth.x[0])};
  return fold == truth;
}
bool terminal(int n) {
  checks++;
  V a = reg[n - 1].x, as = a ^ 4;
  for (int i = 0; i < n - 1; i++) {
    V b = reg[i].x, bs = b ^ 4;
    if (test(a == b) || test(a < b) || test(b < a) || test(as < bs) ||
        test(bs < as))
      return true;
  }
  return false;
}
// `seen` records the original cells loaded on test zero. Any program correct
// on the first four tests reads all three before returning its verdict.
void walk(int n, int seen, int depth, const Mem &mem, bool last_reg) {
  assert(n <= 8 + depth && depth <= 5);
  prefixes[depth]++;
  if (seen == 7 && last_reg && terminal(n)) {
    solutions++;
    return;
  }
  if (depth == 5)
    return;
  int missing = 3 - __builtin_popcount(unsigned(seen));
  bool spare = 5 - depth > missing;
  for (int i = 0; i < n; i++) {
    int addr = reg[i].x[0];
    bool fresh = addr < 3 && !(seen >> addr & 1);
    if (!fresh && !spare)
      continue;
    Row v;
    for (int j = 0; j < 32; j++)
      v.x[j] = mem[reg[i].x[j]].x[j];
    if (contains(n, v))
      continue;
    reg[n] = v;
    walk(n + 1, fresh ? seen | (1 << addr) : seen, depth + 1, mem, true);
  }
  // A nonload cannot collect a required original cell.
  if (!spare)
    return;
  std::unordered_set<Row, Hash> results;
  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++) {
      if (i < 8 && j < 8)
        continue;
      for (int op = 0; op < 20; op++) {
        Row v = alu(op, reg[i], reg[j]);
        if (contains(n, v) || !results.insert(v).second)
          continue;
        reg[n] = v;
        walk(n + 1, seen, depth + 1, mem, true);
      }
    }
  // A final STORE cannot affect the terminal comparison.
  if (depth >= 4)
    return;
  for (int i = 0; i < n; i++) {
    int addr = reg[i].x[0];
    if (addr < 3 && !(seen >> addr & 1))
      continue;
    for (int j = 0; j < n; j++) {
      Mem changed = mem;
      for (int k = 0; k < 32; k++)
        changed[reg[i].x[k]].x[k] = reg[j].x[k];
      if (changed != mem)
        walk(n, seen, depth + 1, changed, false);
    }
  }
}
int main() {
  constexpr int tests[32] = {164, 166, 172, 228, 42,  28,  64,  35,
                             5,   194, 138, 33,  150, 220, 139, 3,
                             34,  143, 176, 97,  240, 196, 78,  59,
                             152, 30,  22,  245, 47,  77,  180, 252};
  std::copy(tests, tests + 32, inputs);
  assert(satisfiable(inputs[0]) && !satisfiable(inputs[1]) &&
         !satisfiable(inputs[2]) && !satisfiable(inputs[3]));
  Mem memory{};
  for (int i = 0; i < 8; i++)
    for (int j = 0; j < 32; j++)
      reg[i].x[j] = i;
  for (int j = 0; j < 32; j++) {
    int x = inputs[j];
    truth.x[j] = satisfiable(x) ? 255 : 0;
    for (int a = 0; a < 3; a++)
      memory[a].x[j] = (x >> (3 * a)) & 7;
    printf("%d ", x);
  }
  puts("");
  walk(8, 0, 0, memory, false);
  for (int i = 0; i <= 5; i++)
    printf("depth %d prefixes %lld\n", i, prefixes[i]);
  printf("comparisons on last result %lld matching prefixes %lld\n", checks,
         solutions);
  return solutions != 0;
}
