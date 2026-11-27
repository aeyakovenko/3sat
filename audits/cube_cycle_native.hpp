// Cube-cycle catalog: scalar four-bit native RAM operations (independent implementation).
// The tables are compared with cube_cycle_native_model.py (python3 cube_cycle_native_model.py --dump)
// by every program that includes this header and is given the dump.
#pragma once
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

namespace r13 {

enum Alu { And, Or, Xor, Add, Sub, Mul, Shl, Shr, Sar, ShlMod, ShrMod, SarMod, Rol, Ror, Eq, Lt, Slt, Ne, Ge, Sge, NALU };
static const char *ALU_NAME[NALU] = {"and", "or", "xor", "add", "sub", "mul", "shl", "shr", "sar", "shlmod",
                                     "shrmod", "sarmod", "rol", "ror", "eq", "lt", "slt", "ne", "ge", "sge"};
enum Br { BEq, BLt, BSlt, NBR };
static const char *BR_NAME[NBR] = {"eq", "lt", "slt"};

inline int sgn(int a) { return (a & 8) ? a - 16 : a; }

inline int alu(int f, int a, int b) {
  int k = b & 3;
  int fill = (a & 8) ? 15 : 0;
  switch (f) {
  case And: return a & b;
  case Or: return a | b;
  case Xor: return a ^ b;
  case Add: return (a + b) & 15;
  case Sub: return (a - b) & 15;
  case Mul: return (a * b) & 15;
  case Shl: return b >= 4 ? 0 : (a << b) & 15;
  case Shr: return b >= 4 ? 0 : a >> b;
  case Sar: return b >= 4 ? fill : ((a >> b) | (fill << (4 - b))) & 15;
  case ShlMod: return (a << k) & 15;
  case ShrMod: return a >> k;
  case SarMod: return ((a >> k) | (fill << (4 - k))) & 15;
  case Rol: return ((a << k) | (a >> (4 - k))) & 15;
  case Ror: return ((a >> k) | (a << (4 - k))) & 15;
  case Eq: return a == b;
  case Lt: return a < b;
  case Slt: return sgn(a) < sgn(b);
  case Ne: return a != b;
  case Ge: return a >= b;
  case Sge: return sgn(a) >= sgn(b);
  }
  std::abort();
}

inline bool br(int f, int a, int b) {
  switch (f) {
  case BEq: return a == b;
  case BLt: return a < b;
  case BSlt: return sgn(a) < sgn(b);
  }
  std::abort();
}

struct Tables {
  uint8_t op[NALU][16][16];
  uint8_t cmp[NBR][16][16];
  Tables() {
    for (int f = 0; f < NALU; ++f)
      for (int a = 0; a < 16; ++a)
        for (int b = 0; b < 16; ++b) op[f][a][b] = (uint8_t)alu(f, a, b);
    for (int f = 0; f < NBR; ++f)
      for (int a = 0; a < 16; ++a)
        for (int b = 0; b < 16; ++b) cmp[f][a][b] = br(f, a, b);
  }
};

// Compare with the JSON dump of cube_cycle_native_model.py.  The dump is a flat JSON object
// {"alu": {name: [[..16..] x16]}, "branch": {...}, "order": [...]}; we only need the
// integers in order of appearance after each quoted name.
inline std::vector<int> ints_after(const std::string &text, const std::string &key, int count) {
  std::vector<int> out;
  size_t pos = text.find("\"" + key + "\": [[");
  if (pos == std::string::npos) return out;
  pos += key.size() + 4;
  while ((int)out.size() < count && pos < text.size()) {
    if (text[pos] >= '0' && text[pos] <= '9') {
      int v = 0;
      while (pos < text.size() && text[pos] >= '0' && text[pos] <= '9') v = 10 * v + (text[pos++] - '0');
      out.push_back(v);
    } else {
      ++pos;
    }
  }
  return out;
}

inline int check_against_dump(const Tables &t, const char *path) {
  std::ifstream in(path);
  if (!in) {
    std::fprintf(stderr, "cannot open table dump %s\n", path);
    std::exit(2);
  }
  std::stringstream ss;
  ss << in.rdbuf();
  std::string text = ss.str();
  size_t alu_pos = text.find("\"alu\"");
  size_t br_pos = text.find("\"branch\"");
  if (alu_pos == std::string::npos || br_pos == std::string::npos) std::exit(2);
  std::string alu_text = text.substr(alu_pos, br_pos - alu_pos), br_text = text.substr(br_pos);
  int n = 0;
  for (int f = 0; f < NALU; ++f) {
    auto v = ints_after(alu_text, ALU_NAME[f], 256);
    if (v.size() != 256) std::exit(2);
    for (int a = 0; a < 16; ++a)
      for (int b = 0; b < 16; ++b, ++n)
        if (v[16 * a + b] != t.op[f][a][b]) {
          std::fprintf(stderr, "ALU table mismatch %s %d %d\n", ALU_NAME[f], a, b);
          std::exit(2);
        }
  }
  for (int f = 0; f < NBR; ++f) {
    auto v = ints_after(br_text, BR_NAME[f], 256);
    if (v.size() != 256) std::exit(2);
    for (int a = 0; a < 16; ++a)
      for (int b = 0; b < 16; ++b, ++n)
        if (v[16 * a + b] != t.cmp[f][a][b]) {
          std::fprintf(stderr, "branch table mismatch %s %d %d\n", BR_NAME[f], a, b);
          std::exit(2);
        }
  }
  return n;
}

inline bool is_cover(int mask) {
  int rot = ((mask << 1) & 0xffff) | (mask >> 15);
  return (mask | rot) == 0xffff;
}
inline int word_of(int mask, int i) { return (mask >> (4 * i)) & 15; }

}  // namespace r13
