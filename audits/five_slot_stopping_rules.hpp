#pragma once
#include <array>
#include <cstdint>
#include <vector>

inline int sw(int x) { return x < 8 ? x : x - 16; }
inline int sar(int x, int b) {
  int v = sw(x), d = 1 << b;
  return v >= 0 ? v / d : -((-v + d - 1) / d);
}
inline int operation(int op, int a, int b) {
  switch (op) {
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
    return sar(a, b);
  case 9:
    return a << (b % 4);
  case 10:
    return a >> (b % 4);
  case 11:
    return sar(a, b % 4);
  case 12:
    return (a << (b % 4)) | (a >> (4 - b % 4));
  case 13:
    return (a >> (b % 4)) | (a << (4 - b % 4));
  case 14:
    return a == b;
  case 15:
    return a < b;
  case 16:
    return sw(a) < sw(b);
  case 17:
    return a != b;
  case 18:
    return a >= b;
  default:
    return sw(a) >= sw(b);
  }
}
struct Trial {
  std::uint64_t input;
  bool answer;
};
inline Trial challenge(int p, int q, int n, int m) {
  return {std::uint64_t(p + 16 * q + 256 * n + 4096 * m),
          !(p & n) && !(q & m) && (n != 15 || m != 15)};
}

// If opposite answers reach the same first undecided register observation,
// the only valid stationary action there is to continue.
template <std::size_t capacity, class Machine>
bool fits_stopping_rule(const Machine &machine,
                        const std::vector<Trial> &suite) {
  std::vector<std::vector<unsigned short>> paths;
  std::vector<std::size_t> cursor(suite.size(), 0);
  for (auto test : suite)
    paths.push_back(machine.observations(test.input));
  static std::array<std::uint64_t, capacity> forced{};
  static std::uint64_t epoch = 0;
  static std::array<unsigned char, capacity> votes{};
  ++epoch;
  std::vector<unsigned> touched;
  while (true) {
    bool good = true;
    for (std::size_t i = 0; i < suite.size(); ++i) {
      auto &j = cursor[i];
      const auto &seq = paths[i];
      while (j < seq.size() && forced[seq[j]] == epoch)
        ++j;
      if (j == seq.size()) {
        good = false;
        break;
      }
      unsigned id = seq[j];
      if (votes[id] == 0)
        touched.push_back(id);
      votes[id] |= suite[i].answer ? 1 : 2;
    }
    bool change = false;
    for (unsigned id : touched) {
      if (votes[id] == 3) {
        forced[id] = epoch;
        change = true;
      }
      votes[id] = 0;
    }
    if (!good || !change)
      return good;
    touched.clear();
  }
}
