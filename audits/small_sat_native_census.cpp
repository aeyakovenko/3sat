// Direct census independent of the Python first-occurrence dynamic program.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>

int main() {
    std::array<unsigned, 8> input{};
    constexpr unsigned n = 144;
    unsigned best = 0, least = 1000;
    std::uint64_t sat = 0, overtime = 0, record = 0;
    for (unsigned code = 0; code < (1u << 24); ++code) {
        for (unsigned i = 0; i < 8; ++i)
            input[i] = (code >> (3 * i)) & 7;
        unsigned t = 7 + 6 * 8 + 1 + 1 + 1;
        bool accepts = false;
        for (unsigned trial = 0; trial < 8; ++trial) {
            ++t;
            unsigned i = 0;
            for (; i < 8; ++i) {
                t += 4;
                if (input[i] == trial)
                    break;
                t += 2;
            }
            if (i == 8) {
                t += 2;
                accepts = true;
                break;
            }
            t += 2;
        }
        if (!accepts)
            ++t;
        sat += accepts;
        overtime += t > n;
        least = std::min(least, t);
        if (t > best) {
            best = t;
            record = 0;
        }
        record += t == best;
    }
    assert(sat == (1u << 24) - 40320 && best == 320 && record == 5040);
    std::cout << "ordered inputs " << (1u << 24) << ", SAT " << sat
              << ", over 144 steps " << overtime << ", min " << least
              << ", max " << best << ", maximizers " << record << '\n';
}
