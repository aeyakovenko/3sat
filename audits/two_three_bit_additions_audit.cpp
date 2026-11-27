// Exhaust the independent-first-operands case for two three-bit additions.
// Compile with c++ -std=c++20 -O2. A uint64_t stores the table on six bits.
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <unordered_set>
#include <vector>

using TruthTable = std::uint64_t;

struct LinearSpan {
    std::array<TruthTable, 64> pivots{};

    TruthTable remainder(TruthTable value) const {
        for (int i = 63; i >= 0; --i) {
            if ((value >> i) & 1) value ^= pivots[i];
        }
        return value;
    }

    void insert(TruthTable value) {
        value = remainder(value);
        if (value) pivots[std::bit_width(value) - 1] = value;
    }
};

// Cache the linear remainder map on eight byte-sized contributions.
struct ByteRemainders {
    std::array<std::array<TruthTable, 256>, 8> lookup{};

    explicit ByteRemainders(const LinearSpan& span) {
        for (int byte = 0; byte < 8; ++byte) {
            for (int part = 0; part < 256; ++part) {
                lookup[byte][part] = span.remainder(TruthTable(part) << (8 * byte));
            }
        }
    }

    TruthTable operator()(TruthTable value) const {
        TruthTable result = 0;
        for (const auto& block : lookup) {
            result ^= block[value & 255];
            value >>= 8;
        }
        return result;
    }
};

std::array<TruthTable, 9> first_stage_generators() {
    std::array<TruthTable, 9> forms{};
    forms[0] = ~TruthTable(0);
    for (int i = 0; i < 6; ++i) {
        for (int point = 0; point < 64; ++point) {
            if ((point >> i) & 1) forms[i+1] |= TruthTable(1) << point;
        }
    }
    forms[7] = forms[1] & forms[2];
    forms[8] = (forms[3] & forms[4]) ^ ((forms[3] ^ forms[4]) & forms[7]);
    return forms;
}

std::vector<TruthTable> full_rank_quadratics(const std::array<TruthTable, 9>& input) {
    std::vector<TruthTable> result;
    for (unsigned mask = 0; mask < (1u << 15); ++mask) {
        std::array<unsigned, 6> rows{};
        TruthTable quadratic = 0;
        int index = 0;
        for (int i = 0; i < 6; ++i) {
            for (int j = i + 1; j < 6; ++j, ++index) {
                if (!((mask >> index) & 1)) continue;
                rows[i] ^= 1u << j;
                rows[j] ^= 1u << i;
                quadratic ^= input[1+i] & input[1+j];
            }
        }
        LinearSpan span;
        unsigned rank = 0;
        for (unsigned row : rows) {
            if (span.remainder(row)) {
                span.insert(row);
                ++rank;
            }
        }
        if (rank == 6) result.push_back(quadratic);
    }
    return result;
}

int main() {
    const auto generators = first_stage_generators();
    std::vector<TruthTable> available{0};
    for (auto form : generators) {
        const auto original_size = available.size();
        for (std::size_t i = 0; i < original_size; ++i) {
            available.push_back(form ^ available[i]);
        }
    }
    const auto quadratics = full_rank_quadratics(generators);
    if (quadratics.size() != 13888 || available.size() != 512) return 2;

    // A scalar output of the second addition is L + p(a + uv).
    // For fixed p, L + pa ranges over the span of S and pS.
    for (TruthTable p : available) {
        LinearSpan span;
        for (auto form : generators) {
            span.insert(form);
            span.insert(p & form);
        }
        const ByteRemainders reduce(span);
        std::unordered_set<TruthTable> target;
        for (TruthTable q : quadratics) target.insert(reduce(q));
        for (std::size_t i = 0; i < available.size(); ++i) {
            TruthTable factor = p & available[i];
            for (std::size_t j = 0; j <= i; ++j) {
                if (target.contains(reduce(factor & available[j]))) {
                    std::cerr << "Rank-six quadratic reachable\n";
                    return 1;
                }
            }
        }
    }
    std::cout << "All 512 propagation forms checked against 13888 rank-six quadratics\n";
}
