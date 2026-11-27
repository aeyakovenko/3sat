// Compile with c++ -O3 -std=c++17. Each column of a table is one program input.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>

using Table = std::array<std::uint8_t, 16>;
using Registers = std::array<Table, 4>;

enum class Op { And, Or, Xor, Add, Sub, ReverseSub, Mul, ShiftRight, ShiftLeft };
constexpr std::array operations{Op::And, Op::Or, Op::Xor, Op::Add, Op::Sub,
                                Op::ReverseSub, Op::Mul, Op::ShiftRight, Op::ShiftLeft};

Table constant(unsigned value) {
    Table result;
    result.fill(static_cast<std::uint8_t>(value));
    return result;
}

template <class F> Table binary(const Table& left, const Table& right, F op) {
    Table result;
    for (unsigned input = 0; input < result.size(); ++input)
        result[input] = op(unsigned(left[input]), unsigned(right[input])) & 15U;
    return result;
}

Table evaluate(Op op, const Table& a, const Table& b) {
    switch (op) {
        case Op::And: return binary(a, b, [](auto x, auto y) { return x & y; });
        case Op::Or: return binary(a, b, [](auto x, auto y) { return x | y; });
        case Op::Xor: return binary(a, b, [](auto x, auto y) { return x ^ y; });
        case Op::Add: return binary(a, b, [](auto x, auto y) { return x + y; });
        case Op::Sub: return binary(a, b, [](auto x, auto y) { return x - y; });
        case Op::ReverseSub: return binary(a, b, [](auto x, auto y) { return y - x; });
        case Op::Mul: return binary(a, b, [](auto x, auto y) { return x * y; });
        case Op::ShiftRight: return binary(a, b, [](auto x, auto k) { return x >> k; });
        case Op::ShiftLeft: return binary(a, b, [](auto x, auto k) { return x << k; });
    }
    std::abort();
}

bool formula_satisfiable(unsigned packed) {
    for (unsigned assignment = 0; assignment < 4; ++assignment) {
        bool a = assignment & 1, b = assignment & 2;
        if ((a || b) && (!(packed & 1) || a) && (!(packed & 2) || !a) &&
            (!(packed & 4) || b) && (!(packed & 8) || !b)) return true;
    }
    return false;
}

struct Census {
    Table target;
    std::array<Table, 16> literals;
    std::uint64_t tested = 0, solved = 0;

    bool comparator_works(const Table& a, const Table& b) const {
        // The first input determines whether EQ or NE could realize the table.
        bool use_equal = ((a[0] == b[0]) == bool(target[0]));
        for (unsigned input = 1; input < 16; ++input)
            if (((a[input] == b[input]) == use_equal) != bool(target[input])) return false;
        return true;
    }

    void enumerate(Registers& regs, unsigned depth, unsigned budget) {
        if (depth == budget) {
            ++tested;
            const Table& last = regs[depth];
            // A literal tested for equality on all SAT (resp. UNSAT) inputs
            // must be its value at packed=0 (resp. 3).
            bool win = comparator_works(last, literals[last[0]]) ||
                       comparator_works(last, literals[last[3]]);
            for (unsigned i = 0; i < depth && !win; ++i)
                win = comparator_works(last, regs[i]);
            solved += win;
            return;
        }
        for (unsigned i = 0; i <= depth; ++i) {
            for (unsigned j = 0; j <= 16 + i; ++j) {
                const Table& right = j < 16 ? literals[j] : regs[j - 16];
                for (Op op : operations) {
                    bool shift = op == Op::ShiftLeft || op == Op::ShiftRight;
                    if (shift && (j == 0 || j > 3)) continue;
                    Table next = evaluate(op, regs[i], right);
                    if (next == literals[next[0]]) continue;
                    auto end = regs.begin() + depth + 1;
                    if (std::find(regs.begin(), end, next) != end) continue;
                    regs[depth + 1] = next;
                    enumerate(regs, depth + 1, budget);
                }
            }
        }
    }
};

int main() {
    Census census{};
    Registers regs{};
    for (unsigned x = 0; x < 16; ++x) {
        regs[0][x] = x;
        census.literals[x] = constant(x);
        census.target[x] = formula_satisfiable(x);
    }
    for (unsigned depth = 0; depth <= 3; ++depth) {
        census.tested = census.solved = 0;
        census.enumerate(regs, 0, depth);
        std::cout << depth << " data instructions: " << census.tested
                  << " candidates, " << census.solved << " solutions\n";
        if (census.solved) return 1;
    }
    const auto& x = regs[0];
    Table r1 = evaluate(Op::Xor, x, constant(1));
    Table r2 = evaluate(Op::And, x, constant(10));
    Table r3 = evaluate(Op::Sub, constant(2), r1);
    Table r4 = evaluate(Op::And, r3, r2);
    for (unsigned i = 0; i < 16; ++i)
        if ((r4[i] == r2[i]) != bool(census.target[i])) return 1;
    std::cout << "Four data instructions and EQ give the correct decision on all 16 formulas.\n";
}
