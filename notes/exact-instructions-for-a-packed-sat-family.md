# An exact five-instruction SAT decision on a four-bit input

Start with the fixed clause (a∨b). Bits 0,1,2,3 of an input word say whether to adjoin, respectively, the unit clauses a, ¬a, b, ¬b. These are 16 different formulas. Every clause can be padded to width three by repeating its last literal. The encoding is a presence bitmap for this fixed catalog. For example, input 10 includes ¬a and ¬b. It is unsatisfiable even though its units alone are consistent.

**Exact minimum.** On the following machine, deciding this family needs five instructions in the worst case among straight-line programs. Four data instructions followed by a comparison suffice:

    r1 = x XOR 1
    r2 = x AND 10
    r3 = 2 SUB r1
    r4 = r3 AND r2
    return r4 == r2

Words are four bits. Each data instruction has unit cost, writes a new register and may read any earlier register, the input, or any literal from 0 through 15. Available operations are AND, OR, XOR, ADD, SUB, MUL and logical shifts by a literal 0 through 3. Arithmetic is modulo 16. A final EQ or NE between two words returns the verdict and costs one instruction. The input is already in a register. There are no intervening branches, table loads or variable shifts. The literal 10 is decimal. The model allows arbitrary reuse of intermediate registers.

## Complete lower-bound census

The checker represents each intermediate register by its 16 outputs. The target truth table comes from enumerating the four assignments to a,b for each formula. For all programs too short to meet the claimed bound it gives

| Data instructions before the branch | Candidate instruction sequences checked | Solutions |
| ---: | ---: | ---: |
| 0 | 1 | 0 |
| 1 | 111 | 0 |
| 2 | 24,366 | 0 |
| 3 | 8,085,955 | 0 |

The counts are candidate sequences after pruning; different sequences can realize the same function. A shortest program has no instruction which computes a known constant or an existing register table, since every later use could use the earlier value. Operations on constants alone can likewise be removed. The generator tries both operand orders for subtraction and immediate shifts explicitly; all other binary operations commute. The last data result must occur in the final comparison, or the instruction can be deleted. Comparing that result to another register is checked directly. For comparison against a literal there are only two possible candidates: the data value at input 0, which is SAT, and the data value at input 3, which is UNSAT. These tests cover both EQ and NE. A comparison of two literals, or a register with itself, would be constant.

The same checker verifies the displayed five-instruction program on the entire domain. Reproduce with:

    c++ -std=c++17 -O3 packed_unit_sat_synthesis.cpp -o /tmp/packed-unit-sat
    /tmp/packed-unit-sat

[Complete C++17 census](../audits/packed_unit_sat_synthesis.cpp).

## What induction on the first sizes actually gives

For one variable with fixed clause a and optional units a,¬a, the analogous two-bit machine needs exactly two instructions. Mask the negative unit's bit and compare with zero. A bare comparison of the input with a literal singles out one word or its complement, while the one-variable decision accepts exactly two of the four words.

For k variables, use one fixed disjunction of all k positive variables and optional units of either sign on each variable. The formulas admit the following exact induction. After reading a prefix of variable pairs, record one of three states:

1. Some variable has both unit signs present.
2. Units are consistent and every variable seen is forced false.
3. Units are consistent and at least one seen variable can be true.

Start in state 2. A conflicting pair of units sends every state to 1, which is absorbing. Otherwise a variable with the negative unit absent changes state 2 to 3, and state 3 persists. Only state 3 satisfies the completed formula. These are the minimum possible number of deterministic prefix states for all sizes. State 3 differs from the other two on an empty continuation; appending one variable with no units distinguishes states 1 and 2. All three states occur after just one pair of bits.

Thus the SAT verdict at size k alone cannot give the verdict at size k+1, even for this catalog: a contradiction and a consistent all-false prefix both have verdict UNSAT. The former remains UNSAT after adjoining a free variable and the latter becomes SAT. One additional distinction makes this particular induction work. For k>3 the long clause can be encoded in 3-CNF by a fixed chain of OR gates with new variables; the census itself only used the direct tiny encodings. This state minimality concerns prefix processing. It supplies no induction on the minimum number of instructions of arbitrary RAM programs, and the five-instruction result makes no asymptotic time claim for general SAT.

## The adaptive word RAM on the same 16 formulas

On an adaptive unsigned four-bit RAM the exact worst-case cost is **three instructions**. Giving branches a signed two's-complement comparison as well reduces it to **two**. A terminal leaf returns its constant verdict for free. Only the path actually taken is charged. The program may be tailored to this input catalog and the number of registers and amount of code are unrestricted.

Both machines have the arithmetic and bitwise operations above, now allowing shifts by another register or a literal. The audit even allows logical and arithmetic shifts with saturated or modulo-four counts, rotations in both directions, and comparisons writing a zero/one register. A comparison branch directly tests EQ, NE, unsigned LT or its reverse/complement; the signed variant additionally tests signed LT and its reverse/complement. Initially only the input and literals are available. Scratch words start at zero; a LOAD or STORE costs one instruction and reads its address from a register or literal. A branch compares registers or literals.

The complete truth table accepts exactly input words 0,1,2,4,5,6,8,9. The unsigned program first rejects x≥10 with one branch. Otherwise compute r=x AND 3, then accept if r≠3. The signed program needs no data instruction:

    if unsigned(x) < 7:
        return x != 3
    else:
        return signed(x) < signed(10)

The value of signed(10) is −6. In the second branch only 8 and 9 represent smaller signed values.

For the lower bounds it suffices to classify all depth-two programs. If the first instruction is a comparison branch, each child can choose its own comparison on the original operands, or a constant verdict. A first data instruction can only help if its result is used by the second comparison. A first LOAD returns the known constant zero. A first STORE changes no register, so a following comparison still uses original operands. A STORE followed by a LOAD exhausts both instructions without reaching a comparison. These observations also cover an instruction pointer with a backward edge under the stated worst-case depth, by unfolding the first two steps.

The finite checker enumerates the entire 16-input truth table of each distinct root operation. Counting a predicate and its complement as two branch masks, it finds

| Available branch orders | Initial branch masks | New data-register tables | Successful data roots at depth two | Successful branch masks at depth two |
| --- | ---: | ---: | ---: | ---: |
| Unsigned | 60 | 254 | 0 | 0 |
| Unsigned and signed | 84 | 278 | 0 | 2 |

Neither instruction set's initial branch masks include the target. The two successful signed root masks are complements, giving the same split with its children interchanged. The audit checks the witnesses against all four Boolean assignments for every packed input. [Adaptive RAM census](../audits/packed_unit_sat_adaptive_audit.py).

The four input bits fit into one machine word. A three- or two-instruction decision therefore also shows precisely why these sizes cannot support an inference of more than one RAM step per encoded bit. Allowing input-indexed table data for free would change the initialization convention: a preloaded decision table and a lookup could decide every fixed finite catalog.
