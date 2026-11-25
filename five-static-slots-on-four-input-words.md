# The step from four to five stored RAM instructions

For every deterministic program with at most five stored instructions in the four-bit-word RAM specified below, some formula in the 16-bit selector family either receives an incorrect answer or fails to receive an answer in 16 executed instructions. The program, including all its instructions, may be chosen afresh. The failing formula may depend on the program. Indirect writes, memory aliasing and loops are included.

At the preceding size, six four-bit selector inputs already defeated every four-instruction program, even without a deadline. One five-instruction program solves that entire earlier catalog. Enlarging the catalog is necessary for the step with the same or a more generous deadline. [Four-instruction certificate](static-program-size-on-two-sign-planes.md)

## The SAT predicate and machine

Take eight Boolean variables, one fixed positive disjunction of all eight, and independently select their positive and negative unit clauses. A fixed chain of auxiliary variables can express the disjunction in 3-CNF. Pack the selectors into four nibbles at addresses 0, 1, 2, 3, in order $P_0,P_1,M_0,M_1$. These sixteen selector bits are the entirety of the input counted in this experiment. The verdict is SAT exactly when both $P_i\mathbin{\&}M_i=0$ and at least one $M_i$ differs from 15. All 65,536 strings represent legal instances.

Registers and the remaining twelve writable addressed words start at zero. Each instruction is a one-result arithmetic, logic, shift, rotation, comparison or copy instruction, a LOAD, a STORE, or a conditional jump comparing two registers or literals with fixed successors. Unsigned and signed comparison are allowed. A memory instruction uses a direct literal or a single register address. Instructions have fixed operands, and terminal YES and NO labels are free. The full finite basis is in the linked checkers. Length 16 is public and arbitrary four-bit immediates are allowed. Fusing a load with a test or extracting arbitrary output predicates without charging instructions changes the model.

## Covering every program

If no instruction repeats, at most five instructions execute. The Boolean restriction of the predicate to four binary words requires all four words on some path. Four loads and one comparison cannot decide the resulting function. If a total nonconstant program executes a loop, it must have at least two effective conditional sites. With a single such site, both outgoing continuations must eventually give different constant verdicts, leaving no returning continuation. An input on which the deadline expires is already a witness. Equivalently, assume all catalog inputs finish correctly by the deadline and derive a contradiction. [Five executed instructions and copy-only machines](exact-clocks-for-two-word-sat-inputs.md)

| Remaining configuration | Reason for exclusion |
| --- | --- |
| No LOAD | The verdict is independent of the input. |
| No value-producing arithmetic or logic | On a high-valued essential four-cell family, three data sites in total cannot supply all four numeric input addresses. This also covers copy and literal-injection instructions. |
| Two LOADs and one ALU, two branch sites | Address closure, comparison coupling, and a finite control-graph census exclude all aliases at the 16-step deadline. [Proof and checker](two-load-programs-with-five-static-slots.md) |
| One LOAD and one ALU, three branch sites | The unique feasible addressing update on a sensitive suite is increment by one. A pair of adjacent negative words defeats the comparisons, or a repeated self-addressed load costs at least 20 steps. This argument allows multiple independent control cycles. [Three-branch proof](two-load-programs-with-five-static-slots.md#trading-one-load-for-a-third-comparison-site) |
| One LOAD, one ALU and one STORE, two branch sites | No schedule can read the sensitive inputs and realize the verdicts under even arbitrary stationary exit tests, at any running time. [Writable-memory proof](one-load-one-store-with-five-static-slots.md) |
| One LOAD and two ALUs, two branch sites | All five partitions of the three destination registers fail, even without a deadline. [Two-ALU proof](one-load-two-alus-with-five-static-slots.md) |

Unused slots or fixed jumps do not help. With only one LOAD and one ALU and fewer than three branch sites one may allow an additional unused site. A move is a copy or a one-result ALU table independent of one operand. Four or more branch sites leave at most one data instruction. The tables and control arguments cover programs independently of any edit relation to a preceding program. For reconstructing a finite witness suite one can use the union of all tests in the four cases, including the single-word mutants that justify compulsory reads, or simply use the full catalog.

## How far the deficit can extend on this catalog

There is a ten-slot straight-line branching program with worst-case time at most ten. Load $P_0,M_0$, compute their AND and branch to NO if nonzero. Do the same for $P_1,M_1$, retaining both negative words. If $M_0\ne15$, return YES. Otherwise return YES precisely when $M_1\ne15$. This uses four LOADs, two ANDs and four comparisons. Thus the minimum static program size for the 16-step deadline lies between six and ten, inclusive. Seven explicit inputs also defeat **arbitrary** code at a six-executed-instruction deadline. With unrestricted code the optimal worst-case time on this catalog lies between seven and nine steps inclusive. [Seven-input certificate and upper bound](seven-tests-for-six-native-steps.md)

The finite result handles the multiplier one on a compact promise encoding. The analogous assertion for an arbitrary static-size cutoff and an arbitrary linear multiplier on ordinary encoded SAT still requires a way to produce failures for every newly admitted program. The earlier size-uniform edit argument scales to arbitrary cutoffs but charges only order $n/\log n$ steps. [Quantifiers, explicit SAT and the address charge](bounded-ram-programs-and-separate-sat-witnesses.md)
