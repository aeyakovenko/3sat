# Seven tests against every six-step evaluator

In the dense 16-bit sign-plane SAT catalog, let a four-digit hexadecimal string give the four input words in memory order P₀,P₁,M₀,M₁. The binary-branch, four-bit word RAM cannot meet a six-step deadline on all seven of these inputs, regardless of code size:

| Input | SAT |
| --- | --- |
| 4488 | yes |
| DD77 | no |
| 8EB6 | no |
| F488 | no |
| 4F88 | no |
| 44F8 | no |
| 448F | no |

Thus the unrestricted-code optimum on this catalog at this length is at least **seven executed instructions**. The test suite also defeats six static slots without a loop. A six-slot program executing more than six steps on some input is outside this result. [Machine, encoding and leaf conventions](exact-clocks-for-two-word-sat-inputs.md).

## Classification of the accepting path

On 4488 each of the four single-cell mutations in the last four rows changes the verdict. Its accepting execution must load each original cell before its last comparison. An original value overwritten before it is read cannot affect a computation. All seven inputs have every native word at least four. Direct input addresses are 0,…,3 and the other cells start at zero.

The accepting path has room for four necessary LOADs, its last comparison, and at most one additional instruction. A word read directly from an original cell points into scratch when used as an address. Before any ALU or store, a register therefore represents one fixed input column or the constant zero on this entire suite: direct addressing selects a column or zero, and an indirect address through an original column always selects initial zero scratch.

* **An earlier comparison, an extra LOAD, or no extra instruction.** Along the base path the two comparison outcomes, if two are used, are comparisons of input columns and literals. A negative with the same two outcomes necessarily follows this same control path. An extra load can only supply another unmodified column or a constant. Moves and fixed jumps in place of an extra instruction do not increase the information available here.
* **A STORE.** Apart from it the four loads on the base must all read distinct original cells. At the store's execution time its address either points into scratch on every example or is a fixed address on every example. If it overwrites a fixed input cell, that cell must already have been read on the base and cannot be among its subsequent four necessary reads. After the store no base load can read scratch or previously read input cells. Inductively the remaining addresses therefore select the same unmodified input columns throughout the suite. In this case a single comparison of columns/literals suffices to represent the accepting path.
* **An ALU instruction.** Its result q is a word function of two operands chosen from the input columns and the literals. In the enumeration we even allow columns the program may not have loaded yet. All four base loads still have to read distinct original cells. A load through q can therefore occur usefully at most once. Write L(q) for the selected input word when q<4 and zero otherwise. On the base, a necessary load through q returns an original high word; that high word cannot itself address another necessary original load. Every other necessary load chooses a fixed input column on the suite. For example, selecting the address of a directly loaded column indirectly would access scratch on the base, which is impossible here. This leaves only columns, literals, q, and L(q) as operands of the closing comparison. The argument allows the ALU result to overwrite a prior register.

## Finite verification

The audit enumerates the signs of equality and both signed and unsigned orders of all unmodified column/literal pairs. For each possible outcome matching the base it retains the mask of negative examples with that same outcome. It intersects these masks in all pairs to cover the two-comparison case. It separately enumerates every allowed ALU on every pair of columns or literals, yielding 763 distinct word tables on the seven examples. For each q it constructs the table of L(q) and includes comparisons of these words with all possible operands. Comparisons of a word with itself accept every negative if they accept the base. Complementing a branch changes neither its agreement mask nor the classification.

The union has 60 different negative agreement masks. Each is nonempty. Therefore whichever admissible accepting path a correct six-step program would take on 4488, at least one listed UNSAT input follows it and also accepts. The run uses exact word and bitmask operations and does not assume a space restriction. Run with `python3 six_step_sat_transcript_audit.py`. [Finite audit](../audits/six_step_sat_transcript_audit.py).

A direct upper bound for unrestricted code is nine steps. Load M₀ and branch on M₀=15. In the false branch the fixed positive clause can be satisfied whenever both unit pairs are consistent, so first load P₀ and test (P₀ AND M₀)=0 (one AND and a comparison), then load P₁,M₁ and test the second conflict in the same way. In the true branch load M₁ and reject if it is 15, load P₀ and reject unless it is zero, then load P₁ and test (P₁ AND M₁)=0. Each longest path has four loads and five other instructions. The unrestricted-code optimum at this length therefore lies between seven and nine inclusive.
