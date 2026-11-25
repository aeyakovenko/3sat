# Exact native SAT clocks at two, four and six input bits

Fix k named variables, one fixed positive disjunction of all k variables, and optional positive and negative unit clauses for each variable. The input consists of n=2k selector bits. In the **sign-plane encoding**, word 0 is the bitmap P of positive units and word 1 is the bitmap M of negative units. For k=1,2,3 the word size w=⌈log₂ n⌉ is k, so there is no padding. At all three sizes each formula is a 3-CNF allowing the standard padding of short clauses by repeated literals.

| Selector bits n | Word width | Minimum worst-case native steps |
| ---: | ---: | ---: |
| 2 | 1 | 2 |
| 4 | 2 | 5 |
| 6 | 3 | 5 |

The optimum first exceeds the encoded length at four bits. Already at six bits it is below the length. Every lower bound here covers all programs in the machine model below, including nonuniform programs specialized to the displayed length. [Exhaustive RAM search](split_word_sat_adaptive_audit.py).

## Machine and upper bounds

The input begins in data memory. Initially all registers and other memory words are zero. All w-bit literals are available as immediate operands. A load or store, with direct or register-indirect address, costs one step. Input words may be overwritten. There are 2^w addressable memory words and unrestricted registers. An arithmetic instruction on two register/literal operands, a bitwise instruction, or a binary comparison branch costs one step. Fixed terminal states return ACCEPT or REJECT for free. Program code and its fixed branch targets are separate from writable data.

The audit includes addition, subtraction, multiplication modulo 2^w, bitwise AND, OR, XOR, logical and arithmetic shifts, both rotations, equality and both signed and unsigned orders. Shift counts can be register operands or literals. It permits both saturating and modulo-w shift counts. It also permits comparisons writing a zero/one register. Complementing a comparison gives its other verdict or data predicate. No comparison implicitly reads a memory operand. Memory is word-addressed, so the existence of a scratch address or literal does not permit a free table of precomputed answers.

For every k, an assignment exists exactly when M is not all ones and P AND M is zero. Hence the following program costs at most five steps:

    load M from address 1
    if M is all ones, reject
    load P from address 0
    r = P AND M
    if r == 0, accept; otherwise reject

At two bits load M and test it for zero. One instruction cannot both read an input word and compare it when all input-dependent registers start empty. At six bits the lower bound only needs the 16 inputs P∈{0,1,2,3}, M∈{4,5,6,7}. All program registers, memory addresses and immediates still have the full three-bit range on this restricted test set.

For comparison with the first census, taking four inputs bits in **two** words grouped by variable yields the same optimum of five. In that encoding x and y each equal 0 (no unit), 1 (positive), 2 (negative) or 3 (conflicting units). Load x and reject 3. Load y. If x=2 test y<2 and otherwise test y<3. The four-step lower bound uses the actual grouped input words. The previous one-word experiment instead supplied a four-bit register at entry and had a different machine and optimum. [One-word census](exact-instructions-for-a-packed-sat-family.md).

## Why the lower-bound enumeration covers the machine

For the tested inputs, each register is represented by its entire table of values, each memory cell by another table, and the current branch domain by an input subset. Down to the remaining horizon the checker tries every binary comparison of accessible words and searches the two branches independently. Either may terminate as soon as its target is constant. For data instructions the checker tries every result of the listed operations on every operand pair. It also tries reading through every available address table, and changes the memory tables for every possible store through every address with every available value. A predecessor can be forgotten by an actual machine; storing all earlier register values in the census permits all such programs. Conversely the model's unlimited registers realize this complete retained history.

Results equal to an old register or literal add no capability. Sorting the remaining tables merely renames registers. An instruction without a semantic effect on the tested domain cannot improve a minimum clock. A useful store must be followed by a load and, for fixed verdict leaves, an instruction that makes the verdict depend on the loaded data, so stores with less available time may be skipped. A fixed-target jump can be removed by unfolding a bounded-horizon program into a tree. A data-indexed dispatch with many outgoing code targets would be an additional instruction. For instance a four-way switch at each of two levels can decide any table of two two-bit words in four steps by alternating loads and switches; its multiway branch cost differs from the binary-branch model tested here.

## Six specific inputs are necessary and sufficient

A test suite defeats the class of four-step programs when every member of the class gives at least one wrong verdict on the suite. **The minimum cardinality of such a suite for four-bit sign planes is six.** Exactly three six-input suites suffice. One is

| P | M | SAT |
| ---: | ---: | --- |
| 1 | 0 | yes |
| 2 | 1 | yes |
| 3 | 1 | no |
| 0 | 2 | yes |
| 2 | 2 | no |
| 0 | 3 | no |

The other two replace only the first row, respectively by (P,M)=(3,0) or (0,1), both SAT. The full native search proves that no four-step program fits any of the three suites, and explicitly tests feasibility on every one-row deletion.

To prove that every smaller suite can be fitted, enumerate an inexpensive subclass. Load P and M first. The last two instructions are either a binary comparison branch with a comparison chosen separately in each child, or one data instruction followed by one comparison. This yields 3,692 distinct realizable decision tables when both constant verdicts are included. For each table mark the subset of inputs on which it agrees with SAT, then close the marked subsets under deletion. All 4,368 five-input subsets are marked. Of the 8,008 six-input subsets only the three above are unmarked. Thus a witness against the whole RAM class cannot have fewer than six rows, even though the three six-row impossibility results require searching the larger class with arbitrary instruction order and scratch accesses.

These counterexamples certify a finite time deficit for this compact catalog and exact instruction convention. They provide no lower bound above linear time for unrestricted SAT on ordinary encoded input. The checked six-bit case explicitly falsifies an induction asserting that a positive deficit at size four must persist at the next size.

## Sensitivity to the output instruction

Re-running the four-bit sign-plane census with a free choice at each leaf of any bit of any register, in addition to constant verdicts, still gives optimum five. If the leaf may also invert the chosen bit for free, the optimum drops to four. Exhaustion rules out depth three under this stronger convention. One optimal four-step program loads P and M, then uses the following tree (bit 0 is least significant):

    if M == 1:
        return NOT P[0]
    if signed(P) < 0:
        return NOT M[1]
    return NOT M[0]

Here signed(P)<0 means P=2 or P=3. When M=1, only its low bit conflicts with P. In the other branch M is 0, 2 or 3. If P has high bit one, only M=0 is allowed; otherwise both M=0 and M=2 are allowed. This dependence on output cost is one reason to state the leaf convention explicitly when comparing a tiny optimum with input length.

## Eliminating a five-step evaluator on a larger dense input

At k=8 the dense selector string has exactly 16 bits. With w=⌈log₂16⌉=4 there are four physical input words, in order P₀,P₁,M₀,M₁, two per sign plane. The fixed positive disjunction can be represented in 3-CNF by a fixed OR chain with new variables; its presentation adds no per-instance selectors. Set every input word to 0 or 1. The negative units cannot then force all eight variables false. The SAT bit on this 16-input test suite is the Boolean function

$$
(1-P_0 M_0)(1-P_1 M_1).
$$

Its unique real multilinear polynomial has degree four. A deterministic decision tree with at most three Boolean queries per path gives a polynomial of degree at most three: induct at a queried bit x by combining the two subtree polynomials as (1−x)L+xR and reducing x²=x. Therefore on at least one execution a correct RAM must read four original input words. Indeed, a decision tree can simulate it by querying the original binary value of a cell at its first load, retaining previous answers and explicitly simulating subsequent writes.

On such an execution with at most five steps, the four loads must precede a final comparison. A path ending at a constant verdict before any comparison after its last load is independent of that final data value; the decision-tree simulator can omit such a query by terminating immediately. Thus a five-step decider must start with four loads, followed by its only branch. This is the same instruction prefix for every input, although the word addresses may be data-dependent.

Now set P₀=P₁=1 and vary M₀,M₁ independently. All registers holding a loaded data word have values in {0,1}. A load addressed by a previously loaded word therefore reads cell 0 or 1, both equal to 1. Every loaded table is consequently constant, M₀, or M₁. The required verdict on this square is NOR(M₀,M₁). One comparison involving a literal depends on at most one of the two bits. One comparison between the two bits has the same outcome at (0,0) and (1,1). Neither can compute NOR. This eliminates every five-**step** program on the 16-bit family, including indirect reads and unrestricted code length; it only proves a lower bound of six steps.

For a machine with five **static instruction slots** and loops, an execution may use more than five steps. One restriction still follows. If a total nonconstant machine with only fixed-target binary branches has just one conditional site B, the path from each successor of B is deterministic until it either returns to B, terminates with one fixed verdict, or loops without B. Both verdicts must be reachable, so the two successors lead to opposite halts with no return to B. Such a machine executes no loop on a reachable input. Thus a looping five-slot evaluator must dedicate at least two sites to control and has at most three static data instructions. A subsequent census eliminates this residual class under a sixteen-step deadline. [Full five-slot proof](five-static-slots-on-four-input-words.md)

## Five static instruction slots without arithmetic

There is a separate elimination for looping programs on the same dense 16-bit catalog. Suppose every data instruction is a load, store, word copy, or move of an immediate. Registers and memory can be overwritten, and both load and store addresses can depend on data. Comparisons against registers or immediates may branch to arbitrary fixed code locations. Then **no total program of at most five static slots in this class computes the catalog**, even with no time limit.

For each i∈{0,1} use words Pᵢ=4+xᵢ and Mᵢ=8+yᵢ for independent bits xᵢ,yᵢ. The fixed high bits of P and M are disjoint. Every input word is at least four, and the decision is again (1−x₀y₀)(1−x₁y₁), which depends essentially on every one of the four original cells.

A program executing no loop takes at most five steps and was excluded above. A total nonconstant program executing a loop needs at least two static branch sites, leaving at most three data sites. Let D and I be the numbers of direct and register-indirect **load** sites. Let S count sites that can deposit a literal value in a register or memory, meaning a move-immediate or a store with literal payload. An immediate specifying an address or a comparison threshold is never supplied as a data value by that use. These site types are disjoint and D+I+S≤3.

Induction over any execution shows that every data value in a register or memory is zero, an original input word, or one of the at most S injected literals. This remains true after storing at a data-dependent address. A direct load site can read only one fixed original input cell. If I>0, the only possible original-cell addresses furnished by an indirect load operand are zero and the injected literals in {1,2,3}; the original data values themselves are at least four. Thus at most D+1+S≤D+I+S≤3 distinct original cells are addressable by any load, across all runs in the test suite. If I=0, at most D≤3 are addressable. This count allows the program to write anywhere. An original value overwritten before its first read cannot influence the computation. There is always an essential original cell that the program cannot read, a contradiction.

The finite audit checks the truth table and essentiality for this high-valued 16-input suite, and enumerates all possible sets of direct addresses and injected low literals in the reachability bound. The result covers every branch topology, register allocation and timeout in the stated no-arithmetic subclass. The separate instruction-allocation proofs complete the looping case with arithmetic at the 16-step deadline. [Five-slot census](five-static-slots-on-four-input-words.md)
