# The densely packed eight-bit selector length

At k=4 the unchanged sign-plane catalog has n=8 selector bits and w=3. Its physical words a,b,c in addresses 0,1,2 encode P=a+8(b mod 2) and M=⌊b/2⌋+4c, with c∈{0,1,2,3}. Thus the three words are packed consecutively across the sign-plane boundary. SAT means P AND M=0 and M≠15. The question here is whether five *static* instruction sites can always meet the *eight-step* deadline. These are different bounds. [Earlier lengths and RAM semantics](exact-clocks-for-two-word-sat-inputs.md).

**Every program with at most five stored instructions fails on some eight-bit input within the eight-step deadline.** This is the first failure strictly after six bits (the next even selector length is eight). At k=1,2,3,4 the answers to “is there a five-slot program meeting the n-step deadline?” are respectively yes, no, yes, no. In particular four bits is the first failure overall. This result is specific to the length-dependent deadline: it does not determine whether eight-bit inputs admit a five-slot program with sixteen steps.

For example, the five-slot program that solves the six-bit catalog treats cell 1 as the entire negative mask, rejects if it equals 7, and otherwise checks whether cells 0 and 1 have a common set bit. On eight bits, $(a,b,c)=(0,6,3)$ means $P=0$, $M=15$. Its positive disjunction and four negative unit clauses are jointly unsatisfiable, but this program accepts. With $c=2$ the same program accepts correctly. This pair defeats that particular carryover. The full census below also covers every possible replacement program.

## Any number of static slots with a single LOAD site

No total binary-branch program containing just one static LOAD site meets this deadline. The argument allows arbitrary ALU operations and writable data memory. Use the SAT input (a,b,c)=(4,4,2). Changing a to 6 makes the formula UNSAT; changing b to 5 makes it UNSAT; changing c to 3 makes it UNSAT. All three original words must therefore be loaded on the accepting execution before its final comparison. A word overwritten before its first read cannot affect the verdict.

In a total nonconstant program, if the only LOAD site is visited L≥2 times before the final comparison, there must be **at least L+1 branch executions** on that prefix. Without a branch between two visits, fixed control flow would loop forever. There must also be a comparison after the last necessary load. Suppose these L branches were all the branches on the prefix. The first branch reached after each visit to the LOAD must then be the same site B, since the intervening control flow is fixed. One successor of B returns to B without any intervening branch. It must be taken on all the returning visits: the final visit must take a successor that leads to a terminal without encountering another branch. Since there was no branch before first reaching B, the only reachable alternatives are to continue the loop, or to return that one fixed verdict. This contradicts totality and nonconstancy. Trailing data instructions that cannot affect the verdict can be ignored.

Consequently the deadline allows at most three LOAD executions, all of which must read distinct original words. The accompanying at least four branches leave **one** step for any other operation. If a separate register supplies the LOAD address, reading three distinct addresses requires two changes to that one register. A literal address cannot vary. If instead the LOAD overwrites its address register, none of the three original values on (4,4,2) is the address of a different original cell. In particular 4 points into scratch and the value 2 occurs only in cell 2. Moving from each original read to the next requires a distinct register update. Reading a modified or scratch cell to perform an update would already be an extra LOAD. The available single step is insufficient.

## Pure comparison of values obtained by LOADs

There is also an independent unbounded-time exclusion for any number of read-only LOAD sites with at most three fixed comparison sites and no other data instruction. A fixed comparison with a literal defines a unary Boolean function of a word; ordering the operands and complementing the result covers all binary-branch conventions. After identifying complements there are 18 such predicates on the eight word values, including the constant case. A register/register comparison is covered by preserving equality, unsigned LT, or signed LT on every ordered pair of values.

For two inputs of opposite SAT verdict, start with a binary relation containing the matching zero initial registers and the three pairs of original word values. Extend it until applying indirect LOAD simultaneously to both components gives no new pair. If all fixed unary comparisons agree across related values, and all fixed binary comparisons agree across all ordered pairs of related values, the two executions stay in the same control state with correspondingly related registers. Each direct or indirect load preserves the relation, and no branch distinguishes the inputs. They cannot both be answered correctly.

Across the 80 SAT and 176 UNSAT inputs, record the sets of comparison predicates preserved by these closures. The finite audit finds 427 distinct sets; every multiset of up to three allowed predicates is contained in at least one of them. Hence this comparison-only read-only model fails independently of its deadline. This argument does not automatically cover stores. [Finite comparison audit](../audits/eight_bit_catalog_load_sites.py).


## All alias choices for two LOADs and one ALU

With two fixed binary branch sites and two LOADs, name the destinations of the two LOADs and the ALU in first-write order. This gives exactly the five register identifications below. Unwritten registers equal literal zero. Each LOAD can use an input address, one representative scratch address, or any writable register as its address. Two direct LOAD sites cannot read all three original words. Enumerate every binary ALU table on all reachable-width register tuples, taking operands from registers and all eight literals. The generated tables include all arithmetic, shifts, rotations and data comparisons of the declared machine. For a particular alias pattern, two syntactic instructions giving the same complete register-tuple table are interchangeable.

The control census permits the three data sites to have arbitrary fixed successors. Bypass a data site that leads only to a fixed terminal, since the data cannot change that verdict. Unreachable sites remain allowed. Sort each pair of distinct branch successors, retaining predicate complements, and name the first conditional encountered from entry the first branch. If a branch's successors coincide, it is a fixed jump and is immaterial. Keep graphs reaching both terminals and with an eight-step YES path containing at least three LOAD executions. There are 734. These are the same normalizations used in the four-word census. [Control normalization](two-load-programs-with-five-static-slots.md).

For each input compute which original word addresses are essential, by testing every allowed change to each individual word. For every surviving graph and data palette, allow free branch choices on every input. There must be some path within eight steps to the correct terminal that reads all those essential addresses. This filter leaves 4,358 graph/palette pairs. For each such pair try every independent choice of two actual comparison truth tables on the register tuple. Simulate the resulting fully specified program on the 256 inputs until a failure is found, counting any timeout as failure.

| LOAD 1, LOAD 2, ALU destinations | Data palettes | Graph/palette pairs after filtering | Distinct predicates per site | Realizations checked |
| --- | ---: | ---: | ---: | ---: |
| 0,0,0 | 1,206 | 96 | 36 | 124,416 |
| 0,0,1 | 5,860 | 1,340 | 80 | 8,576,000 |
| 0,1,0 | 5,860 | 471 | 80 | 3,014,400 |
| 0,1,1 | 5,860 | 471 | 80 | 3,014,400 |
| 0,1,2 | 16,005 | 1,980 | 134 | 35,552,880 |

None of the 50,282,096 realizations passes. The independent two-LOAD/STORE case allows input overwrites and both kinds of indirect addressing. Its address and control tests eliminate all 12 surviving data palettes even with free branch choices. [Pure-register and ALU census](../audits/eight_bit_catalog_two_loads.cpp) · [Writable-memory census](eight-bit-sat-with-two-loads-and-a-store.md).

## Completing the static allocation argument

A total nonconstant binary-branch program that loops needs at least two effective branch sites. With two sites available for control, three data sites remain. There must be at least one LOAD; the single-LOAD argument applies however the unused sites are allocated. With two LOAD sites the remaining data operation is an ALU, a STORE, or a copy included in the ALU enumeration. With three LOAD sites, there is no other data instruction and the comparison-only argument applies. More branches leave only fewer data sites. These statements allow arbitrary fixed control targets and initially zero scratch.

An acyclic five-site program may use three LOADs, an ALU or STORE, and only one branch. For a nonconstant program with a single branch all instructions affecting its verdict precede that comparison; after it only the two fixed verdicts are possible. Enumerate the data prefixes containing three loads plus that spare operation in every order. The three loads have to read the three distinct original cells on (4,4,2); before that read, the original value must not have been overwritten. On the full input set the checker skips a data result equal to an existing register/literal or a STORE that never changes memory; such a redundant instruction could simply be removed, leaving the load-only case. EQ and both signed and unsigned orders of every operand pair, in both orientations and complemented as needed, supply the terminal comparison. The enumerated 10,978 ALU prefixes and 1,728 STORE prefixes yield zero solutions. Four LOADs and a comparison fall under the load-only argument. Fewer than three LOAD executions cannot read the baseline's three essential words.

Reproduce the comparison closure and both C++ cases with:

    python3 eight_bit_catalog_load_sites.py
    c++ -O3 -std=c++17 eight_bit_catalog_two_loads.cpp -o /tmp/eight-bit-loads
    /tmp/eight-bit-loads
    c++ -O3 -std=c++17 eight_bit_store_controls.cpp -o /tmp/eight-bit-store
    /tmp/eight-bit-store

This establishes a finite failure for the full stated static class at multiplier one. The minimum number of executed steps with unrestricted code at eight selector bits, and the asymptotic time for explicit SAT, are separate questions.

At six stored instructions the one-comparison allocation also fails, even with arbitrary indirect memory operations among its five data sites. The full six-slot case remains open. [Finite witness suite for a single comparison](single-comparison-at-eight-selector-bits.md)
