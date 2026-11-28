# Every four-word cube-cycle solver needs nine steps, with bounds at the next two word widths

Every correct four-bit program needs at least **nine executed instructions** on some satisfiable mask and on some unsatisfiable mask in the same explicit 89-file suite. Computed first reads, overwriting input, arbitrary program text and all native scratch cells are allowed. The existing fourteen-step program works on all 65,536 masks. This closes the unrestricted eight-step case left open by the earlier census. The exact shared clock lies in **[9,14]**. The familiar nine-step *exact* clock for a different sign-plane catalog is a separate result. [Earlier cube-cycle census and upper program](clock-bounds-for-the-four-word-cube-cycle-catalog.md) · [Sign-plane catalog](exact-nine-step-clock-for-four-sat-words.md)

The same proof gives the following lower bounds when the native width changes with the encoded selector length. Here $L$ is the physical selector length, $w=\lceil\log_2 L\rceil$, and $m=\lceil L/w\rceil$. If $L=mw-1$, the unused high bit of the last word is zero.

| Selector bits $L$ | Word width $w$ | Words $m$ | Shared worst-case lower bound |
| --- | ---: | ---: | --- |
| 16 | 4 | 4 | 9 |
| 20 | 5 | 4 | 9 |
| 24, 25 | 5 | 5 | 10 at both lengths |
| 29, 30 | 5 | 6 | 11 at both lengths |
| 41, 42 | 6 | 7 | 12 at both lengths |
| 47, 48 | 6 | 8 | 13 at both lengths |
| 53, 54 | 6 | 9 | 14 at both lengths |
| 59, 60 | 6 | 10 | 15 at both lengths |

The lower bound in each row is $m+5$ on each verdict separately. The argument certifies both lengths of an adjacent pair independently. It does not assert that applying XOR insertion to an individual hard mask makes its image hard. Only the *proved lower bounds* increase across the rows. The proof covers the original twenty native operations and also unsigned quotient and remainder, permitting both zero-divisor conventions specified below.

## The instance and its one-bit successor

Write $h(u,v)=(1-u)(1-v)$ for the indicator that two adjacent selector bits are both zero. A mask is satisfiable exactly when some cyclic pair has $h=1$. For the 16-bit catalog these witnesses are precisely the four-cube vertices left uncovered by the selected Gray-cycle edges. For an arbitrary length $L\ge3$, there is a fixed proper 3-CNF template with one model per such vertex. Require exactly one selected vertex $s_i$. A deterministic prefix OR with the additional binary clauses forbidding $s_i$ together with its preceding prefix OR enforces this in linear size. For each edge $i$ compute $d_i=s_i\lor s_{i+1}$. Its selector enables the single clause forbidding $d_i$. Use both directions of each Boolean gate definition. To pad units and binary clauses to width three, fix three fresh names false by the seven proper clauses excluding every other assignment. Every true vertex extends uniquely. The clocks above charge the $L$ physical bits of the selector catalog. Printing the whole template in ordinary DIMACS has a different length.

**A linear map over $\mathbb F_2$ gives an exact successor at every length.** Between any two adjacent bits $u,v$, insert $z=u\oplus v$, leaving the original bits at their new positions. The map is injective, and
$$h(u,z)=h(z,v)=h(u,v).$$
If the old edge carried a hole, it now carries two. Otherwise neither new edge carries one. The only two local Boolean functions with these two identities are XOR and OR. The values at $00,01,10$ must be $0,1,1$ respectively, and the value at $11$ is free. Repeating subdivision on each edge uniformly doubles the number of witnesses at each iteration. These identities hold on all inputs, independently of the machine.

The distinction matters for the proposed induction. With $m$ packed words, a single program decides the entire cycle predicate in $O(m)$ steps by checking internal adjacent pairs and carrying one endpoint bit across each word boundary, including the wraparound. At a partial last word it uses the known length to mask padding. Thus the algebraic successor preserves the verdict and can make the witness count grow without forcing a higher asymptotic decision time. The larger finite clock bounds above have their own proof.

## When the last original word must be read

In the native catalog each register or literal operand is one $w$-bit word. A load, store, binary ALU operation, or two-operand conditional branch is one instruction. Branch targets and terminal verdicts are fixed labels. The input initially occupies addresses $0,\ldots,m-1$, all other words and registers start at zero. The twenty operations include modular arithmetic, both conventions for shifts, rotations and comparisons returning a word. We also allow unsigned division by zero returning zero or the all-ones word, and unsigned remainder by zero returning zero or its dividend, with each convention available as a separate opcode.

Fix a base input whose full words equal $b$, where $b$ is 5, 13 or 27 at widths 4, 5 or 6 respectively. A partial word has $w-1$ live low bits and value 7 at width five or 13 at width six. Every base word is internally free of adjacent zeros on its live bits. Its lowest live bit is one, its highest live bit is zero, and its numeric value is at least $m$. Every original word is pivotal on this base. Replacing one word by a word with an internal hole makes the mask satisfiable. Consequently a correct run must load each original word before overwriting it.

Suppose all the relevant files terminate by step $m+4$. Let $t$ be the instruction first loading the last unread original word on the base. All completions of that one word follow the same path up to that load and place its value $x$ in the designated register. If the last original has $k$ live bits, its preceding word ends in zero and the following word starts with one. Thus on its legal domain $0\le x<2^k$ the required *cover* bit is
$$P_k(x)=[x\text{ has no adjacent zeros among its }k\text{ live bits and its low bit is one}].$$
We claim $t\le m+1$. If $t=m+2$, only two steps remain. Two successive guards on $x$ and literals cannot recognize $P_w$, even if the second guard depends on the first. One ALU operation followed by a guard cannot do so either. The exhaustive tests allow comparisons against the new result, the original $x$, and any literal in either order and polarity. A store with no subsequent read cannot improve a final guard.

The remaining possibility is one load then a guard. A literal load gives a literal or $x$. For an indirect load by $x$, start with the unmodified memory with $x$ in the last unread position and the stated base values in the other input positions. At most two prior stores can change this returned-value table at two values of $x$, since the execution before reading $x$ was fixed. In every tested layout, each such unmodified load-and-guard computation errs on at least three values, unless the guard ignores the load, a case already excluded. The cases $t>m+2$ have at most one remaining instruction and the unary guard obstruction already applies. In the 89-file proof we use only the unary domain $U=\{3,4,5,9,11,12,13,14\}$ at width four. At its high values $x\ge4$ the unmodified load by $x$ returns zero. A final guard depending on this load has, there, one of the four defaults constant false, constant true, nonnegative or negative. Their error counts on the high members of $U$ are 3, 4, 3 and 4. [Unary checks and truth-table identities](../lean/CubeCycleThreeStepSuffix.lean)

## Three steps on two free original words

The first $m+1$ base instructions contain all $m$ fresh reads and one further instruction $E$. The run cannot have halted earlier under the claimed deadline without a correct terminal on the same completions; a short path can equivalently be padded by a constant guard. Before $E$, all registers are literals, initial zero or raw words from earlier fresh reads. Freeze the sources of the at most two raw operands of $E$ to their base value. Choose two remaining full-word positions as $x,y$ and keep every other position at its base value. There are at least four full words before freezing in every row, including the partial-word rows.

On this restriction the first $m+1$ instructions follow one common control path and read the designated cells. A raw register with base value at least $m$ could never be the address argument of a base fresh read. Such a read has a literal or constant address, or uses the output of $E$. An ALU or branch at $E$ has its operands fixed. A store at $E$ has a fixed address and value, including a possible overwrite of an already read input. A nonfresh load at $E$ has a fixed address and returns a constant or a raw alias. An alias of a free word has base value $b$ and cannot be the address of a later base fresh read. This proves the common-prefix assertion inductively. All suffix registers can be granted $x,y$ and every literal for free. The memory is the original layout with at most one fixed-address, fixed-value override.

At width four let $x,y$ range over the following ordered pairs, printed as two hexadecimal digits with $x$ first.

```
44 45 4b 54 55 59 5b 5c 7b 94 95 b4 b5 b7 bb bc c9 cb
```

Both components are in $\{4,5,7,9,11,12\}$. Every internally safe letter in that set has low bit one. On any placement of these pairs the cover bit is exactly $P_w(x)\land P_w(y)$. At widths five and six we use the full square of the following alphabets, with the same property.

| Width | Alphabet in decimal |
| ---: | --- |
| 5 | 9, 11, 13, 16, 19, 21, 24, 27, 31 |
| 6 | 19, 23, 27, 33, 39, 43, 49, 55, 63 |

Three remaining native instructions cannot decide that conjunction on the indicated rows. Here is the exhaustive classification. End with a comparison, padding a constant verdict if necessary. If the first instruction is a guard, each branch may choose its own two guards, or one result-producing instruction and a final guard. If one register is computed first and both following steps are guards, use the new register in either guard. For two result-producing instructions followed by one guard, the second result is an independent first result, an ALU involving the first result, or a load indexed by that result. Enumerate both orders, all immediate operands, every placement of the two input words and every fixed memory override. The two loads may even use independent initial overrides, which enlarges the candidate class. A store influences an answer in this budget only in the order store, load, guard. The return is the stored value when the two addresses match and the initial value otherwise. Both address operands and the stored value range over literals and the two raw words. This list covers branching programs with arbitrary code size because the only path-dependent remaining instructions come after earlier guards.

Take $bbbb$ together with all one-position changes from $U$ and all six ordered placements (increasing address) of the eighteen pairs. The union contains **89** distinct masks, of which 62 are satisfiable and 27 are covers. No depth-eight tree is correct even just on these masks. If a program correct on this suite halted by step eight on all inputs of either verdict, replacing all its still-running leaves at that deadline by the opposite verdict would give such a tree. This proves the separate existential witnesses for each verdict in the same suite. The same truncation argument works with the full legal unary domains and the two-word squares for the larger sizes. For a partial last word the unary check covers that word separately, using its $w-1$ live bits and retaining its actual numeric base value in memory when another word varies. The two free suffix words always have full width. Minimality of the suite size is open.

## One hard suite serves both lengths at width six

For each $m=7,8,9,10$, take the base with all full words 27 and a five-live-bit tail of value 21. Append zero in the previous padding bit. This leaves every initial word at exactly the same address with exactly the same value. The compiler can replace any public length register by the chosen constant at fixed length. Thus a correct program on the image yields a program with the same clock on the original suite.

Here is one suite on which the two predicates agree and on which the $m+5$ bound holds. Include the base, all changes of one word for which both lengths give the same verdict, and all two-full-word placements of pairs from the width-six alphabet. For the first full word, the unary agreement condition excludes precisely the internally safe even words. For every other full word the domain is unrestricted. For the partial tail the allowed values are $0,\ldots,31$ except the safe odd words less than 16. A unary value on one of these restricted domains is a cover exactly when it has no adjacent live zeros and its low bit is one. To see the two-word case, both words either have an internal hole or are safe with low bit one. With the tail fixed at 21, every intervening seam on a putative cover is then safe at either length. The ordinary base-pinning proof applies. The minimum numbers of errors before two fixed store repairs in the unary load case are 13, 13 and 5 for the first, internal and tail positions. The three-instruction test uses the actual tail value in the memory image.

It follows that the four extensions 41→42, 47→48, 53→54 and 59→60 preserve the finite lower bound on **the very same suite in memory**, with a hard file of either verdict for each correct program. The choice of hard file may still depend on the program. The shorter and longer catalogs charge the same word width. At width five this particular unary proof fails. Its allowed tail is $\{0,\ldots,15\}\setminus\{5,7\}$, and its covers are $11,13,15$. A two-guard tree first tests $x<13$, returning $x=11$ on that branch and $x\ne14$ on the other.

## Infinitely many one-bit extensions with the same hard file in memory

There is also a lower bound that transfers across the same one-bit extension for arbitrarily large native widths. Fix $w$ and $m$ such that $L=mw-1$ and $L+1$ both have width $w=\lceil\log_2 L\rceil=\lceil\log_2(L+1)\rceil$, $w\ge4$, and $m\le 2^{w-1}-1$. Start at length $L$ with all live bits one. Use this base and its $m$ variants obtained by zeroing one whole input cell, including the live bits of the partial cell. Append a zero. This linear embedding leaves every physical memory word unchanged because the new bit occupies a former zero padding bit. The base remains a cover, since both its old boundary bits were one. Every edit still contains two consecutive live zeros. Thus both lengths have the same labels on the same physical words. A program for either length can run on the other suite at identical cost, specializing its public length if the model provides one.

On the base itself, **every correct program executes at least $m+\lceil m/2\rceil$ instructions** at both lengths. It must load every original cell before an overwrite, by the single-cell edits. Mark these $m$ first reads. Both possible base word values, $2^w-1$ and $2^{w-1}-1$, lie beyond the last input address. Consequently no marked read can use a register still holding such a raw word as its address. Following one original word from its marked read, some other instruction must take it as an operand before its last copy disappears or the program halts. Otherwise zeroing this cell leaves the entire control path unchanged. Copies obtained by repeated loads of its original address do not affect the argument: until a first operand use, all addresses and all branches are independent of that word. Each instruction other than a marked read has at most two operand slots and can supply this first use for at most two originals. This proves the count. For example, $m=\lfloor 3\cdot2^{w-2}/w\rfloor$ meets the length and address conditions at every sufficiently large $w$.

The earlier homogeneous-word theorem improves the same base bound to $[5(m-1)-24]/3$ by marking the $m-1$ full words. Enlarge the common suite to allow any subset of them to change to zero. Every nonempty subset leaves an internal hole, the common full-word value lies outside the input addresses, and there are 24 numerical opcodes. These are the hypotheses of that theorem. [Homogeneous-word counting argument](executed-operands-on-homogeneous-sat-words.md)

This witnesses an unbounded sequence of genuine transfers by physical identity. It prices reading and using packed words. Loading each word and comparing it with the expected base word decides the shared promise in $2m$ steps. The entire cyclic selector has the uniform scan bound above.

## A concrete failure of a width-independent suffix induction

For the six-letter four-bit alphabet, its good values are the primes $5,7,11$. Their six distinct pair products are $25,35,49,55,77,121$. None is also a product involving a bad letter. At every word width $w\ge145$, the *same* two-register subproblem has a three-instruction solution. Multiply $x$ by $y$, rotate a fixed literal right by that product, then branch on the sign. Give the literal a one in bit $j-1$ for each of the six products $j$. Since $1\le xy\le144<w$, the new sign bit is exactly the old bit $xy-1$. This program works on the entire six-letter square. The obstruction at wider widths therefore needs new letters or a different invariant. [Product and rotation check](../lean/CubeCycleThreeStepSuffix.lean)

## Verification

The Lean file checks the width-four model on the 18 ordered pairs, the restricted unary computation, the 89-element union, and the Boolean subdivision identities. Its large finite searches use `native_decide`. The deduction from an arbitrary native execution to those finite tests is the prefix argument above. The C++ enumeration covers all three widths. At widths four and five it additionally compares the original twenty ALU tables and five oriented guards with independent bit-sliced implementations. We compared its dumped 24 ALU tables and three primitive comparisons at widths four, five and six with the independent Python arithmetic and direct quotient/remainder semantics, totaling 145,152 entries. [Python word semantics](../audits/ramsey_dimacs_word_audit.py) The fourteen-step upper program can be replayed separately on all 65,536 masks. [Native enumeration](../audits/cube_cycle_three_step_suffix.cpp) · [Lean checks](../lean/CubeCycleThreeStepSuffix.lean) · [Upper-program replay](../audits/cube_cycle_verify_program.py)

From the repository root, build with a C++17 compiler supporting 128-bit unsigned integers and run:

```sh
g++ -O3 -std=c++17 -DNATIVE_WIDTH=4 -DCHECK_REFERENCE audits/cube_cycle_three_step_suffix.cpp -o /tmp/cycle4
/tmp/cycle4 4 5 '4 5 7 9 11 12' suite89
g++ -O3 -std=c++17 -DNATIVE_WIDTH=5 -DCHECK_REFERENCE audits/cube_cycle_three_step_suffix.cpp -o /tmp/cycle5
for m in 4 5 6; do /tmp/cycle5 "$m" 13 '9 11 13 16 19 21 24 27 31'; done
g++ -O3 -std=c++17 -DNATIVE_WIDTH=6 audits/cube_cycle_three_step_suffix.cpp -o /tmp/cycle6
for m in 7 8 9 10; do /tmp/cycle6 "$m" 27 '19 23 27 33 39 43 49 55 63'; done
for m in 5 6; do /tmp/cycle5 "$m" 13 '9 11 13 16 19 21 24 27 31' partial 7; done
for m in 7 8 9 10; do /tmp/cycle6 "$m" 27 '19 23 27 33 39 43 49 55 63' partial 13; done
for m in 7 8 9 10; do /tmp/cycle6 "$m" 27 '19 23 27 33 39 43 49 55 63' common 21; done
lean lean/CubeCycleThreeStepSuffix.lean
python3 audits/cube_cycle_verify_program.py audits/cube_cycle_program_14.json
```
