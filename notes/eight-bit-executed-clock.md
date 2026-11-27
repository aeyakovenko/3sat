# Executed instructions on the eight-bit SAT selector family

For the eight-bit packed selector encoding, every correct program in the specified three-bit RAM needs **at least seven executed instructions** on some formula. Nine suffice on all 256 formulas. These bounds allow arbitrary program length, fixed-target binary branches, early returns and writable scratch. They refer to the [separate-operation RAM and eight-bit catalog](eight-bit-catalog-load-sites.md). An inclusion-minimal set of 19 of the 256 formulas already requires at least seven steps. A comparison can choose two completely different continuations.

Let $a,b,c$ be the words at addresses $0,1,2$. The eight input bits are the binary expansion of $a+8b+64c$; $c$ ranges from 0 to 3. The two optional-unit masks are $P=a+8(b\bmod2)$ and $M=\lfloor b/2\rfloor+4c$. They select the positive and negative units supplementing a fixed disjunction of all four variables. A nonzero 4-bit assignment satisfying all selected units exists precisely when $P\mathbin{\&}M=0$ and $M\ne15$.

## Exhausting all programs with a six-step deadline

The [C++20 census](../audits/eight_bit_executed_clock.cpp) lists the 64 selector bytes explicitly and evaluates their labels by trying all nonzero assignments. A node consists of the subset of inputs reaching it, every currently available register, the eight writable memory cells and a remaining time budget. Every register and memory cell has one three-bit word per member of the subset. The code tracks all 64 words simultaneously using three 64-bit bit planes. It checks the word operations against scalar truth tables on every operand pair.

A constant verdict ends a branch. Otherwise the search tries the following transitions.

* Test equality or an unsigned or signed order on any available register or literal. Recur on both nonempty outcomes independently. Interchanging the successor labels covers complementary comparisons.
* Load through any available address or store any available word through any available address. Direct addressing uses a literal. All cells outside the three input cells start at zero. All stores, including those preceding the first input load, are eligible while a later load and comparison still fit.
* Apply an arithmetic, Boolean, shift, rotation or word-comparison operation to a pair of available words. Literal-register operand orders are included. Retain every prior result in its own register. Every actual overwrite can be simulated by using the newer register name, and unrestricted registers make each discovered continuation realizable.

A fixed jump can be omitted by unrolling a time-bounded program. An instruction computing a value already available on the entire active domain can be omitted, as can a store leaving all those memories unchanged. A store with fewer than three steps left cannot affect a later memory observation and verdict. Monochromatic branch outcomes require no instructions. The search may combine independent branch continuations even when an original program might have shared their code.

One more pruning rule accounts for compulsory reads. Fix a base input at a node. For each original cell it has never loaded, check whether a still-active opposite-verdict input differs from the base only there. If so, that original cell must be loaded on the base before a final comparison. An overwrite which erases the difference can never distinguish the two. If there are $m$ such cells and only $m+1$ steps left, the next instruction for $m>0$ must load one of them on the base. This argument works even if addresses depend on already loaded words. Counting a read of an overwritten cell as an earlier visit merely weakens this pruning rule.

The 64-row search returns infeasible. The numbers of recursive calls at remaining budgets six down to one are respectively 1, 62, 4,223, 198,126, 2,181,031 and 6,777,625. They count calls, including repeated states. Compile and reproduce with `c++ -O3 -std=c++20 eight_bit_executed_clock.cpp -o /tmp/eight-bit-clock` and `/tmp/eight-bit-clock`.

## An inclusion-minimal set of 19 formulas

Removing groups and then single formulas from the original 64 in five orders produced infeasible sets of sizes 22, 19, 21, 23 and 24. The 19 selector bytes in the smallest set found were `166, 228, 42, 164, 30, 172, 64, 44, 55, 1, 180, 113, 33, 150, 155, 187, 56, 17, 94`. The exhaustive search on this set, filling the remaining bit-plane positions by duplicating its last formula, returns infeasible. It makes 1, 62, 4,212, 187,417, 2,423,344 and 7,254,183 recursive calls at the six remaining budgets in descending order.

For each of the 19 possible single deletions, an explicit program runs in at most six instructions on every eight-bit input and answers every remaining formula correctly. An independent scalar interpreter replays each program on all 256 inputs and checks that its sole error within the 19 is the omitted formula. Every proper subset therefore fits the deadline. Whether some other infeasible set has fewer than 19 formulas remains open. Run `python3 minimal_eight_bit_executed_suite.py` with a C++20 compiler to replay the programs and rerun the complete negative search. [Verification script and all 19 programs](../audits/minimal_eight_bit_executed_suite.py)

## A nine-step program and an exact class of prefixes

Load $c$ and identify it with two comparisons, first testing $c<2$ and then testing equality with the lower value of the chosen half. The remaining behavior is as follows, with arithmetic modulo eight.

| Value of $c$ | Remaining program |
| --- | --- |
| 0 | Load $a,b$ and accept iff $((a+a)\mathbin{\&}b)=0$. |
| 1 | Load $a$ and reject if $a\ge4$. Load $b$ and apply the same conflict test as for zero. |
| 2 | Load $a,b$ and accept iff $(((a+a)\mathbin{\vert}1)\mathbin{\&}b)=0$. |
| 3 | Load $b$. If $b=2$, load $a$ and accept iff $a=0$ or $a=2$. Otherwise if $b=0$, load $a$ and accept iff $a<4$. Otherwise if $b=4$, load $a$ and accept iff $a<2$. All other $b$ reject. |

Every executed load, word operation and comparison costs one. The maximum after the three-instruction prefix is six. The census checks the answers and clocks against all 256 assignment tests.

Nine is **optimal** among programs which first load any one of the three words and then completely identify its value by branches before reading any further data or modifying memory. Arithmetic before identification is allowed. To see why, the same exhaustive native decision procedure gives the exact minimum remaining times when the initial value $v$ of a particular word is promised publicly. Its address is still populated, and all other input words vary freely.

| Known word | Exact remaining times in increasing order of $v$ | $\sum_v 2^{r(v)}$ |
| --- | --- | ---: |
| $a$ | 6, 5, 5, 4, 5, 5, 5, 5 | 272 |
| $b$ | 4, 4, 6, 5, 5, 5, 5, 5 | 256 |
| $c$ | 5, 5, 6, 6 | 192 |

If the identifying prefix uses $d(v)$ comparisons on value $v$, its terminal decision strings are prefix-free. All registers set before identification can now be replaced by known immediate literals, and the original memory is intact. Thus a total budget $T$ gives $1+d(v)+r(v)\le T$. Kraft's inequality gives $\sum_v 2^{r(v)}\le 2^{T-1}$. Every row exceeds $2^7$, ruling out eight steps for such a prefix. The displayed program attains nine.

For the full native model the interval is seven through nine. The exact slice costs give an obstruction to one form of program specialization. A separate exhaustive check rules out eight-step programs that compress their first two loaded words into a single three-bit result before loading the third. A solver can also use a loaded word as a memory address or an ALU operand while several of its values remain possible. The query masks represent a fixed catalog, and an instruction bound at this length does not transfer to unbounded SAT. [One-word summaries and residual truth tables](eight-bit-one-word-summaries.md)
