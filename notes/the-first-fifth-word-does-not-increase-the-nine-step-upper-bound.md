# A ninth instruction still suffices when a fifth SAT input word becomes live

A tightly packed 21-bit SAT selector file occupies five native words. One fixed program decides all 2,097,152 such files in at most nine instructions. It uses the fifth input word as a memory address on precisely the branch where the new selector matters. The same nine-instruction upper bound holds at 20 bits with four full words. [Executable programs and complete input audit](../audits/fifth_selector_word_audit.py) · [Operational proof in Lean](../lean/FifthSelectorWordUpper.lean)

## The consecutive-length encodings

At length $2k$, lay out the $k$ positive-unit selectors, then the $k$ negative-unit selectors, least significant bit first within each native word. The CNF contains the selected units and the fixed disjunction $x_1\lor\cdots\lor x_k$. At length $2k+1$ the disjunction gains $x_{k+1}$. The extra trailing bit $z$ selects the negative unit $\neg x_{k+1}$. There is no positive-unit slot for the new variable at this length. The native word width is $\lceil\log_2 n\rceil$. Only the unused high bits of the final physical word are zero.

The injection from an even length appends one, forcing the new variable false. The injection from an odd length inserts a zero positive selector for the new variable before the negative sign plane. Both preserve every parent verdict. The new bit is genuine at every step. The number of parent files on which toggling it reverses the verdict is respectively 1, 6,560, 1, 19,682 and 1 on the five steps from 16 through 21. These counts were checked against every file in each parent catalog.

At 21 bits, $k=10$. In address order the five physical words are $(P,Q,M,N,z)$, where $P,Q$ are the positive masks and $M,N$ the negative masks. The first four words use all five bits. The last has value zero or one. A file is satisfiable exactly when

$$
(P\mathbin{\&}M)=(Q\mathbin{\&}N)=0,\qquad (M,N,z)\ne(31,31,1).
$$

Indeed, the first condition excludes contradictory units. Among the first ten variables some can satisfy the fixed disjunction whenever a negative mask omits a bit. If both masks are full, the disjunction can be satisfied only by the eleventh variable, which is possible exactly when $z=0$.

## The ninth instruction

Load $N$ and compare it with 31. If $N\ne31$, an old variable can satisfy the disjunction. Use three instructions to load $Q$, compute $Q\mathbin{\&}N$ and reject a conflict. If it passes, use four instructions to load $P,M$, compute their AND and return its zero test.

If $N=31$, load $Q$ and reject unless $Q=0$. Load $M$ and compare it with 31. These first six instructions leave three. For $M\ne31$ use them to load $P$, compute $P\mathbin{\&}M$ and test zero. On the exceptional branch $M=N=31$, $Q=0$, run

```
z ← memory[4]
x ← memory[z]
accept iff x = z
```

At $z=0$ the second load returns $P$, so the last instruction tests $P=0$. At $z=1$ it returns $Q=0$, and the last instruction rejects. The last three instructions are optimal from this branch if $P,z$ have not been read. At $P=z=0$ changing either one reverses the verdict, so both cells must be read and one comparison is required.

The completed program takes four instructions on 63,488 files, five on 1,536,000 and nine on 497,664. Exactly 118,097 files are satisfiable. These are clocks of the exhibited program. A lower bound matching nine for all correct programs at this length is a separate question.

There is also a variant with a useful restriction property. Let the fifth bit instead enable a new, unconstrained disjunct $x_{11}$ when it is one. On the exceptional branch load $P$, load the bit and accept iff $P<z$ in unsigned order. Both complete programs have the same clock distribution. In this variant the restriction $z=0$ leaves every predecessor memory cell and every zero-initialized scratch cell with its previous value. Any lower bound already proved for the full 20-bit four-word input at the same width therefore transfers immediately to this 21-bit variant. For the negative-unit convention the preserving value is one, changing the initial contents of address 4.

## What the extension establishes

Let $T(n)$ be the optimum worst-case clock over all correct programs for the consecutive, tightly packed catalogs above. The four-bit census gives $T(16)=9$. The fifth-word program gives $T(21)\le9$. Consequently **at least one** $n\in\{16,17,18,19,20\}$ satisfies $T(n+1)\le T(n)$. This contradicts strict clock growth at every successor for this particular verdict-preserving construction, even as the native word width and the number of occupied words each grow. It does not determine which of the five inequalities holds, and the finite clocks place no asymptotic lower bound on ordinary SAT. [Four-bit clock and model](exact-nine-step-clock-for-four-sat-words.md)

The Lean file proves the equivalence with existence of a satisfying assignment, correctness and the nine-step clock for both fixed programs, a run attaining nine for each, and the inequality between adjacent optima from the two endpoint hypotheses. The finite lower bound at 16 enters as the earlier census theorem. The scalar program independently executes both instruction trees on every 21-bit file. Run `lean FifthSelectorWordUpper.lean` and `OPENBLAS_NUM_THREADS=1 python3 fifth_selector_word_audit.py`.
