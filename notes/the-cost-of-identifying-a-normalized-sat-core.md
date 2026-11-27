# The cost of identifying a normalized SAT core

For proper ASCII DIMACS 3-CNF, the sharp leading cost of identifying the normalized clause set by binary control flow is
$$
\alpha=\frac{\log_2 10}{12}=0.2768273412\ldots
$$
instructions per encoded bit. There are families attaining this information rate on which one globally correct SAT program takes $O(N/\log N)$ instructions on both verdicts.

More precisely, for each finite core-length cutoff $H$, there is one globally correct program $P_H$ using at most $2^{\alpha H+o(H)}$ **bits of code**. On every file of physical bit length $N$ whose normalized core has bit length $M\le H$, it takes
$$
 T_{P_H}(F)\le \alpha M+
 O\!\left(1+\frac{N}{\log(N+2)}
            +\frac{M\log\log(M+4)}{\log(M+2)}\right).
$$
The constants are independent of $H$. This includes files padded beyond $H$. The program changes with $H$. The unrestricted linear, quadratic and cubic SAT questions remain open.

## The induction that survives

Charge all bits of a native program description, including its word-width coefficient and immediates. Fix the roster through code length $C$, and give its members absolute instruction deadlines $t_i$. Start with the seven sign clauses on variables $1,2,3$ forcing all three false. Append $m$ copies of `-1 2 3 0` with a newline after every row. Changing the leading minus of any one copy to a space makes the file UNSAT at the same length. With header `p cnf 3 ` followed by the count and a newline, the exact bit length is
$$
 N=8\bigl(9m+77+\operatorname{digits}_{10}(m+7)\bigr).
$$
The seven initial rows occupy 68 bytes. Consecutive editable bytes start 72 bits apart.

Run each candidate on the SAT center through its deadline. One aligned $w_i(N)$-bit load covers at most $\lceil w_i(N)/72\rceil$ editable positions. Thus
$$
 m>\sum_i t_i\left\lceil w_i(N)/72\right\rceil
$$
leaves one edit unseen by the whole roster. The two runs of each candidate agree through its deadline or earlier halt, including in the presence of writes. Each candidate therefore fails on at least one member of this common pair. For $C+1$, enumerate the enlarged finite roster, increase the absolute deadlines as desired, and take the first larger $m$ satisfying the inequality. This search terminates because each width is $O_i(\log m)$. This is the journal’s common unread-word argument with explicit byte accounting. [Earlier finite-roster argument](hamming-cycles-in-the-physical-sat-verdict.md)

At deadline $a(N+1)^k$, even one candidate exhausts this counting argument for large $m$ and fixed $a>0$, $k\ge1$. The failure has an execution witness. Deduplication leaves at most eight clauses on every file in the construction, so one fixed correct program handles the entire sequence in $O(N/\log N)$. Increasing the multiplier from $a$ to $a+1$ also reopens previous timeouts by a full $(N+1)^k$ steps at unchanged length. A previously observed wrong terminal verdict remains a failure. These two docket entries behave differently under deadline padding.

## Where the bit-length constant comes from

Use the journal’s separate-operation RAM with binary fixed-target branches, unrestricted writable memory, and width $16\lceil D\log_2(N+2)/16\rceil$ for fixed $D\ge1$. Finite control labels can address the whole program text. The domain for the numerical coefficient is well-formed, comment-free ASCII with three distinct variables per clause. The existing packed normalizer sorts and deduplicates the clauses and renames the occurring variables densely in $O(1+N/\log(N+2))$ instructions. Ranking names by decimal length first ensures that no occurrence gets longer. Write $B=M/8$ for the normalized byte length. [Packed parser](packed-normalization-of-dimacs-clauses.md) · [Nonexpanding renaming](dense-sorted-cores-for-ram-exhaustion.md)

Let $A_{B,c}$ count dense sorted cores of at most $B$ bytes with $c$ distinct clauses. Two bounds on the **same** count give the coefficient. Order the clauses temporarily. The $3c$ positive decimal field lengths have sum at most $B$, so there are at most $\binom B{3c}$ length vectors and at most $10^B$ digit strings for each vector. Alternatively, every dense name is at most $B$, giving at most $B^{3c}$ ordered name sequences. Allow eight sign patterns per clause. Every clause set has $c!$ different orders. Hence
$$
 c!\,A_{B,c}\le 8^c\min\!\left\{10^B\binom B{3c},\,B^{3c}\right\}.
$$

Distinct records over a fixed byte alphabet cost $\Omega(c\log(c+1))$ bytes altogether, so $c=O(B/\log B)$. Put $x=c\log_2 B$. Then $\log_2(c!)=x-O(B\log\log B/\log B)$, and the logarithm of the length-vector factor fits the same error. It follows that
$$
 \log_2 A_{B,c}
 \le \min\{B\log_2 10,\,3x\}-x
       +O(B\log\log B/\log B).
$$
The maximum of the main term occurs at $3x=B\log_2 10$. Summing over the possible clause counts costs only $O(\log B)$ further bits in the logarithm. The result is $(2/3)B\log_2 10+O(B\log\log B/\log B)$. Dividing by **eight physical bits per byte** gives $\alpha$.

## Amortizing actual comparisons

After normalization, dispatch on $M,c$ and scan the $3c$ signed dense identifiers. At a given prefix let $z$ be the number of remaining cores, and let $z_j$ survive the actual next identifier $j$. A hardwired ordered threshold tree finds $j$ in at most
$$
 \left\lceil\log_2(z/z_j)\right\rceil+1
$$
binary comparisons. Give the legal identifiers consecutive intervals of masses $z_j/z$. The dyadic cell at the displayed depth containing an interval’s midpoint fits inside that interval. The cells form an alphabetic prefix code, so every fork is one comparison of the loaded identifier with a literal. This is the existing finite-suite lookup method. [Journal lookup construction](code-bits-needed-to-fit-a-finite-sat-suite.md) · [Gilbert and Moore, *Variable-Length Binary Encodings*](https://www.nokia.com/bell-labs/publications-and-media/publications/variable-length-binary-encodings/)

The value-sensitive potential is $\log_2 z$. Its drops telescope on the **actual path** to at most $\log_2 A_{B,c}$. The loads, cursor arithmetic and comparison rounding cost $O(c)$ more. The table covers every possible normalized core in the selected slice, so the leaf can return its precomputed SAT verdict immediately. Larger cores go to exhaustive SAT. Length dispatch can test successive representable dyadic endpoints before refining the selected interval, avoiding truncation of a large horizon literal on a small input.

The tries through $H$ have at most a polynomial in $H$ times the number of cores in instruction slots. Charging their literals and binary control targets adds another polynomial factor. This gives the claimed code budget. The normalization runs at the physical width, and the threshold branches run directly on its output. There is no interpreter multiplier on $\alpha M$.

Consequently, fix $a>\alpha$ and $\epsilon>0$. For all sufficiently large code budgets $C$, **no suite of sufficiently long files whose cores all satisfy**
$$
 M\le (1/\alpha-\epsilon)\log_2 C
$$
**can defeat every $C$-bit program at deadline $aN$**. One $P_H$ fits the budget and passes the entire suite, however much whitespace or repetition was used to enlarge its physical lengths. For $aN^2$ or $aN^3$, the same conclusion holds for every fixed $a>0$. This is a necessary condition on a proposed proportional-time successor. It gives no failure witness against the next program.

## A counterexample to reversing the potential

Take $v=10^d-1$, $d\ge2$. Put the seven forcing clauses from the absolute test in a common prefix. Add a clause $(1,2,t)$, and add $(-1,2,i)$ for every $4\le i\le v$ to make the names dense. Choose any $m$-subset of the
$$
 p=\binom{9\cdot10^{d-1}}3
$$
positive triples on the $d$-digit names. Each optional row costs exactly $3d+5$ bytes including its newline. The two settings $t=3,7$ differ in one ASCII bit. The first file is UNSAT. The second is SAT by setting variables $1,2,3$ false and every other variable true.

For either verdict there are $\binom pm$ different clause sets at one physical length. On the SAT side they even define different assignment relations. Set exactly the three names of a candidate high triple false in addition to $1,2,3$. The assignment survives precisely when that triple was omitted. Quotienting by arbitrary variable permutations loses at most a factor $v!$.

To see sharpness through every sufficiently large byte cutoff $B$, take $d=\lfloor\log_{10}(B/(\log_2 B)^2)\rfloor$, then take the largest $m$ fitting the cutoff. The fixed rows use $O(vd)=O(B/\log B)$ bytes, $m\sim B/(3d)$, and $\log_2(p/m)=2\log_2 B-O(\log\log B)$. Therefore $m\log_2(p/m)\le\log_2\binom pm$ gives the matching lower rate $\alpha$ per physical bit. The loss $\log_2(v!)=O(B/\log B)$ leaves it intact.

A program required to identify the assignment relation from its binary control path must consequently execute at least $(\alpha-o(1))N$ branches on some positive file. **SAT decision on these very files takes a packed scan.** A fixed globally correct solver looks for all eight contradiction clauses, then tests the specified assignment, with general SAT fallback if neither check settles the file. Both checks use the normalized triples in $O(N/\log N)$ time on the family.

There is also a direct counterexample to a bounded potential drop per instruction. Keep every positive setting at one size and just one negative setting. Put the tag in the fixed prefix. One load of its physical word distinguishes the lone negative from all the positives, dropping $\Theta(N)$ bits of completion potential on that run. The size of an assignment relation, or of a graph certifying it, supplies no corresponding sequence of executed instructions. The pointer argument charges operations on a specific suffix. Summing semantic possibilities here cannot extend that charge. [Round 1 execution bound](processing-butterfly-queries-after-the-last-physical-word.md)

## Checks

The new audit matched exact byte-length histograms against an independent inclusion–exclusion count, replayed **78,223 binary threshold comparisons on 7,423 cores**, and checked **1,024 physical one-bit SAT/UNSAT pairs** against full assignment tables. All 10,240 three-name challenges recovered the intended triple-membership bit. At $d=2,m=198$, the physical length is 25,768 bits and $\lfloor\log_2\binom{117480}{198}\rfloor=2104$. At $d=1000,\ m=vd$, integer length arithmetic certifies a rate of at least **0.275697** without materializing the file. Reproduce with `python3 -B normalized_core_clock_audit.py`. [Audit code](../audits/normalized_core_clock_audit.py)

This counts identities of normalized clause sets. Historical priority for this encoded-length coefficient is unverified.
