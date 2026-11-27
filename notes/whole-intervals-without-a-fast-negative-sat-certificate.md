# Whole intervals without a fast negative SAT certificate

The fixed unary nondeterministic RAM language $H$ of native time $t(n)=\Theta(n^2)$ lies outside both $\mathrm{NTIME}(o(n^2))$ and $\mathrm{coNTIME}(o(n^2))$. For the negative side there is a stronger statement. Fix any finite list of nondeterministic programs which, on $1^n$, only accept when $H(1^n)=0$. There is $c>0$ and there are infinitely many of the original source intervals $[b,e]$ on which **every** $n=b,\ldots,e-1$ is an actual negative length and **none** of the programs has an accepting branch within $c n^2$ instructions. Different lists can have different intervals. A negative program may be incomplete or may run for unbounded time. This concerns the verdict of the existing source and uses its existing encoding. [The fixed native machine and its two clocks](a-fixed-unary-ram-source-for-physical-sat-compilers.md)

## Moving the input back one place

The source uses $b=B_j$, $e=B_{j+1}-1$, with $B_{j+1}=2^{B_j^3}$. Each interval is assigned an opponent code and an integer quota $p$, every pair infinitely often. At $b\le n<e$, it simulates the assigned opponent on $1^{n+1}$ with an $n^2$ host-work budget. At $e$ it deterministically complements the result of running that program on $1^b$ for $b^2$ guest steps. On a fixed opponent, simulation overhead per guest instruction is bounded uniformly in the interval and quota. This is the delayed diagonalization in the source construction. [Žák, *A Turing machine time hierarchy*](https://doi.org/10.1016/0304-3975(83)90015-4)

Given sound negative programs $V_1,\ldots,V_s$, write a fixed opponent $Q$. On $1^k$ with $k\ge2$, put $m=k-1$ and recover the quota from the interval of $m$. Nondeterministically select a $V_i$ and simulate it on $1^m$ for $\lfloor m^2/p\rfloor$ of its native instructions. Accept exactly on a timely accepting branch. A physical scan or one-time truncated unary copy costs $O(k)$; the fixed rounded word-width change needs at most constantly many limbs and constant-depth sparse-address simulation as in the source. Each branch costs $O_s(m^2/p+k+\operatorname{polylog} k)$ with a constant independent of $p$.

After constructing $Q$, choose a sufficiently large fixed $p$ so that all its branches fit the host budget on the interiors of sufficiently late intervals assigned to $(Q,p)$. At **each** such $n$ one now has the exact equation
\[
                H(1^n)=Q(1^{n+1})
                 =[\ \text{some }V_i(1^n)\text{ accepts by }\lfloor n^2/p\rfloor\ ] .
\]
If the bracket were true, soundness would give $H(1^n)=0$ and the displayed equality would give $H(1^n)=1$. Thus both sides are zero. This proves the whole-interval assertion, including a common clock for the list. A complete $o(n^2)$-time recognizer of the complement would violate it. For the ordinary nondeterministic side the original source uses its endpoint to force disagreement with every fast positive candidate.

There is also a direct check with the unshifted proposed complement $Q$ itself. On a sufficiently late faithful interval one would have $Q(n+1)=1-Q(n)$ through the interiors. The gap $e-b$ is odd since both neighboring $B$'s are even. This gives $Q(e)=1-Q(b)$. The endpoint says $H(e)=1-Q(b)$, contradicting $H(e)=1-Q(e)$. It gives a disagreement without identifying a whole negative interval. The one-place shift above supplies the stronger statement.

## A necessary subformula size at every length of such an interval

Let $\Phi_n$ be any uniformly clause-indexed family of proper ordinary 3-CNFs with satisfiability exactly $H(1^n)$. Suppose $t^{O(1)}$ clause indices suffice, the length/directory is obtained in $o(t)$ work, and fetching a designated clause with its three full names costs $\lambda(t)=(1+\log t)^{O(1)}$ native operations, including reading and comparing the representations. For example, bounded RAM acceptance has suitable locally generated named formulas. An arbitrary raw-bit interface for variable-length files alone need not implement this clause-fetch operation. [Local native formula layout](local-sorting-for-parsimonious-ram-encodings.md) · [Jahanjou, Miles and Viola, *Local Reductions*](https://eccc.weizmann.ac.il/report/2013/099/)

On some infinitely recurring set of entire source interiors as above, all the $\Phi_n$ are unsatisfiable and their minimum unsatisfiable core size $q_n$, measured in original clause occurrences, satisfies
\[
                 q_n\ \ge\ \log_2 t-O(\log\log(t+2)).
\]
Indeed guess a set of $q$ clause indices below this threshold. Fetch the clauses, compare their names and give the occurring names dense identifiers. Reject the guess if there are $q$ or more occurring variables. A minimally unsatisfiable family on $v$ occurring variables has at least $v+1$ clauses by Tarsi's lemma. Hence a smallest core of size $q$ passes this extra test. Exhaust the at most $2^{q-1}$ assignments on the dense names in $O(q\,2^q)$ native operations. This only accepts a genuinely unsatisfiable subformula. For $q\le\lfloor\log_2 t-C\log_2\log_2(t+2)\rfloor$ and a sufficiently large constant $C$ the check, all fetches and renaming cost $o(t)$. The interval theorem forbids such a branch at every interior length of a suitable sequence of intervals. [Aharoni and Linial, *Minimal non-two-colorable hypergraphs and minimal unsatisfiable formulas*, reporting Tarsi's lemma](https://doi.org/10.1016/0097-3165(86)90060-9)

Suppose instead that ordinary SAT has a deterministic $O(N^K)$ solver for a fixed $K\ge1$ on its actual encoded bit length. The negative checker can run it on the $q$ selected clauses alone, returning the opposite bit. The renamed subformula has $O((q+1)\log(q+2))$ physical bits. Decimal digit trie insertion takes time linear in the fetched names, and the new dense names can be printed in $O(q\log(q+2))$ time. The native word width on this smaller file can be simulated in the source width by masking, with native memory addresses fitting in a fixed number of limbs. Thus the check costs
\[
 O\bigl(o(t)+(q+1)\lambda(t)+[(q+1)\log(q+2)]^K\bigr).
\]
Here the $o(t)$ term is common setup and the other constants do not depend on a cutoff. Run this fixed checker on all $q$ by guessing one $q$, retaining the soundness of its quick branches. On its hard intervals, every minimum core therefore gives
\[
 (q_n+1)\lambda(t)+[(q_n+1)\log(q_n+2)]^K=\Omega(t).
\]
For $K>1$ and polylogarithmic $\lambda$ this forces $q_n=\Omega(t^{1/K}/\log t)$. For $K=1$ it gives $q_n=\Omega(t/(\lambda(t)+\log(t+2)))$, retaining the possible cost of fetching a single clause. This statement is conditional on the hypothesized ordinary solver. The previous logarithmic core bound is unconditional. A finite set of fixed sound proof checkers can be included in the same list, giving hard intervals simultaneously for all of them. These are checker-time and core-structure statements on the locally obtained genuine negative files; they do not establish superlinear SAT decision time on submitted packed inputs.

## How far positive queries to nested predicates can go

Consider an abstract system indexed by lengths. An equation at position $i$ either copies or negates a Boolean functional $G_i(P,Q)$ of the queried predicates $P,Q$. Allow arbitrary coordinate shifts and joint use of multiple lengths, assuming each functional is monotone as either predicate gains new accepted lengths. We ask for a nested pair $Q\subseteq P$ whose Boolean difference $P\setminus Q$ solves every equation. This question retains the signs and positive query access and discards the complexity of recognizing the two predicates.

Let $E$ be the set of negating positions. For a set $X$ of positions put $P=E\cup X$ and $Q=E\cap X$. At a copying position the difference equals $X$ and at a negating position it equals its complement. The map $X\mapsto\{i:G_i(E\cup X,E\cap X)\}$ is monotone. Take its least fixed point, the intersection of all its pre-fixed points, or iterate from the empty set in a finite system. The resulting nested pair satisfies all equations. Thus positive black-box uses of the two candidate predicates and a designated output sign per length cannot by themselves contradict a difference representation. This construction makes no claim that the resulting predicates have short native clocks, or that the actual source belongs to a Boolean complexity class.

Core Lean proves the sound-negative-copy contradiction, the unshifted odd-gap disagreement and the monotone fixed-point realization on an arbitrary index domain. The native simulation and the bounds for actual refutations are manuscript arguments. [Lean proofs](../lean/SignedUnaryInterval.lean)
