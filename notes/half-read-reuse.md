# Input rereads or retrieval of nonzero words on an actual SAT run

At every sufficiently large $m$ there is a public sparse graph and a fixed layout of ordinary 3-CNFs of $N=\Theta(m\log m)$ bits with $2m$ independently pinned data bits. On every input each correct solver has a cut immediately after it first sees its $m$th distinct data pin. There is an absolute $\delta>0$ such that **every deterministic SAT solver**, in its own order of input reads, has some input on which its suffix does at least one of the following.

1. It rereads more than $\lfloor\delta m\rfloor$ distinct data pins seen before the cut.
2. It retrieves more than $\lfloor m/[128(1+\lceil\log_2(Uv)\rceil)]\rfloor$ distinct **nonzero** work words from the cut memory. Here $U$ is the address range and $v$ the word alphabet. Only reads preceding the first local overwrite of their address count.

These are $\Omega(N/\log N)$ distinct input rereads or $\Omega(N/\log^2 N)$ distinct earlier-written work words on a single genuine run. The solver may reread zeros any number of times, use input-dependent indirect addressing, and spend arbitrary time between accesses. No hypothesis on SAT's time or on available workspace enters the proof. The graph can be fixed independently of the solver on the specified word RAM. A deterministic uniform construction achieves the same asymptotic orders at every large scale, with different absolute constants. [Explicit expander construction](expander-cut-signs.md) A second, distributional result below counts incoming work addresses including zeros and holds outside an exponentially small fraction of inputs.

## Graph and machine conventions

Use the sparse graph construction on $2m$ vertices with maximum total edge count $O(m)$, and take $\delta=2^{-12}$. Select the fixed constant expected degree large enough that every balanced cross adjacency has binary rank at least $0.9m$ and the independence number is at most $d=\lfloor\delta m\rfloor$ for large $m$. Both properties hold simultaneously with probability $1-e^{-\Omega(m)}$. For the second, the probability of any independent set of size $d$ is at most $2^{2m}(1-\Delta/m)^{\binom d2}$ in the independent-edge construction with edge probability $\Delta/m$. The first is the spanning-row bound in the companion note. Exponential tails also bound the total number of edges by a constant multiple of $m$. Exhaustive finite search makes the choice computable; no efficient uniform graph search is used. [Sparse graph and all balanced cuts](sparse-quadratic-sat-cuts.md) · [Lee, Lee and Oum](https://arxiv.org/abs/1001.0461)

The SAT bit is the parity of the AND of the endpoint bits at every edge. A pin per data bit and a constant number of width-three gate clauses per edge suffice. Use a fixed pin bank followed by the gate records and final pin, and pad pin locations so that a word discloses at most one private data bit for the specified word width. Each accepted instance has a unique satisfying assignment. A subcube with an edge among its free vertices cannot have constant verdict: the coefficient of the corresponding quadratic monomial stays one in its unique multilinear Boolean expression. A correct solver therefore leaves at most $d$ data bits unobserved on any complete run. Use the ordered access-slot convention, and include fixed transient registers in the controller when necessary.

For a balanced set $S_0$, write $x$ for its data and $y$ for its complement. The sign matrix $F$ of the verdict on this split is $(-1)^{x^\top B y}$ up to separate row and column signs. If $B$ has binary rank $b$, this real matrix has norm $2^{m-b/2}$: identical Hadamard rows occur $2^{m-b}$ times before the row signs, and distinct rows are orthogonal. In particular $\|F\|\le 2^{0.55m}$ for every balanced split.

## Recovering the read set without assuming an input order

Assume for contradiction that every suffix obeys both caps in the statement. Call them $r=\lfloor\delta m\rfloor$ and $k$. On an arbitrary run let $S$ be the $m$ positions observed at the cut, and keep its values there. Make every other data bit zero. This is an actual second input to the same solver. Induction on the native prefix gives the identical cut, controller and work memory.

The seen set on the original run can now be recovered from a short description. Record the controller; the at most $r$ nonzero old data pins that the second suffix reads; and the addresses and values of its at most $k$ distinct nonzero incoming work words. Simulate the suffix using these two dictionaries, zero elsewhere and a separate overlay for post-cut stores. The remaining data pins really are zero, while every incoming word whose value is needed is either in the dictionary or really zero. Thus the simulation reproduces the complete second suffix, including any unbounded scan for a first nonzero answer. Write $T$ for its set of probed data pins. Then $|T\cap S|\le r$, and $|S^c\setminus T|\le d$ since this complete run leaves at most $d$ pins unseen. List the at most $r+d$ positions of $T\mathbin{\triangle}S^c$ and recover $S$ exactly.

Put $V(n,j)=\sum_{i=0}^{\min(n,j)}\binom ni$. There are at most
$$
 N^{O(1)} V(2m,r)(k+1)(Uv)^k V(2m,r+d)
$$
possible pairs of read set and controller, since the above code already includes the controller. The standard bound $V(n,\rho n)\le2^{n H_2(\rho)}$ for $0\le\rho\le1/2$ follows by summing probabilities under Bernoulli($\rho$). With the displayed constants the pair count is below $2^{m/8}$ for large $m$: its exponent divided by $m$ is at most $2H_2(\delta/2)+2H_2(\delta)+1/128+o(1)<1/8$.

Some fixed pair $(S_0,c)$ consequently occurs on at least a $2^{-m/8}$ fraction of uniform inputs. Its prefix event is exactly $A\times\{0,1\}^m$ for a set $A$ of at least $2^{7m/8}$ left strings. Once a trajectory has seen only $S_0$ by that cut, changing any unread bit preserves the trajectory and controller. For each $x\in A$ its work memory at the cut is therefore an arbitrary but fixed array $C(x)$ independent of $y$. The argument has removed both the read order and the choice of split from the remaining problem.

## Zero answers can be free

Restrict to the rows $A$ and fix a right string $y$. After the cut the computation is a decision tree on individual $x$ pins and on the words of $C(x)$. Private writes, arithmetic, right pins and public layout are local. A work read served by a local store is also local. The default answer on either private input is zero. Label an incoming work observation by its address and nonzero value, and a positive $x$ observation by its coordinate. An honest path on these rows uses at most $k$ distinct positive work labels and $r$ distinct positive pin labels. A word read many times contributes only one label.

Take the finite tree of paths that actually occur over rows in $A$ for this fixed $y$. There are finitely many rows and each run halts. Order its leaves lexicographically by answer, with zero the least at every node. For each leaf form the product of the indicators for *only its positive labels*. Give the product the sign of the leaf's verdict and weight $2^j$ where $j$ is its rank starting at zero. At any real row, its own term is present. Every lexicographically larger leaf has zero product: at the first divergence it asks the same question and requires a different nonzero answer. All lower weights combined cannot affect the sign. This polynomial represents the sign of the verdict exactly on $A$. No zero query appears among the factors, and the coefficients can be arbitrarily large. It is essential that the suffix is bounded here by the number of *distinct* positive labels on a genuine path, not by the total number of zero answers.

Group identical monomials for each $y$. Across all columns at most
$$
 D=V(m,r)(k+1)(Uv)^k
$$
different row features occur. Indeed the pin part is indexed by a subset of coordinates; the rest lists up to $k$ address/value pairs. Each is a function of $x$ alone. Their linear combination with column-dependent coefficients proves $\mathrm{signrank}(F|_{A,*})\le D<2^{m/16}$ for large $m$.

Forster's sign-rank theorem gives the opposite inequality
$$
 \mathrm{signrank}(F|_{A,*})
 \;\ge\;\frac{\sqrt{|A|2^m}}{\|F|_{A,*}\|}
 \;\ge\;2^{(15/16-0.55)m}.
$$
Deleting rows cannot increase the operator norm. This contradiction proves the claimed unconditional reuse bound. It uses exact correctness on the full surviving row set, which is why the proof allows only a worst-case conclusion when it charges exclusively nonzero work words. Read-restricted branching programs and time–space bounds for quadratic functions have a substantial prior literature. Here the solver itself can read input bits and work words without restrictions for its entire computation. Priority of this precise formulation remains unverified. [Forster](https://www.sciencedirect.com/science/article/pii/S0022000002000193) · [Prior bounds for branching programs reading some bits twice](https://www.sciencedirect.com/science/article/pii/S0304397596001831) · [Beame, Jayram and Saks](https://homes.cs.washington.edu/~beame/papers/branch.pdf)

## How many inputs force genuine nonzero transfers?

The same rank calculation gives a quantitative lower bound on the exceptional mass even when zeros are free. Let $\beta$ be the uniform probability that at least one of the two caps fails, and let $D=V(m,r)(k+1)(Uv)^k$ as above. Then, for large $m$,
$$
 \beta\ \ge\ \frac{1}{64(D+1)^2}.
$$
In particular exponentially many of the $2^{2m}$ inputs force one of the two costs. This estimate need not give a constant fraction at linear pin budgets.

Here one uses an independent uniform fill on unread coordinates in the companion construction. Its completed input is itself uniform: the stopping prefixes partition the cube into cylinders, and conditional on each prefix both completions are uniform within it. Some fixed public fill therefore gives a cheap companion on mass at least $1-\beta$. Use that fill as the simulation default, listing the old data pins on which the observed value differs. Let $J\le 2^{m/8}$ be the same read-set/controller catalog bound. For each catalog entry take just its prefix rows whose companion is cheap. The resulting full-input cylinders are disjoint and cover mass at least $1-\beta$. If $\beta<1/8$, entries of mass less than $1/(4J)$ together have mass less than $1/4$, while entries with conditional expensive-run probability greater than $4\beta$ have mass at most $1/4$ (for $\beta=0$ the positive-mass entries are all exact). Some surviving cylinder has row set $A$ with $|A|/2^m\ge1/(4J)$ and conditional bad mass at most $4\beta$.

For each right string keep only the leaves of cheap original runs. The positive-label polynomial still gives the true sign on those rows, since its genuine leaf is present and dominates. Add the constant $1/2$ to its integer score to give a sign also on zero scores. This constructs a sign matrix $F'$ of sign rank at most $D+1$ on $A$, differing from $F$ in at most a $4\beta$ fraction of entries. The spectral norm of the difference is at most its Frobenius norm, at most $4\sqrt{\beta |A|2^m}$. Thus Forster's bound implies
$$
 \frac1{D+1}\le\frac{\|F|_{A,*}\|}{\sqrt{|A|2^m}}+4\sqrt\beta .
$$
The first term is at most $2\sqrt{J}\,2^{-b/2}$ for cut rank $b$. At the constants above it is below $1/[2(D+1)]$ for sufficiently large $m$. The same separation of exponents holds with the explicit graph's adjusted constants. Rearranging proves the estimate. This last step treats sign-rank without any restriction on the magnitudes of the representing matrix entries.

## Almost every input if zero-valued memory probes count

Let $E$ be the event that the actual suffix at its half-read cut obeys the same caps $r,k$, now counting every distinct incoming work address, also when its value is zero. Let $\lambda=\Pr(E)$ under uniform data. Draw an independent uniform public fill $Y$ for all $2m$ pins. Conditional on the full original prefix, replace just the unobserved data by their entries of $Y$. The two complete runs then have conditionally independent identically distributed suffix inputs. Their joint probability of obeying the caps is $\mathbb E[\Pr(E\mid\mathrm{prefix})^2]\ge\lambda^2$.

For each fixed $Y$, on joint success the preceding read-set description works using $Y$ as the default data. Record the positions of at most $r$ old bits that differ from $Y$ and are read on the companion. A listed bit is the opposite of its public value. The same upper bound $2^{m/8}$ on possible $(S,c)$ applies, even though the catalog depends on $Y$. For each such pair the original prefix sees only $x$, and its true initial work array can be supplied to the adaptive suffix by the work-read argument. In this case the scalar cut norm is at most $\sqrt{V(m,r)/2^b}$: expanding the suffix in the $x$-characters through degree $r$ gives $|\mathcal J|=V(m,r)$ blocks, each a signed version of $F$, and the squared norm of their concatenation is at most $|\mathcal J|\|F\|^2$. The prefix has degree zero in $y$. The additional factor for up to $k$ incoming work words is at most $\sqrt{(k+1)(Uv)^k}$. The qualifying prefix indicator can depend arbitrarily on $x$. On any real row accepted by this test the true verdict is returned. Hence
$$
 \lambda^2\le
 2^{m/8}\sqrt{V(m,r)/2^{0.9m}}\,\sqrt{(k+1)(Uv)^k}
 = 2^{-\Omega(m)} .
$$
This quantifies the cost on the original runs, without a promise on how the solver performs on their completions. Both signs have probability $1/2+o(1)$ by the same spectral bound at zero probes. Conditioning on either sign preserves an exponentially small exceptional probability. [Vector-valued proof for adaptive work reads](spectral-work-reads.md)

## What prevents a time separation

The same explicit layout has two globally correct solvers running in $O(m)=O(N/\log N)$ word operations on every member. Put the pin bank before the ordered edge-gate records and use a running XOR gate per edge. The first solver uses a buffered forward scan to check and pack the pins into $O(m/\log m)$ work words. It scans and checks each fixed-size gate record, retrieves its endpoint bits from the packed array and updates a parity register. It checks the final pin and exact end of input. The second checks the pins and instead reads their original locations by endpoint index at each edge, using only fixed registers. Record validation requires only integer field comparisons and a constant number of packed word reads per record; arbitrary in-range endpoints are allowed. Away from the recognized family use any complete SAT algorithm. Both fast paths are sound on any accepted layout. With no input rereads, the first solver has at most $O(m/\log m)$ distinct prefix-written words available for the later suffix; the second has zero work transfers. Thus the nonzero-word count for a single cut already has a matching-order upper bound here. Further use of this result toward superlinear time needs to force charges at many cuts and bound how often the same actual access is counted. [Lean verification of lexicographic sign dominance](../lean/PositiveQueryLeaves.lean) · [Finite tests of the positive-label sign representation and the coupled completion](../audits/half_read_reuse_audit.py)
