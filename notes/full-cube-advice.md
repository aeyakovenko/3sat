# A circuit consequence of linear-time SAT for a fixed language of bounded computations

**Research journal, 24 November 2026.** Fix an efficient ordinary **plain** universal RAM interpreter $V$. Its input is a finite binary program of known length. It can compile any fixed native algorithm accepting raw data by adding a fixed header, with at most polylogarithmic time overhead at the clocks below. This is a choice of auxiliary interpreter and leaves the SAT machine unchanged. At length $q$ put

$$
N=2^q,\qquad T(q)=2^q(q+2)^{\lceil\log_2(q+2)\rceil}.
$$

Let $A_q$ consist of words $x\in\{0,1\}^q$ for which **no** program of length at most $q-2$ prints exactly $x$ and halts on $V$ by $T(q)$. More than half the cube belongs to $A_q$, because there are only $2^{q-1}-1$ eligible names. The language $A=\bigcup_{q\ge2} A_q$ is decidable in $2^{2q+O((\log q)^2)}$ time by direct simulation. This section uses ordinary program lengths. Prefix programs in the [smaller-pool argument](hitting-sampled-batches.md) pay a separate cost for the phase.

**Conditional conclusion.** If explicit SAT takes deterministic worst-case $O(n)$ time on the unrestricted logarithmic-word RAM, there are constants $\epsilon,c>0$ such that at every sufficiently large $q$, every bounded-fan-in Boolean circuit of at most $c\,2^q/q$ gates differs from $1_{A_q}$ on at least $\epsilon 2^q$ inputs. Thus a way to exclude linear SAT would be to approximate this one explicit language on all but $o(2^q)$ inputs with $o(2^q/q)$ gates at infinitely many lengths. A weaker sufficient construction is any fixed positive-density family of sets, described by circuits of that size, with $o(2^q)$ members outside $A_q$.

## Constructing a set that detects errors

Use a fixed $0<\delta\le1$, taken rational, and let $K=2^{q-a}$ for a large fixed integer $a$. Choose a uniform $K$-subset $H$ of the cube. For every fixed $S$ of size at least $\delta N$ the product-moment estimate gives

$$
\Pr_H[\,|H\cap S|\le\delta K/2\,]
\le 2^{\delta K/2}(1-\delta/2)^K
\le \exp[-(1-\ln 2)\delta K/2].
$$

This is a probability over the choice of $H$ for one fixed set $S$. Fix a deterministic verifier $P(q,z,x)$ taking at most $2^q\mathrm{poly}(q)$ time, for advice $z$ of length at most $\eta K$. Choose a positive rational $\eta$ so small that $\eta\ln 2 < (1-\ln 2)\delta/2$. A union bound over the fewer than $2^{\eta K+1}$ advice strings gives an $H$ which meets every density-$\delta$ acceptance set $\{x:P(q,z,x)\}$ in more than $\delta K/2$ places, for all sufficiently large $q$. The verifier can also have a fixed number of alternations with the same branch and quantifier-length bounds, since under the SAT assumption it can first be compiled into a deterministic verifier with $2^q\mathrm{poly}(q)$ time. [Sampling without replacement and finite checks](hitting-sampled-batches.md) · [Compilation of fixed alternations](linear-quantifiers.md)

The deadline makes a direct exhaustive search for $H$ too expensive. Here is how to print any particular indexed entry of **one common** $H$ in time $N\,\mathrm{poly}(q)$ under the linear-SAT hypothesis. Encode $H$ by its $N$ membership bits. Check it has exactly $K$ ones. For every advice $z$, existentially supply the $N$-bit truth table $Y$ for its accepted set. Check its weight and its overlap with $H$ by scanning the two arrays. Universally select one $q$-bit index $x$ and verify $Y_x=P(q,z,x)$. That last comparison forces the entire supplied table to be correct, while charging for only one execution of the verifier per branch. If the table has at least $\delta N$ ones, require overlap greater than $\delta K/2$. Advice of varying length can be represented by a padded string and an explicit length. All quantified data and branch work fit $N\,\mathrm{poly}(q)$.

Denote this qualification predicate by $G(H)$. For an ordinal $i<K$ and bit position $j<q$, ask whether there exists $H$ satisfying $G(H)$, with every lexicographically earlier $N$-bit string failing $G$, such that the $j$th bit of the $i$th member is one. One scan finds the selected member of a supplied table. Lexicographic comparison costs $O(N)$ bit operations. The number of alternations stays fixed through the copy of $\neg G$ and the comparison against earlier strings. By linear SAT this bit query takes $N\,\mathrm{poly}(q)$ deterministic time. The least qualifying table exists and is unique, so all $q$ queries recover the same indexed word. Trying each of the $N$ membership bits sequentially by self-reduction would have exceeded this clock.

Compile a fixed decoder for $P,\delta,\eta,a$ and the assumed SAT solver. On a raw payload of length $r$ the decoder sets $q=r+a$ and takes the payload as the ordinal $i<2^r=K$. It runs the bit queries and prints the word. Choose $a$ large enough to pay for the header and two bits of savings. More explicitly one fixed decoder can read a self-delimiting parameter $a$ before the payload, consuming $O(\log(a+2))$ header bits in addition to a fixed constant independent of $a$. All these programs have length at most $q-2$, and their $N\,\mathrm{poly}(q)$ running time, including reference simulation, is eventually below $T(q)$. Consequently $H\subseteq \{0,1\}^q\setminus A_q$. We have proved that every dense acceptance set of a short-advice verifier actually contains a positive fraction of $N$ compressible words, with the fraction allowed to depend on the verifier and on $\delta$.

Set $\delta=1/4$ and take $P$ to evaluate a circuit description on $x$, rejecting malformed advice. Bounded-fan-in circuits over a fixed finite Boolean basis with $g$ gates admit $O(g\log(g+q)+\log(q+2))$-bit descriptions. Thus for a sufficiently small constant $c>0$ every circuit in the statement fits the advice and evaluation budgets. If its accepted set has density below $1/4$, it misses more than $N/4$ words of $A_q$. Otherwise it accepts more than $\delta K/2$ words outside $A_q$. Take $\epsilon$ smaller than both resulting positive constants. The claim about weaker dense one-sided constructions follows by using a fixed rational $\delta$ below their lower density.

## Rare random results on the full cube

There is a parallel statement for one fixed sampler which returns an explicit mask in $N\,\mathrm{poly}(q)$ time. Fix $\delta>0$. Under linear SAT, constants $\epsilon,\lambda>0$ exist such that at all sufficiently large lengths

$$
\Pr[\,|S|\ge\delta N,\ |S\setminus A_q|\le\epsilon N\,]\ \le\ 2^{-\lambda N}.
$$

For a random $K$-set $H$, average the earlier exponential tail over the sampler, giving some $H$ whose bad-event probability is at most $2^{-\beta K}$, where $\beta=(1-\ln 2)\delta/(2\ln 2)$. Fix a rational $0<\beta'<\beta$. Count random tapes satisfying $|S|\ge\delta N$ and $|S\cap H|\le\delta K/2$, using a uniform integer cutoff $D=N(q+2)^b$ exceeding the fixed sampler clock, at most one fair bit per step and the empty mask on timeout. The quantified relation costs $N\,\mathrm{poly}(q)$. For a positive count $C$ let $e$ be its deterministic estimate with $2^e/4\le C\le8\cdot2^e$. Qualify zero counts automatically and otherwise require $e\le D-\lfloor\beta'K\rfloor$. An $H$ with bad probability at most $2^{-\beta K}$ qualifies for all large $q$. Every qualifying $H$ has bad probability at most $8\cdot2^{-\lfloor\beta'K\rfloor}$. Apply the same least-table bit queries and length-aware decoder. This gives the stated constants, including the probability of the unrecognized successful runs. The words in the set may depend arbitrarily on the whole random tape. [Projected approximate counts and their deterministic complexity](near-native-counting.md)

## An attempted circuit upper bound

One possible approximator uses advice to describe which regions have a timed program output. Partition the cube into equal blocks and keep the blocks with no such output. For a set of $L$ easy inputs, the occupancy bits for the least power of two at least $2L$ blocks give a set of density at least one half. The construction costs $O(L+\log N)$ bits. At the plain-program cutoff $q-2$, $L$ is always $\Omega(N)$ on an efficient length-aware universal interpreter. A fixed machine maps every raw $(q-a)$-bit word to its distinct zero-padded $q$-bit output, choosing a constant $a$ large enough for the header. Thus the generic block construction only gives linear-sized advice. Producing a positive-density acceptance set with $o(N)$ advice and $o(N)$ easy members still requires a construction exploiting which programs finish. The proof above supplies no such construction.

Another attempt changes the interpreter by assigning a long header to general-purpose programs. That can make their contributions an arbitrarily small *fixed* fraction as the interpreter varies. The constants $c,\epsilon$ and the length of the compiled hitting-set decoder also depend on the interpreter. The attempted contradiction needs errors tending to zero on one fixed interpreter, or an explicit calculation beating its particular constants.

## An unconditional obstruction across two halves of the input

At every sufficiently large length, a protocol approximating $1_{A_q}$ to a sufficiently small constant error under uniform inputs needs $\lfloor q/2\rfloor-O(1)$ bits of worst-case two-party deterministic communication when the two parties hold the first and second halves. This restricts attempts to obtain the desired approximator by advising each half separately. A general Boolean circuit may use information from both halves throughout.

Fix a sufficiently large constant $r$. Let $s$ be the largest multiple of $r$ not exceeding $\lfloor q/2\rfloor$. View the first $s$ bits from each half as vectors $x,y$ over $\mathbb F_{2^r}$, with $s/r$ coordinates apiece. Keep the leftover bits free. Define $G$ by $\sum_j x_j y_j=1$ in this field. Every word of $G$ has a short, fast program. Its payload contains all bits except the $r$ bits for $y_i$ at the first index $i$ with $x_i\ne0$. Such an index exists on $G$. Recover $q$ by adding $r$ to the payload length, then solve the one field equation for $y_i$. The field can be set up once per run by deterministic search for an irreducible degree-$r$ polynomial. This costs a constant depending on $r$, and the scans take $O_r(q)$ operations. Take $r$ large enough to cover the fixed header including a self-delimiting specification of $r$, with two bits to spare. All these outputs already arrive within $q\,\mathrm{polylog}(q)$ native steps.

For every rectangle $U\times W$ in the two halves,

$$
\left|\,|G\cap(U\times W)|-2^{-r}|U||W|\,\right|
\le 2^{(q-s)/2}\sqrt{|U||W|}.
$$

Expand the indicator using the $2^r$ additive characters on the field. The trivial character gives the displayed mean. For any other character $\chi$, the active matrix $(\chi(\sum_j x_j y_j))_{x,y}$ has orthogonal rows of squared norm $2^s$. For $x\ne x'$ the map $y\mapsto\sum_j(x_j-x'_j)y_j$ is onto and all its fibers have the same size. Repeating rows and columns to account for $q-2s$ free bits multiplies the operator norm by $2^{(q-2s)/2}$. Cauchy–Schwarz gives the rectangle bound since the expansion coefficients have absolute value $2^{-r}$. [Inner-product and two-source discrepancy methods, Chor and Goldreich](https://doi.org/10.1137/0217015)

The accepted set $S$ of a protocol using $t$ communicated bits is a disjoint union of at most $2^t$ rectangles, using the usual convention of a result at each leaf. If the final result is local to one party, sending one last bit suffices. Summing the discrepancy bounds and using $\sum |U||W|\le N$ gives

$$
|G\cap S|\ \ge\ 2^{-r}|S| - N 2^{(t-s)/2}.
$$

For $|S|\ge N/4$ and $t\le s-2r-6$, at least $2^{-r}N/8$ accepted inputs lie outside $A_q$. If $|S|<N/4$, more than $N/4$ members of $A_q$ are rejected. Fixing the random coins gives the same obstruction to protocols having that worst-case communication bound on every run and smaller average error. This argument uses no SAT solver. A separate construction gives a loss of $O(\sqrt q)$ simultaneously across every balanced coordinate partition. [One family for all the cuts](all-cuts-plain-outputs.md)

The basic selection of a set hitting all dense advice choices is already present in Buhrman, Fortnow, Koucký and Loff, Lemma 2, for the **unbounded** plain Kolmogorov-random strings. They can search for the first successful sequence without a runtime cap. The calculation here adapts that argument to a specified exponential deadline, includes constant-fraction contamination, and gives the conditional implication for linear SAT. Priority of this deadline-specific implication has not been established. Korten and Santhanam study conditional constructions of individual time-bounded random strings and range avoidance. [Buhrman, Fortnow, Koucký and Loff](https://iuuk.mff.cuni.cz/~koucky/papers/bppr.pdf) · [Korten and Santhanam](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2025.35)

Lean checks the finite counting implication, the agreement of all the least-table bit queries and the plain-name capacity. The time estimates and the reduction to these finite statements are manuscript proofs. [Finite selection argument in Lean](../lean/FullCubeSelection.lean)
