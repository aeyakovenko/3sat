# A code and its random translate at a self-referential SAT rejection

**Research journal, 24 November 2026.** A SAT disjunct can force a prescribed distribution of raw inputs to be far from every timely rejection. A second distribution has exactly the same small marginals. On almost every input from the second distribution the actual formula is unsatisfiable. If the solver is fast, these become genuine timely rejections whose proof bits are hard to produce even when the verifier is changed *after* the formula family is fixed. The construction changes the previous formula by adding the disjunct. It gives no time separation for unrestricted SAT. The indistinguishability argument is the high-dual-distance lower-bound method for Merlin–Arthur proofs of proximity. [Fischer, Goldhirsh and Lachish](https://cris.technion.ac.il/en/publications/partial-tests-universal-tests-and-decomposability/) · [Gur, Liu and Rothblum](https://eccc.weizmann.ac.il/report/2018/083/revision/1/download/)

## The guard and the actual monitored computation

Use the universal pair language with explicit input $(P,1^k)$, implicit binary input of length $K$, and guest clock $H=2^k$ from the covering construction. Set $s=2^{\lfloor k/4\rfloor}$, $b=k^2$, $d=sk^C$, $L=bd$ and $K=2L$. The implicit input is two arrays $X,Y$ of $d$ symbols of $b$ bits. The ordinary, shifted SAT formula still tests all $2d$ raw symbols as challenges to the same PCPP, with one common $s$-bit header and one $b$-bit shift. Fix its PCPP with perfect completeness, fresh soundness $\sigma=1/4$, and proximity radius at most $1/32$. BGHSV Theorem 2.6 allows those fixed constants. Fix a decoder with bounded polynomial-in-$k$ work per address. Count every raw symbol disclosed by the verifier or its decoder, including through physical formula-word access, in a per-row bound $h=k^{O(1)}$. [Underlying universal pair language and self-reference](exact-sampled-verdicts.md) · [Shifted batch construction](shifted-proof-challenges.md) · [BGHSV, Theorem 2.6](https://people.csail.mit.edu/madhu/papers/2005/bghsv2-full.pdf)

The added disjunct is true if $X\oplus Y$ has binary Hamming distance at most $\lfloor L/16\rfloor$ from a Reed–Solomon codeword. Guess a monic irreducible binary polynomial of degree $b$ and use the resulting field of $2^b$ elements, represented by their coefficient bits. Use the first $d$ distinct binary names as evaluation points. Guess the coefficients of a polynomial of degree less than $u=\lfloor d/4\rfloor$, evaluate at those points, and count the differing bits. Allowing every such field presentation makes the guard uniform. Irreducibility is checked in $\operatorname{poly}(b)$ time by Frobenius powering and polynomial gcds. The coefficient list takes $bu$ bits. A subproduct and remainder tree performs all evaluations in $d\operatorname{poly}(k)$ word operations, including field arithmetic, since both $b$ and $\log d$ are polynomial in $k$. Quasilinear polynomial multiplication and division by monic divisors suffice. The same existing bounded-RAM 3-CNF compiler converts this verifier and the threshold tests with one disjunction into $N=s k^{O(1)}$ encoded bits. The guard may use $d\operatorname{poly}(k)$ steps *once* in the formula. A virtual read of a word of the resulting clause array decodes coordinates of the bounded computation template and fixed data pins. It never performs a full code-membership computation. [Multipoint evaluation](https://www.cs.toronto.edu/~bor/Papers/fast-modular-transforms.pdf) · [Fast polynomial multiplication](https://users.cs.duke.edu/~elk27/bibliography/91/CaKa91.pdf) · [Locally generated RAM clauses](packed-band-transfer.md)

Choose the finite program $P$ to serve exactly this augmented formula to the given correct deterministic SAT solver $S$ and signal its observed rejection. The universal pair language remains fixed and polynomial-time on arbitrary explicit monitor programs. The checker and syntax generator are fixed before this choice of $P$; their template takes program text as data. Let $A$ be this **actual** monitor's timely rejection fiber at $(P,1^k),K$. Membership in $A$ implies that the augmented formula is unsatisfiable. For every fixed $C$, the overhead per simulated solver step is $k^{O(1)}$. As in the previous syntax construction the row clock and its logarithm-sized dimension fields can be bounded before increasing $C$ to exceed the local probe exponent. Every $O(N^e\operatorname{polylog}N)$ solver with fixed $e<4$ finishes within the guest clock for large $k$.

## Two laws on the raw input

For the analysis at each $k$ fix any one legitimate degree-$b$ field presentation. Let $\mathcal C$ be its code, of cardinality $2^{bu}$. Use the following two distributions; their names refer to the universal monitor claim.

* On $\mathcal D_+$ take $X$ uniform in $\mathcal C$ and $Y$ uniform independent in the full array space.
* On $\mathcal D_-$ take $Y$ uniform and $X=Y\oplus Z$ for an independent uniform $Z\in\mathcal C$.

Every sample from $\mathcal D_-$ is farther than relative *binary* distance $1/32$ from $A$. Indeed every modification of at most $\lfloor L/16\rfloor$ among the $2L$ bits leaves the new XOR within that distance of $Z$. The guard still supplies a satisfying assignment, so a correct solver cannot reject there. On $\mathcal D_+$ the XOR is uniform on $L$ bits. The probability of satisfying the guard is at most

$$
 2^{b+bu+H_2(1/16)L-L}=2^{-\Omega(L)}.
$$

Here $2^b$ bounds the number of field presentations and the ball counts individual bits. All $b$-bit strings are valid field elements. There are no invalid-symbol or padding exceptions.

Both laws agree with independent uniform raw symbols on any set of at most $u$ positions among the $2d$ array locations. Projection of the polynomial evaluations on any $u$ or fewer positions is uniform by interpolation. Under $\mathcal D_-$, even conditioning on the entire $Y$, the selected $X$ positions are these uniform evaluations plus fixed offsets. It follows by fixing a deterministic probe path that any computation making at most $u$ adaptive raw-symbol probes has the same transcript law on the two distributions and on independent uniform input. Internal computation and repeated reads are unrestricted.

## Why the sampled formulas really reject

For fixed header and shift let $v$ be the completed deterministic row predicate, $p$ its fresh acceptance and $\widehat p$ its empirical acceptance on the $2d$ translated challenges. For any even $j$ with $j(h+1)\le u$, each of the following expectations is the same on all three raw input laws:

$$
  \mathbb E[\widehat p^j],\qquad \mathbb E[(\widehat p-p)^j].
$$

For the first identity draw $j$ empirical row indices with replacement. Computing one factor reads that row's challenge and at most $h$ more symbols. For the second take independent choices of empirical and fresh coins for each factor and expand the signed product of differences. Each expanded term still computes only $j$ row outcomes, so its probe budget is $j(h+1)$. The polynomial identity is for expectations; no unbounded-probe computation of $p$ is being proposed.

On $\mathcal D_-$, $p\le 1/4$ pointwise by the actual fiber distance, for every fixed proof. The ordinal-blind empirical-versus-fresh moment bound on independent raw input, transferred for the second displayed moment, gives

$$
 \|\widehat p\|_{L^j(\mathcal D_+)} = \|\widehat p\|_{L^j(\mathcal D_-)}
 \le 1/4+\sqrt{j/(2d)}+jh/d .
$$

Taking the largest even $j\le d/[256(h+1)]$ makes the right side less than $3/8$. Union over all $2^{s+b}$ choices and use Markov's inequality at threshold $1/2$. With $C$ chosen so $d/(h+1)\gg s+b$, the chance that any short header and shift satisfies the threshold on $\mathcal D_+$ is $2^{-\Omega(d/(h+1))}$. Combining with the guard probability proves that the *ordinary augmented formula* is unsatisfiable on all but this fraction of $\mathcal D_+$. This conclusion is unconditional for a correct $S$. A claimed fast solver converts these negatives into timely rejections in $A$. [Ordinal-blind moment inequality](exact-sampled-verdicts.md)

The guard also charges an actual rejecting computation. Use the layout with a separate fixed-width literal-sign pin for each raw bit; the rest of the syntax depends only on the lengths and programs. On any rejecting native execution there must be more than $\lfloor L/16\rfloor$ bit positions at which it has observed *both* raw partners $X_j,Y_j$ and they differ. Otherwise, retaining all observed pins, fill any singly observed pair to equal bits and fill unseen pairs by zeros. The remaining forced disagreements are within the guard radius of the zero codeword. A satisfying completion would produce the same execution and an erroneous rejection. Each fixed-width clause includes variable names of $\Theta(\log N)$ bits, so the packed $\Theta(\log N)$-bit input word meets only constantly many such data pins. This costs $\Omega(L)$ input-word reads on every true rejection in this layout. Here $L=N/\operatorname{polylog}N$ up to choices of fixed exponents, and no superlinear bound follows.

Interpolation strengthens the read bound and locates the observations. Let $D$ be the set of bit positions where both partners were observed on a rejecting run, whether equal or different. Let $I$ be **any** set of at most $u-1$ evaluation locations. At these locations choose full field values consistent with every observed XOR bit. Draw a uniform polynomial of degree less than $u$ taking these values on $I$; interpolation makes this affine fiber nonempty. At each other evaluation location its marginal value is a uniform field element because $|I|+1\le u$. Therefore the expected number of observed XOR bits on which its word disagrees outside $I$ is exactly $|D\setminus(I\times[b])|/2$. An individual polynomial attains at most that mean. At a bit with only one observed partner, select the other to produce the polynomial's desired XOR; at an entirely unobserved bit both values are free. Hence the guard has a satisfying completion whenever this mean is at most $\lfloor L/16\rfloor$. A rejecting transcript must satisfy

$$
  |D\setminus(I\times[b])|>2\lfloor L/16\rfloor
  \quad\text{for every } I\subseteq[d],\ |I|\le u-1.
$$

Taking the $u-1$ locations with the largest paired counts leaves at most $(d-u+1)|D|/d$ observed pairs. Thus $|D|>2\lfloor L/16\rfloor d/(d-u+1)\ge (1/6-o(1))L$. This is an unconditional statement about each rejecting native run with the separate raw-bit pins specified above. It counts paired input observations, with a constant number of pins per physical input-word read in that layout.

## Changing the verifier after the formula has been fixed

Choose any other verifier for this same explicit monitor and length with fresh soundness $\sigma'<\theta'$ on inputs farther than $1/32$, with $\sigma',\theta'$ fixed positive constants. For each of at most $2^a$ proposed shared descriptions, suppose one fresh invocation, including bit generation, uses at most $h'$ raw-symbol probes. All its proof answers must form one oracle for that description and input. Let $p_z$ be its fresh acceptance. For every $\ell$ with $\ell h'\le u$,

$$
 \Pr_{\mathcal D_+}[\exists z:\ p_z\ge\theta']
 \le 2^a(\sigma'/\theta')^{\ell}.
$$

For fixed $z$, $\ell$ independent verifier coin strings give a test of mean $\mathbb E[p_z^\ell]$. Its transcript law is identical on $\mathcal D_+$ and $\mathcal D_-$, and on the latter law soundness bounds its mean by $(\sigma')^\ell$. Markov's inequality and the union bound finish. For $a=o(d/(h'+1))$ the probability is exponentially small in $d/(h'+1)$ when that quantity grows. Single-valued, possibly partial, nondeterministic proof-bit validators qualify for the same bound on certifiable fresh acceptance using their bounded-probe completions from the linked note. The other verifier need never be executed by the physical formula.

This is a per-verifier probability bound on one fixed input distribution at the scale, not a union bound over all nonuniform verifier designs chosen after seeing the input. The hard distributions here live on sparse, structured subsets of the full batch space. A single sparse code could not directly replace the entire rejection fiber in the earlier covering theorem at a fast clock. The auxiliary random translate is what provides a far distribution despite the requirement that the actual rejection fiber cover almost all of the ambient cube at the proximity radius. There is no analogous far distribution established here for the original formula without the guard. No step supplies inexpensive truthful proof readers or a running-time lower bound for $S$.

The finite-field audit checks the two input laws and interpolation on partial transcripts. Lean verifies the double-counting step converting uniform column marginals and rejection of every interpolant into the strict paired-read bound. [Finite-field audit](../audits/guarded_code_rejections_audit.py) · [Lean counting lemma](../lean/GuardedPairedReads.lean)
