# How many Boolean read histories can defeat a public RAM fingerprint?

Consider a RAM verifier comparing a claimed CPU read history with a genuine memory table. It compares the payloads of a designated window of $T$ reads by evaluating their discrepancy polynomial at $d$ points of $K=\mathbb F_q$. For zero genuine replies a candidate is a binary vector $b$, with polynomial $R(z)=\sum_{j<T} b_jz^j$. One candidate passes a tuple $\mathbf a$ if $R(a_i)=0$ for every $i$. The addresses, writes, and other memory records can be checked exactly in the example below.

Two commitment rules give different answers. With one challenge, a Boolean response affine in its binary coordinates is forced to be honest up to exactly $q/2$ reads. With $d$ challenges a verifier that allows a post-challenge choice from a fixed catalog can accept false histories on *every* tuple. At infinitely many lengths, $\Theta_d((q/T)^d)$ candidates suffice and are necessary, even when every candidate changes at least $2T/5$ replies. Indexed replies in the construction take polynomial time in $\log T$ for fixed $d$. The hard direction for an alternation speedup is binding the CPU to a single history before revealing the test. The construction below identifies a failure of one proposed replacement for that binding. [Earlier fingerprint quantifiers](separate-fingerprint-witnesses.md) · [Field-word polynomial responses](polynomially-consistent-false-ram-reads.md) · [Rabin on fingerprinting](https://www.cs.cmu.edu/~15-749/READINGS/optional/rabin1981.pdf)

## Exactly how many read bits can fixed challenges certify?

For a fixed tuple $\mathbf a$, let $G_{\mathbf a}=\operatorname{lcm}_i m_{a_i}$ and $E=\deg G_{\mathbf a}$, with $G=1$ for an empty tuple. A binary polynomial vanishes on the tuple precisely when it is divisible by $G_{\mathbf a}$. On $T$ binary replies, the joint evaluation map therefore has binary rank exactly $\min(T,E)$. Its kernel consists of all multiples $S G_{\mathbf a}$ with $\deg S<T-E$, including zero. Repeating a challenge or testing a Frobenius conjugate buys zero additional rank.

Each direct bit probe adds at most one to this rank. At a fixed tuple the **best possible rank with $h$ direct probes is exactly $\min(T,E+h)$**. Query the highest $\min(h,\max(T-E,0))$ coefficient positions. In the joint kernel these coefficients must vanish, reducing the allowed degree by that many. Divisibility by the same monic $G_{\mathbf a}$ gives equality. This rank statement also bounds adaptive direct probes on the path of all honest answers.

If the field has at least $d$ different degree-$w$ irreducible binary polynomials, take one root of each in $\mathbb F_{2^w}$. The largest attainable $E$ is then $dw$. For fixed $d$ the supply exists for large $w$, since at most $\sum_{i\le w/2}2^i$ field elements can have degree smaller than $w$, and each full-degree orbit has $w$ elements. Thus **some test tuple and probe locations exclude every nonzero response exactly when $T\le dw+h$**. Above this threshold every test configuration admits a nonzero Boolean response, even with no bound on how the test points were selected. At $h=0,T=dw+1$ the coefficients of $G_{\mathbf a}$ already give an explicit false response for every tuple. This result counts payload bits determined by the verifier. Computing the evaluated sum and generating a locally dense counterfeit carry their own costs. [Lean divisibility and degree cutoff](../upstream-checks/BinaryEvaluationDivisibility.lean) · [Exhaustive small-field rank check](../audits/binary_read_sat_trace_audit.py)

## A sharp threshold for bitwise-affine replies

Let $q=2^w$. An arbitrary binary affine response to $a\in K$ has the form $b_j(a)=b_j^0+\operatorname{Tr}_{K/\mathbb F_2}(c_ja)$. Indeed the trace polynomial is nonzero of degree $q/2<q$, so the trace takes the value 1. Multiplication by nonzero $c$ permutes $K$. Thus distinct $c$'s give distinct linear functionals, accounting for all $2^w$ of them.

If $\sum b_j(a)a^j=0$ for every $a$ and $T\le q/2$, all these responses vanish identically. Let $k$ be the greatest index with $c_k\ne0$. Expanding the trace polynomial, the unique top term from the linear parts has degree $k+q/2$ and coefficient $c_k^{q/2}$. This lies above every constant-response term and below $q$. The field root bound excludes such a polynomial. When every $c_j=0$, the same root bound gives every $b_j^0=0$. At $T=q/2+1$ take $b_0(a)=\operatorname{Tr}(a)$ and $b_{2^i}(a)=1$ for $0\le i<w$, with all remaining coefficients zero. This gives a nonzero false history for every $a$, including zero. The same degree estimate shows that a uniform challenge detects a nonzero affine response rule with probability at least $1/2-(T-1)/q$ throughout the sound range. If the reply bits are quadratic functions of the challenge, the analogous threshold over the 512-element field is 70 slots for an everywhere-false response. [Quadratic bound, exhaustive rank and recovered rules](quadratic-boolean-response-fingerprints.md)

## Covering all challenge tuples by dense false histories

Fix $d\ge1$ and let $s$ tend to infinity through the odd primes. Set
$$
 w=3s,\qquad q=2^{3s},\quad Q=2^{2s},\quad D=dsQ,\quad B=4D,\quad T=B+D .
$$
Then $T<q$ eventually. Define $L(z)=z+z^{2^s}+z^Q$. On $K$ its values are in $\mathbb F_{2^s}$, since raising to $2^s$ cycles the three terms. It is linear onto that subfield, where it acts as the identity. Every fiber therefore has exactly $Q$ points, accounting for all roots even in an algebraic closure of the corresponding fiber polynomial.

Let $m_u$ denote the monic minimal polynomial of $u$ over $\mathbb F_2$. For any tuple $\mathbf a$ form
$$
 M(Y)=\prod_{i=1}^d m_{L(a_i)}(Y), \qquad P(z)=M(L(z)).
$$
This binary polynomial has degree at most $D$, has every root in $K$, and vanishes on the tuple. The values of $m_u$ on the subfield form $J=2+(2^s-2)/s$ distinct polynomials, since the two elements of $\mathbb F_2$ have degree one and every other element has degree $s$. Unique factorization, surjectivity and injectivity of substitution by a nonconstant polynomial give exactly $\binom{J+d-1}{d}$ distinct products $P$.

To force many incorrect reads, choose a primitive cube root $\omega\in\mathbb F_4$ and multiply each $P$ by $U(z)=\sum_{j=0}^{B-1}\operatorname{Tr}_{4/2}(\omega^j)z^j$. Since $w$ is odd and all roots of $P$ are in $K$, $P(\omega^{-1})\ne0$. For $D\le j<B$, the coefficient of $R=P U$ is
$$
 \operatorname{Tr}_{4/2}\big(\omega^j P(\omega^{-1})\big).
$$
There are exactly two ones in each full period of three. This interval has length $3D$, giving at least $2D=2T/5$ ones in total. Products remain distinct and have degree at most $T-1$. Conversely each fixed nonzero binary polynomial of degree at most $T-1$ covers at most $(T-1)^d$ ordered challenge tuples. At least $(q/(T-1))^d$ candidates are necessary. Since $q/T=2^s/(5ds)$, the two catalog bounds agree up to a factor depending only on $d$. A verifier drawing fresh challenges *after* the choice of one fixed nonzero word would accept it with probability at most $((T-1)/q)^d$.

For local evaluation assume ordinary public field representations by irreducible binary polynomials of $O(w)$ bits. Compute $L(a_i)$, its Frobenius orbit, and the product $M(Y)$ by field operations polynomial in $w$. For $e\le ds$, expanding $L(z)^e$ takes at most $3^{\operatorname{popcount}(e)}$ monomial terms before cancellations, by binary powering and Frobenius. Summing over $0\le e\le ds$ takes at most $4^{\lceil\log_2(ds+1)\rceil}$ terms. Thus any coefficient of $PU$ can be evaluated by XORing polynomially many indexed mask bits. This is a single algorithm given the field representation. The catalog cardinality counts possible histories without assuming a fast minimal-length encoding of their indices.

## Allowing direct comparisons at $h$ positions

Give the checker $h$ additional positions with genuine replies. The positions may follow an adaptive path of genuine answers at the fixed challenge tuple. The set of queried positions on that path must be fixed independently of the candidate's disclosed index. A verifier that learns the candidate and targets one of its errors poses a different problem.

Take the least even $m>h$ with $m\ge2$, and suppose $2^m\le D$. With a public primitive element $\omega\in\mathbb F_{2^m}$ use the family of masks $\operatorname{Tr}_{2^m/2}(\lambda\omega^j)$ truncated to $B$ coefficients. Since $m$ is even, it does not divide $w$, hence the primitive element is outside $K$. For fixed $P$, requiring agreement at $h$ positions imposes at most $h$ binary homogeneous equations on $\lambda$. Choose a nonzero solution among the $2^m$ scalars. On the interior $D\le j<B$ the sequence has exactly $2^{m-1}$ ones per period $2^m-1$, since multiplication by the nonzero $\lambda P(\omega^{-1})$ permutes the nonzero field elements. Discarding the last incomplete period gives at least $(B-2D)/2$ errors. Coefficients and a solution of the $h$ equations can again be obtained in time polynomial in $\log(B+D)$ at these parameters, given the field representations and primitive mask element.

To price both forms of checking take $B=6(h+1)D,\ T'=B+D<q$. Every candidate changes at least an $\alpha=(B-2D)/(2T')$ fraction. A single word can then pass at most $(T'-1)^d ((1-\alpha)T')^h$ pairs of evaluation tuples and direct-probe tuples. Let $H$ be the smallest number of such dense words covering every pair. The construction and this bound give
$$
 e^{-1/2}\,2^h(q/(T'-1))^d
 \ \le H\ \le O_d\big((h+1)^d 2^h(q/T')^d\big).
$$
Indeed $1-\alpha=(1+3/(6h+7))/2$, and $2^m\le 2^{h+2}$. Thus the upper and lower descriptions differ by at most $d\log_2(h+1)+O_d(1)$ bits. The lower bound allows arbitrary catalogs and ignores the time to choose a member. Lean proves the joint rectangle-cover count used here, including overlapping rectangles and repeated challenge or probe coordinates. The field construction and density proofs are on paper. [Lean counting theorem](../lean/BinaryHistoryCatalogBound.lean) · [Finite-field audit](../audits/boolean_history_catalog_audit.py)

## A proper SAT file and a branchless RAM read window

For $T\ge1$, force anchors $(X_1,X_2,X_3)=(0,0,1)$ by the seven clauses forbidding each other assignment. For each input bit $x_j$ include
$$
 (\neg s_j\lor X_{2+x_j}\lor X_1).
$$
Use fresh distinct selectors $s_j$ and states $v_j$, set $v_{-1}=X_2$, and impose $v_j=v_{j-1}\lor s_j$ by the three clauses
$$
 (\neg v_{j-1}\lor v_j\lor X_1),\quad
 (\neg s_j\lor v_j\lor X_1),\quad
 (v_{j-1}\lor s_j\lor\neg v_j).
$$
Finally add $(v_{T-1}\lor X_1\lor X_2)$. These are all proper triples on distinct names. Selector $j$ can be set exactly when its input bit permits it, and the final state demands at least one selector. Thus SAT is the OR of the $T$ switches. Taking $s_j=X_{4+j}$ and $v_j=X_{4+T+j}$ gives dense names, and the physical length is $N=\Theta(T\log(T+2))$ bits. Changing any one switch in the all-zero base changes exactly one physical bit (ASCII 2 to 3) and the correct verdict.

One fixed correct SAT program recognizes this exact template and uses a complete decision algorithm on all other inputs. It can recognize the template in $O(N)$ word steps by scanning the header, checking the expected clause count and bound, and comparing expected rows character by character, with the one permitted digit choice per switch. Decimal output and comparison of each index take $O(\log(T+2))$ steps by ordinary word division or a table of precomputed decimal names. Invalid oversized header counts can be rejected from the fast path using the physical length. It stores the switches in order, reads each once in a final sequential loop and accumulates their OR without a data-dependent branch. On the base file the true writes and address-sorted replies are zero. Substituting any dense false read word from the catalog into the CPU side gives a locally consistent accepting CPU path. Every other memory address and payload can stay genuine. This witnesses failure of the displayed link check on one globally correct program with genuinely verdict-sensitive inputs. It charges no additional steps to that program's honest execution.

A separate exact check of the integer bit count would catch every nonzero false trace against this zero base. To retain arbitrary fixed timestamp moments through degree $r-1$, use blocks of $b=2^r$ cells per switch, $r\ge1$. Store the bit $x_j\oplus(\operatorname{popcount}(k)\bmod2)$ at offset $k<b$, and undo this mask before each read enters the OR. On the blank file complement all blocks indexed by the ones of a chosen $R$. For chronological payloads, subtracting the genuine bits from the claimed ones now gives the signed integer polynomial
$$
 \Delta(z)=\left(\prod_{i=0}^{r-1}(1-z^{2^i})\right)\sum_{j<T} R_j z^{bj}.
$$
Indeed the coefficient at offset $k$ has sign $(-1)^{\operatorname{popcount}(k)}$ in a changed block. The root at one has multiplicity at least $r$, so $(z\,d/dz)^u\Delta(1)=0$ for $0\le u<r$ (apply the operator before evaluation). These are the exact integer differences of the timestamp power sums. In characteristic two, the second factor equals $R(z)^b$, so all binary-field challenges still pass. Each direct probe pins at most one block, and the fraction of changed read bits is preserved. The construction uses the standard Prouhet–Thue–Morse moment cancellation. These extra checks refer to the read index and payload in the designated window. Arbitrary prime-field evaluations and general history-verification protocols remain outside this argument. [Allouche and Shallit, *The ubiquitous Prouhet–Thue–Morse sequence*](https://cs.uwaterloo.ca/~shallit/Papers/ubiq15.pdf) · [Nguyen, *A generalization of the digital binomial theorem*](https://cs.uwaterloo.ca/journals/JIS/VOL18/Nguyen/nguyen6.pdf)

The native audit independently solves all 254 proper files with one through seven switches, verifies the single-bit edits, and compares honest and fabricated reads under simultaneous binary-field evaluations and exact integer timestamps through degree four. The field audit separately exhausts all single and paired challenges over $\mathbb F_{512}$, samples $\mathbb F_{32768}$, and calculates the affine nullity on both sides of the threshold in two small fields. The small fields test identities even where $T\ge q$; the asymptotic catalog estimate uses $T<q$. No part of this construction excludes linear time for unrestricted SAT. [Native SAT and moment audit](../audits/binary_read_sat_trace_audit.py) · [Finite-field audit](../audits/boolean_history_catalog_audit.py)
