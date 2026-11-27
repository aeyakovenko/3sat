# Which dense address tests must contain many real late outputs?

**Research journal, 24 November 2026.** I tried to exclude short programs by classifying the addresses they might print. Even after removing every genuine early output, each dense accepted set with small Fourier norm contains many genuine late outputs. There is a separate obstruction for Boolean tests whose algebraic degree in the address is at most a fixed positive multiple of $\log_2 q$. Both statements hold for the actual interpreter, without a SAT hypothesis. They restrict proposed address tests for the [sampled-batch criterion](hitting-sampled-batches.md).

## A graph indexed by actual short programs

Use exactly the phases $q=2^k$, the Elias gamma code $a(q)$, $d=|a(q)|+\lceil\log_2(q+2)\rceil$, and $N=2^{d+1}$ from the criterion. Write $u=d+1=3k+O(1)$ and identify pool ranks with $\mathbb F_2^u$ in ordinary binary order. An output is the corresponding rank written as a zero-padded $q$-bit word. Let $T=2^q(q+2)^{\lceil\log_2(q+2)\rceil}$ and choose an early clock $D=2^{\lfloor q/2\rfloor}\mathrm{poly}(q)$ with a fixed constructible polynomial. Write $E^{\le D}$ for the ranks printed and halted on exact names of length at most $d$ by $D$ and $E_q$ for the same set at $T$.

The early density $\alpha_k=|E^{\le D}|/N$ tends to zero. Each distinct rank in the early set has a distinct exact name of weight at least $2^{-d}=2/N$. The total eventual program weights for $q$-bit outputs at different $q$ are disjoint portions of a subprobability. In fact this proves $\sum_k 2|E_q|/N\le1$, including all late outputs. It gives no useful computable rate for $\alpha_k$.

Use an Elias delta code $e(k)$ for $k$, of length $\log_2 k+2\log_2\log_2(k+2)+O(1)$. For this fixed routine reserve a constant $c$ for its interpreter header. Let $2b$ be the greatest even integer at most $d-|e(k)|-c$, and put $L=2^{2b}$. Then
$$
L=\Theta\!\left(\frac{N}{k(\log_2(k+2))^2}\right)=\Theta(B(q)).
$$
For clock and code accounting one may feed the routine a fixed self-delimited reserve $c$ along with $k$, choosing $c$ large enough to cover its header and the $O(\log(c+2))$ bits naming $c$. Small phases can be omitted. The index uses exactly $2b$ bits after $e(k)$. All these descriptions have length at most $d$.

Identify the two halves of the index with $x,y\in\mathbb F_{2^b}$. Let $r=u-2b$ and let $\pi$ select $r$ independent coordinates of the field in its polynomial basis. At large phases $0<r\le b$, since $r=O(\log(k+2))$. Define
$$
G=\{(x,y,\pi(xy)):x,y\in\mathbb F_{2^b}\}.
$$
These $L$ rank vectors are distinct. A nonconstant parity character on $G$ has average of absolute value at most $2^{-b}$. To see this, write its exponent as $A(x)+B(y)+C(xy)$ with linear forms over $\mathbb F_2$. If $C=0$, a remaining nonzero linear form is balanced. Otherwise the map $x\mapsto(y\mapsto C(xy))$ is an isomorphism from the field to its binary dual. It is injective because for any nonzero $x$ multiplication by $x$ is onto. Summation over $y$ therefore vanishes for all but the unique $x$ for which this linear form equals $B$. This leaves a normalized answer of $+2^{-b}$ or $-2^{-b}$. An XOR translation of $G$ preserves the magnitudes. This is the standard bilinear character calculation behind small-bias constructions. [Alon, Goldreich, Håstad and Peralta](https://www.wisdom.weizmann.ac.il/~oded/p_aghp.html)

The fixed program enumerates all exact names of length at most $d$ through $D$, marks their valid pool outputs, and chooses the lexicographically first translation $t$ minimizing $|(G+t)\cap E^{\le D}|$. The average over all $N$ translations equals $\alpha_k L$, so the selected overlap is at most $\alpha_k L$. The program now prints the member of $G+t$ corresponding to its own $x,y$. For the field representation, find the first monic irreducible binary polynomial of degree $b$ by trying possible factors up to degree $\lfloor b/2\rfloor$. Even this search uses only $2^{O(b)}=q^{O(1)}$ steps. Listing all points and scoring translations costs $q^{O(1)}$ more steps. Simulating every bounded name costs $2^dD\,\mathrm{poly}(q)=2^{q/2}\mathrm{poly}(q)$, including checking exact consumption, output length and fixed native emulation. Every resulting program halts within $T$ for sufficiently large $q$. In particular
$$
(G+t)\setminus E^{\le D}\ \subseteq\ E_q\setminus E^{\le D}.
$$
This is one actual set of late outputs answering all the tests below simultaneously. Some words of the translated graph might also have early names, which is why the set difference is needed.

For any pool acceptance mask $A$, give its indicator the normalized parity expansion $1_A(z)=\sum_S\widehat{1_A}(S)(-1)^{S\cdot z}$ and put $\Lambda_A=\sum_{S\ne0}|\widehat{1_A}(S)|$. If its density on the $N$ addresses is $\delta_A$, then
$$
 |A\cap(E_q\setminus E^{\le D})|
 \ \ge\ L\left(\delta_A-\frac{\Lambda_A}{\sqrt L}-\alpha_k\right).
$$
Indeed the constant Fourier coefficient contributes $\delta_A$ to the graph average and the other terms together cost at most $\Lambda_A/\sqrt L$. Deleting early graph points costs at most $\alpha_k L$. Consequently a constant-density mask retaining $o(B(q))$ genuine easy outputs must have $\Lambda_A=\Omega(\sqrt{B(q)})$ on those phases. Advice length, semantic certificates, and membership testing time do not enter this bound.

The indicator of a nonempty affine cell has Fourier norm one including its constant coefficient, by expansion over the linear equations of a basis. A parity decision tree with $s$ leaves has indicator norm at most $s$ by summing its accepting leaf indicators. Thus even arbitrary nonuniform dense address tests given by $o(\sqrt{B(q)})$ accepting affine leaves cannot meet the criterion. This calculation bounds the final test as a function of the rank bits. Low-degree invariants of a RAM's memory or control state do not automatically impose this structure on its accepted addresses. [State invariants and their coefficient access](sparse-state-induction.md)

A public reordering gives another application. List the survivors of the early scan in any fixed order computable in $2^{q/2}\mathrm{poly}(q)$ time. There are $M=(1-o(1))N$ survivors. Run the graph index on their **ranks in that order**, printing the corresponding survivor if the graph rank is below $M$. A dense accepted subset among the survivors extends by zero on ranks at least $M$. Its density on the full rank cube remains bounded below. The same Fourier estimate, now without an early-deletion term, applies to this reordered indicator. A public order may use the entire table of early traces if its construction and storage fit the native clock.

## A different list for low algebraic degree

A quadratic predicate can have large Fourier norm, so I tested degree separately. There exists another set of $L=\Theta(B(q))$ distinct, genuinely late easy ranks which hits **every** dense Boolean address polynomial of degree at most $\lfloor k/8\rfloor$ on a constant fraction of the list. The list is constructible at the late deadline, and the coefficients of a test polynomial may have been chosen with unrestricted computation.

Take the same early-deleted pool $V=[N]\setminus E^{\le D}$. For $a=\lfloor k/8\rfloor$, the number of possible coefficients in a multilinear degree-$a$ polynomial on $u$ bits is
$$
M_a=\sum_{i=0}^a\binom ui \le (eu/a)^a < 2^{0.8 k}=q^{0.8}
$$
for all sufficiently large $k$, since $u/a\to24$. Enumerate the $2^{M_a}$ polynomials and their tables on $V$. For a row with support density $p$ on $V$, let $H$ be a uniform $L$-subset of $V$ and let $h$ count its hits. Sampling without replacement gives $\mathbb E 2^{-h}\le(1-p/2)^L$. Therefore
$$
 \Pr[h<pL/4]\le 2^{pL/4}(1-p/2)^L\le e^{-c_0pL}
$$
for some absolute $c_0>0$. Taking all rows with $p\ge1/k$, the expected number failing their respective lower bounds is at most $2^{M_a}\exp(-c_0L/k)<1$. [Finite product estimate](../lean/BatchHitPotential.lean) · [Hoeffding's sampling comparison](https://doi.org/10.1080/01621459.1963.10500830)

Construct a successful list by fixing its sampled points in order. At each position choose the first unused point minimizing the conditional expected number of failures. For a partially fixed sample, let $v$ be the number of remaining points, $n_1$ the remaining support size of a row, $j$ its hits already fixed, and $h_0$ the number of slots left. The numerator of that row's conditional failure probability is the sum of $\binom{n_1}{i}\binom{v-n_1}{h_0-i}$ over indices with $j+i<pL/4$, using the common denominator $\binom v{h_0}$. Thus every comparison is exact. The chosen expectation never increases and the final number of failures is an integer below one. The time is $2^{M_a}q^{O(1)}$ after the early scan, since $N,L$ and the bit lengths of all the binomial coefficients are polynomial in $q$. Both parts and the native simulation overhead fit $T$. A fixed program with a fresh constant header reserve takes the same kind of $2b$-bit ordinal and prints the corresponding selected survivor. Every selected point has a short late name and no short early name.

If an address polynomial is true on a fixed positive fraction $\delta$ of the original cube, its density on $V$ is at least $\delta/2$ eventually. Its support therefore contains at least $\delta L/8$ genuine late easy words for all sufficiently large $q$. In particular any dense successful mask on the target phases must have Boolean algebraic degree **greater than $\lfloor(\log_2 q)/8\rfloor$** as a function of the rank bits. The same conclusion applies after a uniformly computable reordering of the survivor list, with a dense predicate on survivor ranks interpreted over the ambient binary cube.

More generally the conditional-expectation construction applies to an effectively enumerable family of at most $2^{s(q)}$ masks if the complete table of each can be generated in time $U(q)$, the relevant parameters are uniform, and $2^{s(q)}(U(q)+1)q^{O(1)}$ fits with a fixed exponential margin below $2^q$. The union estimate also requires $s(q)=o(L/k)$ for the stated density threshold. If each table costs $2^{q/2}\mathrm{poly}(q)$, every advice bound $s(q)\le(1/2-\epsilon)q$ with fixed $\epsilon>0$ meets both conditions. The earlier SAT-dependent criterion permits advice up to $o(B(q))$, a substantially larger range. Exhausting an alternating verifier's raw witnesses need not meet the deterministic table-enumeration time.

This also excludes a circuit class on the actual rank inputs. A bounded-fan-in Boolean circuit with $s$ gates and $u$ inputs has an $O((s+1)\log(s+u+2))$-bit description on a fixed basis. For $s\le c_1q/\log_2(q+2)$ and a sufficiently small fixed $c_1>0$, all those descriptions and their $N$-bit tables can be exhausted in $2^{q/2}q^{O(1)}$ time. The same deterministic list of late producers for this class therefore hits every dense mask in it. Moreover, any density-$\delta$ mask $A$ with $o(B(q))$ total easy outputs has Hamming distance $\Omega_\delta(B(q))$ from **every** circuit in that class. For a circuit differing on fewer than $\delta N/2$ positions its density is at least $\delta/2$, so it contains $\Omega_\delta(B(q))$ members of the common late list. All but $o(B(q))$ of those positions must differ from $A$. The same distance argument applies separately to the degree-$\lfloor k/8\rfloor$ family above. Thus sparse nonuniform patches to a simple address test do not suffice either. The circuit and approximation lower bounds require the hypothetical successful mask as a premise.

This attack certifies the late production of many actual words in entire classes of proposed masks. It supplies no dense address mask with the required small intersection, and proves no unconditional running-time exclusion for SAT. I have not established priority for these program-indexing consequences.
