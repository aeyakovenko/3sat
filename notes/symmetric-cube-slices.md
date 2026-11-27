# Extracting the formal permanent from doubled-row patterns

**Research journal, 24 November 2026.** Let a division-free arithmetic circuit of size $s$ over a field $F$ of characteristic different from two compute $P(X)$ on an $m$-by-$m$ matrix of variables. Assume that $P$ has individual degree at most two and agrees with the permanent on all Boolean inputs. Call a row of a monomial *bad* if it contains zero or at least two distinct variables. Assume every nonzero monomial has at most $q$ bad rows. Retain only monomials that have a single variable in each row. Write their coefficients as a matrix
$$
 C_{\tau,S}=\left[\prod_{i=1}^m X_{i,\tau(i)}^{1+\mathbf 1_{i\in S}}\right]P,
 \qquad \tau:[m]\longrightarrow[m],\quad S\subseteq[m].
$$
Column collisions in $\tau$ are allowed. If $r=\mathrm{rank}_F C$, there is an arithmetic circuit over $F$ of size at most $(s+1)r\,m^{2q+O(1)}$ for the **full formal permanent of order $m$**. The choices of slices and linear-combination constants may be nonuniform.

In particular a representative supported entirely on perfect matchings and invariant as a polynomial under column permutations gives a formal permanent circuit with polynomial overhead. Each row can be squared in arbitrarily many different patterns across the polynomial. The circuit computing it has unrestricted shape and depth. A more general statement below permits nonmatching supports and a low-dimensional span of distinct column translates. The journal's previous argument selected fixed exponents per variable with a bounded number of exceptions per monomial. [Earlier per-entry extraction](degree-two-permanent.md)

## Removing bad rows

For a row $i$, let $E_{ij}$ set all its entries to zero except its $j$th entry, leaving that variable and all other rows untouched. Let $E_{i0}$ set the entire row to zero. The operator
$$
 J_i=\sum_{j=1}^m E_{ij}-m E_{i0}
$$
keeps a monomial if it uses exactly one distinct entry from the row, with either exponent, and kills it otherwise. These operators commute on different rows. Set $D_i=J_i-\mathrm{Id}$. On a monomial $D_i$ acts by zero for a good row and by minus one for a bad row. Consequently $Q=\prod_i J_i P$ can be computed using $\sum_{|I|\le q}\prod_{i\in I}D_i P$. Expanding the latter costs $O((s+1)\sum_{j\le q}\binom mj(m+2)^j)$ gates up to polynomial overhead in $m$. All substitutions preserve the cube, and $J_i$ fixes the formal permanent, so $Q$ still agrees with the permanent there. This also proves that the sum of the columns of $C$ is exactly the indicator vector of the bijections $\tau$. Indeed, reducing each positive exponent to one gives the unique multilinear representative on the Boolean cube, in every characteristic.

## Extracting one column and undoing its powers

Fix a pattern $S$. Replace every entry in row $i$ by $tX_{ij}$ for $i\in S$ and by $t^{-1}X_{ij}$ for $i\notin S$. The Taylor parameter used later is independent of $t$. A monomial of $Q$ whose doubled row set is $R$ receives Laurent exponent
$$
        3|S|-m-|R\mathbin\triangle S|.
$$
Thus the coefficient at degree $3|S|-m$ is the polynomial with precisely the chosen doubled pattern. This holds even if that column is zero. The Laurent output has powers between $-2m$ and $2m$. Multiply by $t^{2m}$ and interpolate from $4m+1$ distinct nonzero values of $t$. At each such scalar the circuit is an ordinary evaluation; this avoids any degree-growth assumption about intermediate gates. For finite $F$, take a finite extension with at least $4m+2$ elements. It has degree $O(\log(m+2))$. Represent its elements in a fixed $F$-basis containing one, implement all arithmetic by polynomially many base-field gates, and read the coordinate of one for the final polynomial over $F$. The bounded-weight coefficient isolation is an elementary Newton-face extraction. [Grochow, Mulmuley and Qiao, §6](https://doi.org/10.4230/LIPIcs.ICALP.2016.34)

In the extracted polynomial substitute $1+uX_{ij}$ in plain rows and the formal square root of $1+uX_{ij}$ with constant term one in doubled rows. Truncate at $u^{m+1}$. Recursively solving for the square-root coefficients only inverts two. Extracting the coefficient of $u^m$ yields
$$
        H_S(X)=\sum_{\tau} C_{\tau,S}\prod_i X_{i,\tau(i)} .
$$
Coefficient arithmetic at each gate costs polynomial overhead. Since $\sum_S C_{\cdot,S}$ belongs to the column span, at most $r$ appropriately weighted columns suffice to express it. Applying those same coefficients to the circuits $H_S$ gives the formal permanent. The bound allows any shorter expression for the indicator vector if one exists.

## Translating columns and counting collisions

Let $d$ be the dimension of the linear span of the polynomials obtained by relabeling all columns of $P$. Suppose every map indexing a nonzero row of $C$ misses at most $j$ column labels. The following rank bound applies:
$$
 r\le d\sum_{a=0}^j \binom{\binom m2}{a}.
$$
For each equality partition of the row indices of $\tau$, fix one representative map $\tau_0$. Every other map with the same partition is obtained by relabeling its image columns. The coefficient vectors $C_{\tau,\cdot}$ in this orbit are linear images of translates of $P$, by extracting just the coefficients at $\tau_0$ for all patterns. Thus they span dimension at most $d$ over $F$. A partition into $m-a$ blocks is encoded injectively by choosing the edges of a canonical spanning forest on its blocks, for example a star rooted at the smallest element of each block. The forest has $a$ edges among $\binom m2$ possible pairs. Sum over the admitted partitions. There is no division by a group order.

For $d=1$ and exact column invariance, every orbit contributes at most one independent coefficient row. If all supports are perfect matchings, there is one orbit, $q=j=0$ and $r=1$. More generally, taking the formal permanent lower bound of the cited preprint as input, a polynomial-size degree-two representative must satisfy $q+\log_m r=\Omega((\log m)^{1/3})$, hence also $q+j+\log_m d=\Omega((\log m)^{1/3})$. Constants apply for sufficiently large $m$ in the stated characteristics. These tradeoffs concern the support and output of arbitrary-depth circuits. Earlier functional lower bounds study other circuit restrictions, and symmetric-circuit bounds impose a symmetry condition on the circuit itself. [VP–VNP preprint, Theorem 1.1](https://hexagonmath.org/2611.00954v1) · [Forbes, Kumar and Saptharishi](https://doi.org/10.4230/LIPIcs.CCC.2016.33) · [Dawar and Wilsenach](https://arxiv.org/abs/2002.06451)

## An exponential obstruction for this extraction

Even a small polynomial that vanishes on the cube can force exponentially many isolated columns in the final linear combination. Take $m=2b$ and pair rows $u,v$. For each pair let
$$
 B=\sum_j X_{uj}X_{vj},\qquad B'=\sum_j X_{uj}^2 X_{vj},\qquad
 A=(\sum_j X_{uj})(\sum_j X_{vj})-B .
$$
Define $\Delta=\prod_{\mathrm{pairs}}(A+B')-\prod_{\mathrm{pairs}}(A+B)$. Its size is $O(m^2)$, each monomial uses exactly one variable per row, the polynomial is invariant under every column permutation and it vanishes on the Boolean cube. For a map $\tau$, let $S(\tau)$ be the first rows of pairs for which $\tau(u)=\tau(v)$. The row of the coefficient matrix of $\Delta$ equals $e_{S(\tau)}-e_{\varnothing}$. In $P=\mathrm{perm}_m+\Delta$, a bijective map forces the weight $w_{\varnothing}=1$ in any linear combination recovering the permanent. Each nonempty subset of first rows is $S(\tau)$ for some nonbijective map: assign a shared column to each marked pair and distinct columns to unmarked partners. Its row equation is $w_{S(\tau)}-w_{\varnothing}=0$. Exactly $2^b$ nonzero pattern weights are therefore necessary and sufficient among these isolated columns. This example has $q=0$, column invariance and a polynomial-size additive perturbation. It bounds the slice-combination method, irrespective of other information available about the circuit.

One can instead retain only perfect-matching supports and drop invariance. In each diagonal $2$-by-$2$ block let $A$ be the diagonal product, $B$ the off-diagonal product, and $B'$ the same off-diagonal product with its first-row variable squared. The same expression for $\Delta$ now has size $O(m)$. For the matching choosing swapped blocks on a chosen subset, its row in $C(\mathrm{perm}_m+\Delta)$ is exactly $e_S$, with $S$ the first rows of those blocks. Again every one of $2^b$ weights must equal one. In these examples no bound on $\mathrm{perm}_m$ has been assumed to build $\Delta$.

## Full row and column symmetry still permits an exponential obstruction

For $m\ge4$ put $L_i=\sum_k X_{ik}$. The following cube-zero polynomial has $O(m^2)$ gates, individual degree two, exactly one entry per row in every monomial, and formal invariance under independent permutations of **all** rows and columns:
$$
 Z=\sum_{j=1}^m\prod_i(L_i-X_{ij}+X_{ij}^2)-m\prod_i L_i.
$$
For a given map $\tau$, its contribution from the $j$th product has doubled set precisely $\tau^{-1}(j)$. Thus the coefficient-row equation for expressing the permanent by the columns of $C(\mathrm{perm}_m+Z)$ with weights $w_S$ is
$$
 \mathbf1_{\tau\,{\rm bijective}} w_\varnothing
      +\sum_j(w_{\tau^{-1}(j)}-w_\varnothing)
       =\mathbf1_{\tau\,{\rm bijective}}.
$$

The complete space of these representations is $w_S=1+\sum_{i\in S}b_i$ with $\sum_i b_i=0$. To see this, put $v_S=w_S-w_\varnothing$ and $T=\sum_i v_{\{i\}}$. Each partition of the rows into fewer than $m$ nonempty blocks gives $\sum_B v_B=0$, using a map with those fibers. Merging just the pair $1,2$ in the singleton partition gives $v_{12}=v_1+v_2-T$, with singleton braces suppressed. The disjoint pair $3,4$ gives the same relation. Merging both gives $-T=0$. The bijection equation now gives $w_\varnothing=1$. For every $|S|\ge2$ the partition into $S$ and the remaining singletons gives $v_S=\sum_{i\in S}v_i$, including $S=[m]$. Conversely any stated weights solve the equations since the fibers partition all rows.

In particular $w_S+w_{[m]\setminus S}=2$. In the relevant characteristics, every complementary pair contains a nonzero weight. At least $2^{m-1}$ isolated slices are required. Permuting rows or columns in individual extracted circuits $H_S$ yields another member of the same collection by the output symmetry. Allowing these relabelings does not reduce the minimum.

Over characteristic zero the exact minimum is $3\cdot 2^{m-2}$. To count the zero weights, choose $S$ uniformly. If two nonzero coefficients $a,b$ obey $a\ne\pm b$, then $0,a,b,a+b$ are distinct. Conditioning on all other memberships gives probability at most $1/4$ of any specified sum. Otherwise all nonzero coefficients are $\pm a$ and, unless they are absent altogether, their zero total forces $k$ of each sign. Complementing the selection in the negative positions shows the sum is $a(B-k)$ with $B$ binomial on $2k$ fair trials. A nonzero target has probability at most $4^{-k}\binom{2k}{k-1}\le1/4$, since the ratio of successive bounds is $(2k+2)(2k+1)/(4k(k+2))\le1$. Choosing $b_1=1$, $b_2=-1$ and the others zero attains probability $1/4$ at the target $-1$.

Over characteristic three the minimum is $5\cdot 2^{m-3}$. In fact at least this many weights survive over every odd characteristic. The distinct-pair calculation still applies. With just two nonzero coefficients of the form $\pm a$, their sum forces them to be opposites and the nonzero target again has probability at most $1/4$. With three or more such coefficients, flip the negative memberships. Three fair trials modulo the characteristic have maximum point mass at most $3/8$. Each additional trial averages translates of the preceding distribution, preserving this upper bound. In characteristic three take $b_1=b_2=b_3=1$ and all other $b_i=0$. Exactly the selections of two of these three give weight zero. The assertions concern linear combinations of individually recovered row patterns and their relabelings. A circuit gate can of course display the cheap vanishing term explicitly.

These transformations would bound the size of a degree-two functional representative if its row defects and coefficient rank were sufficiently small. A deterministic SAT RAM is given neither an arithmetic representative for counting Boolean perfect matchings nor either structural bound. Thus this direction has yielded no elapsed-time lower bound for SAT. Priority for the extraction and its two examples remains unverified. [Finite checks](../audits/symmetric-cube-slices-check.py) · [Lean pattern and obstruction lemmas](../lean/SymmetricCubeSlices.lean)
