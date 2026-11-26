# Encoded length versus variable names for late SAT lookups

Consider the same positive query for $k$ independently addressed $m$-bit tables. The query may occupy $r$ proper ternary clauses. This time measure the **encoded bit length of the baseline DIMACS file**, with arbitrary decimal names and database-dependent preprocessing. Fix $k,r$ and write $S=\min\{h:\binom{h}{r}\ge m^k\}$. For each $b\ge\max(S,m^{1/3})$, put $b'=\min(b,m)$. Then the asymptotically optimal simultaneous scale is
$$
             S\log m+\frac{m\log m}{\log(2+(b')^3/m)}.
$$
More precisely, every representation using at most $C b$ distinct baseline names for a fixed $C$ needs at least a constant times this many bits on some database. There is a representation reaching this length with $O_{k,r}(b)$ names. Constants may depend on the fixed parameters and on $C$. The upper construction gives short query packets too. The order of clauses and redundant duplicate records can be chosen arbitrarily in the lower bound.

Consequently, if the name budget is unrestricted, the exact order of the minimum worst encoded length is $\Theta_{k,r}(m+m^{k/r}\log m)$. A length $O(m)$ representation exists exactly when $r>k$. At $r=k$ the length cost is $\Theta(m\log m)$. Even for $r\ge3k$, where $O(m^{1/3})$ names suffice, insisting on this smallest order of name budget always costs $\Theta(m\log m)$ bits. These are representation thresholds on ordinary SAT inputs.

## Counting clause sets of short files

The $S-r$ name lower bound for positive identity queries implies a baseline length of $\Omega(S\log m)$, since distinct names need distinct decimal identifiers. Each representation also distinguishes $2^m$ tables just by varying the first bank, so some file uses $\Omega(m)$ bits. These two elementary facts suffice when $b>m^{9/10}$, since then $\log(2+(b')^3/m)=\Theta(\log m)$. The same trivial bit bound applies to representations with unlimited names.

For smaller $b$, canonicalize any private names absent from the public query alphabet. At most $3r m^k$ names can occur in those queries. Choosing and assigning canonical names for the $O(b)$ baseline variables costs $O(b\log m)=o(m)$ bits. Once they are chosen, at most $U=O(b^3)$ distinct proper clauses exist. If each baseline has length at most $L$, each contains at most $p=O(1+L/\log(L+2))$ distinct clauses: short strings supply too few distinct records to fit more, even before any renaming. Equivalently choose and minimally serialize one representative per distinct signed triple; their combined length is bounded by a constant times the original length. Distinct clause sets define all answer functions after canonicalization. Taking $p$ no larger than $U$, the count gives
$$
                     p\log_2(eU/p)\ \ge\ \Omega(m).
$$
This follows from $\sum_{j=0}^{p}\binom{U}{j}\le(eU/p)^p$ for $1\le p\le U$ (substitute $p/U$ into the binomial theorem). It implies
$$
                   p=\Omega\left(m/\log(2+b^3/m)\right).
$$
For example put $d=\log_2(2+U/m)$ and substitute $p=\epsilon m/d$ in the increasing function $p\log_2(eU/p)$. Its value is $O(\epsilon(1+\log(1/\epsilon))m)$ uniformly for $d\ge1$. Choose a sufficiently small fixed $\epsilon$. Capacities with $U=o(m)$ are already excluded by the same count. Since $L=\Omega(m)$, recovering bit length from $p$ costs another $\Omega(\log m)$ factor. This proves the length lower bound. [SAT set-pair inequality](how-many-tests-fit-in-the-last-sat-clauses.md) · [Counting baselines with public names](few-names-for-late-lookup-packets.md)

## Packing a block of data into a ternary clause

Use the [subset decoder](few-names-for-late-lookup-packets.md) for the $r$ query pins. It uses $S+o(S)+\operatorname{polylog}m$ names, $O_{k,r}(S+\operatorname{polylog}m)$ clauses and computes all $k$ binary address coordinates. Replace its final bank lookup as follows.

Let $X=2+(b')^3/m$. Pick the largest power of two no greater than $\max(1,(\log_2 X)/24)$, and call it $B$. Thus $1\le B=O(\log m)$ and $B=\Theta(\log X)$. Rounding $m$ up to the next power of two and filling extra table entries arbitrarily increases its size by a factor less than two; the address generator still uses the original $m$. Partition the table into consecutive $B$-bit blocks. The low address bits give a position $j$ in a block. Split the high address into three chunks of nearly equal lengths, with values $a,b_0,c$.

Use shared decoder flags for all values of each high chunk and of $j$. For each $B$-bit mask $z$ compute $D_z=[z[j]=0]$, which takes $O(B)$ gates per mask. For each third-chunk value $c$ and mask $z$ define $K_{c,z}=[H_3=c]\land D_z$. For the data block at high address $(a,b_0,c)$ with mask $z$, put precisely the following data clause in the baseline,
$$
              \neg [H_1=a]\ \lor\ \neg [H_2=b_0]\ \lor\ \neg K_{c,z}.
$$
All flag families are disjoint. After the query selects an address, every clause except the one for the matching high address is automatically true, and that clause holds exactly when the addressed bit is one. Distinct chunk positions use distinct flag names even when the chunk lengths agree. Handle empty chunks as fixed flags. Functional gates and short clauses can use the same three false anchors as the subset decoder. This use of a named small truth table in a literal is related to the journal's [bit-once matrix encoding](compact-bit-projection-of-matrix-mismatch.md).

There are $O_k(m/B)$ data clauses. The number of additional gates, decoder names and clauses is
$$
       O_k\big((m/B)^{1/3}2^B+B2^B+\operatorname{polylog}m\big).
$$
Here $2^B=O(X^{1/24})$, $X=O(m^2)$ and $b'\ge m^{1/3}$. Thus this expression is $O_k(b')$ and $o(m/B)$ for large $m$. For the first bound use $m^{1/3}X^{1/24}=O(b')$ and absorb the smaller terms. Assign dense identifiers to all used names. Each clause costs $O_{k,r}(\log m)$ explicit bits. The resulting bound is $O_{k,r}((S+m/B)\log m)$, which has the asserted order for every budget. This proof permits arbitrary bits of preprocessing in constructing the baseline. The result accounts for bytes of the actual SAT formula, not time spent by the SAT solver. [Lean guard and mask proofs](SharedChunkGuards.lean) · [Finite packed lookup checks](positive_subset_flags_audit.py)

## Opposite verdicts at the same actual last load

The encoded-length order and the sharp threshold $r>k$ survive two extra requirements. The same baseline must answer a **signed** query, returning SAT iff $\bigwedge_h x_h(q_h)=e$ for a tag $e\in\{0,1\}$. Its two packets at a fixed $q$ must differ by exactly one physical ASCII bit. The positive tag gives all the lower bounds.

For the upper bound use a proposed output bit $a_h$ for each bank, and in its shared mask library compute $D_z=[z[j]\ne a_h]$. The same ternary data clauses now force $a_h$ to the actual selected bit. Compute the AND of the $k$ forced bits. In addition to the $S$ ordinary subset flags, give each possible index $i$ two tagged flags. Each implies the ordinary $y_i$ and forces the AND to its corresponding tag. For the least element of the query subset pin the tagged version, and for each of the remaining $r-1$ elements pin the ordinary version. On an honest choice all unneeded flags may be false. Give the two flags of each index distinct decimal identifiers with identical prefixes and final digits 2 and 3, avoiding existing identifiers, at an $O(S)$ increase in the name range. All actual names still have $O_{k,r}(\log m)$ digits. The sign, the anchors and every other byte of the query stay fixed. The two final digits differ in precisely their ASCII low bit.

To make this an actual last-load pair, use the [aligned packet layout](literal-profiles-at-the-last-clause.md). Put one baseline clause and $r-1$ fixed true padding clauses in each of the interchangeable data packets, with the anchor clauses and header in a public region. The number of source clauses is $O_{k,r}(S+m/B)$. One packet per native word of a sufficiently large fixed logarithmic width, plus power-of-two whitespace padding, therefore preserves the encoded-length upper bound. For a fixed database, assign these data packets in order to the first distinct packet addresses a deterministic correct solver reads. A halt before the last discovery, or a blind overwrite of an unseen packet, would make the two sign choices indistinguishable on some completion. Correctness thus forces a last load. The two sign choices at its address now give real files with a common cold execution prefix, a one-bit difference and opposite verdicts. This strengthens the physical layout conclusion; the two genuine continuations can still both be fast.
