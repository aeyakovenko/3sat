# Counting work-memory reads that survive a cut

Use a good seed, the $2m$ pins, $p=\lfloor m/2-m/a\rfloor$, $g=m/a^2$ and $\epsilon=2^{-g/4}$ from the [spectral cut construction](spectral-sat-cuts.md). Fix one balanced partition of the pins into $x,y$ after seeing the seed. On almost every data input, **at every cut in the first $N^b$ steps of any fixed correct solver**, at least one of the following happens, for any fixed $b$.

* The prefix inspected more than $p$ distinct pins of $y$.
* The suffix inspects more than $p$ distinct pins of $x$ before the verdict.
* The suffix reads at least $c m/\log^3 m$ distinct work addresses before its first post-cut overwrite of each such address. The constant $c>0$ can depend on the RAM word-width coefficient.

The exceptional probability is $2^{-\Omega(g)}$. The solver can use unrestricted workspace and arbitrarily many post-cut operations. The last quantity charges actual operations even if the address contains an initial zero. In particular this does not assert that every address counted was previously written. Register contents, program counter and subinstruction state together use $O(\log N)$ bits for each fixed solver.

## Giving the suffix adaptive access to the actual memory

The cut estimate extends to vector-valued functions. If the components of $A$ have degree at most $p$ on each $y$-slice and the components of $B$ degree at most $p$ on each $x$-slice, then
$$
 |\mathbb E[f\langle A,B\rangle]|\le\epsilon (\mathbb E\|A\|^2\,\mathbb E\|B\|^2)^{1/2}.
$$
Apply the scalar matrix to all coefficient vectors, or sum its coordinate bounds and use Cauchy–Schwarz. This also explains why comparing two independently reconstructed *entire* snapshots costs no factor depending on snapshot length: map each string to its own unit basis vector. Only the work of reconstructing each side counts.

For a fixed time and possible controller, compute the true prefix up to that time, abstaining on excessive $y$ probes, an earlier halt or a different controller. Its final work array $C$ has $U$ addressable words from an alphabet of $v=2^w$ values. Both $U$ and $v$ are polynomial in $N$. Give the suffix an auxiliary oracle $Z\in[v]^U$ for that initial work array. Simulate ordinary post-cut stores locally. On an incoming read consult the latest local store if present; otherwise consult $Z$. Impose two independent caps, $p$ distinct $x$ coordinates and $k$ distinct oracle addresses, defaulting to zero (an abstention in signed notation) on excess or divergence. For the true array and controller, every assertion is correct.

For each $(x,y)$ expand the signed suffix answer $b(x,y,Z)$ in the binary Walsh characters of $Z$, viewing each word as $w$ bits. A depth-$k$ adaptive *word* tree has Fourier support on characters involving at most $k$ distinct whole-word addresses. This follows by expanding the indicators of its leaves, each fixing at most $k$ words, including for trees which also read $x$ with $(x,y)$ held fixed. Thus at most
$$
 D_k=\sum_{i=0}^{\min(k,U)}\binom Ui(v-1)^i
$$
characters are needed across all inputs. For fixed $y,Z$, the suffix answer has $x$-degree at most $p$. Consequently each Fourier coefficient $\widehat b_\alpha(x,y)$, an average over $Z$, retains the same $x$-degree, even when the paths and oracle addresses vary with $x$. Parseval gives $\sum_\alpha|\widehat b_\alpha|^2\le1$ pointwise. On the prefix side put $A_\alpha$ equal to the character evaluated at its actual $C$, multiplied by the indicator of a qualifying prefix. This factor has $y$-degree at most $p$ for fixed $x$. Its pointwise squared vector norm is at most $D_k$. The vector bound shows that the probability of a successful actual outcome within both probe caps is at most $\epsilon\sqrt{D_k}$ for a fixed cut time and possible controller. This argument supplies genuine replies to an adaptive suffix without a guessed address list or an assumption that memory forecasts are truthful.

There are $N^{O(1)}$ times and controllers in the union, and $\log_2 D_k=O(k\log N+\log(k+1))$. Choose a sufficiently small fixed constant in $k=\lfloor c g/\log N\rfloor$. The union probability is $2^{-\Omega(g)}$. Inclusion of all cuts only requires the *chosen cut time* to lie in the polynomial window. A solver obtaining its answer from a register is covered by the controller factor.

## Checking just the values a suffix forecasts

There is a sharper exact constant for a different operation: the suffix forecasts $q$ address/value pairs and may use those forecasts to determine its own subsequent probes. The analyst tests the forecasts against the prefix memory all at once. For a fixed suffix-side program the resulting list and asserted verdict must have been computed within its $x$-pin cap without consulting the actual prefix memory. Only outcomes on which *all* forecasts are right are counted. If the resulting execution is a correctly completed simulation on that event, the correlation bound applies. Repeated addresses can be deduplicated; contradictory forecasts fail. State the test for exactly $q$ distinct addresses; take a union for variable $q$.

The matrix of the test has rows $C\in[v]^U$ and columns $(Q,b)$ with $|Q|=q$ and $b\in[v]^Q$. Its entry is $1[C|_Q=b]$. Its real factorization norm $\gamma_2$, the smallest product of maximal row-vector and column-vector Euclidean norms in an inner-product representation, is exactly
$$
 G(U,q,v)=v^{-q}\sum_{i=0}^q (v-1)^i\sqrt{\binom Ui\binom qi}.
$$
Accordingly the probability of verified correct forecasts leading to the verdict is at most $\epsilon G$ for one choice of controller and time. The entire suffix description may be chosen from a catalog, charging the catalog size. In particular $G(U,U,v)=1$. A fixed, publicly known set $Q$ also has factor one whatever its size, by equality of two strings. Looking up a data-dependent partial array has a different cost. [Factorization norms in communication, Linial and Shraibman](https://www2.mta.ac.il/~adish/Pubs/Papers/ccfn.pdf) · [Fourier singular-value methods for related pattern matrices, Sherstov](https://web.cs.ucla.edu/~sherstov/pdf/pattern-matrix.pdf)

For the upper bound, represent each alphabet value by a unit vector at a vertex of the centered regular simplex, so different values have inner product $-1/(v-1)$ ($v\ge2$). Each equality indicator is $v^{-1}(1+(v-1)\langle u_c,u_b\rangle)$. Multiply the $q$ factors. At level $i$ the row includes one unit tensor for each $i$-subset of the address space; the column includes tensors only on the $i$-subsets of $Q$. Their norms are $\sqrt{\binom Ui}$ and $\sqrt{\binom qi}$. Rescale the two sides inversely at each level to equal squared norms after distributing its positive coefficient. Then concatenate all levels. The product of the two norms is $G$. On the cut the resulting row and column feature components have the required opposite-side degrees because they are functions of the respective completed transcripts.

For the matching lower bound, view the test matrix $M$ as a kernel between uniform probability spaces. The squared singular-value operator applied to a character (or a tensor of centered single-symbol functions) supported on $i$ addresses has eigenvalue
$$
 v^{-2q}\binom qi /\binom Ui
$$
for $i\le q$, and zero otherwise. Indeed for fixed $Q$ the average over the label $b$ contributes $v^{-q}1[C|_Q=C'|_Q]$. Averaging over $C'$ gives another $v^{-q}$ and annihilates characters not supported within $Q$. Level $i$ has multiplicity $\binom Ui(v-1)^i$. Thus the nuclear norm of $M/\sqrt{\#\mathrm{rows}\,\#\mathrm{columns}}$ is exactly $G$. Every factorization bounds this normalized nuclear norm from above by its product of maximum vector norms, by the Frobenius product inequality. This proves equality for the whole alphabet, including the high-word-width regime. The optimality concerns the matrix factorization, not the strength of every possible argument about RAM reads.

The spectral construction can be recognized, copied to work memory and evaluated by a full-scan solver in word time $O(N/\log N)$ with the stated padding. The third alternative therefore cannot be multiplied by the number of qualifying cut times. An incoming word read at time $u$ may count at every cut since its last store. Large cutoff windows and disjoint address/value forecasts alone do not resolve that overlap. [Finite matrix and trace audit](../audits/spectral_cut_audit.py)
