# How the range of old RAM addresses changes the late SAT lower bound

For the aligned DIMACS family, the number of **possible addresses across databases** determines a sharp bound in the affine charging model. Fix a deterministic exact SAT decider. If at each dyadic size the nonzero work cells at its cut always lie in a common set of $O(N\log^K N)$ addresses for fixed $K$, then both continuations of some opposite one-bit pair incur $\Omega(N/\log^2 N)$ charged steps. This holds for arbitrarily large lengths even with unlimited prefix time. The charged instructions process old data nonlinearly, branch on them, or use them for addressing. All affine operations on the old state and all knowledge of the pending query are free. A globally correct program with $O(N)$ total time on the canonical files and a common $O(N)$-word bank attains the rate. The possible addresses in a bank may be anywhere in the native address space.

One can also let the database choose the bank. At an interval of $s$ rows, permit any fixed menu of $2^{o(s)}$ eligible banks of that size, with the little-o bound uniform across dyadic intervals. Give the chosen index to the suffix for free. The same lower bound holds. In particular it applies to old nonzero cells covered by $o(s/\log N)$ intervals of total length $O(N\log^K N)$ words. The interval starts and lengths can depend arbitrarily on the actual prefix. One logarithmic word per endpoint suffices to describe this cover. [Physical cut, charged instructions and matching packed algorithm](nonlinear-work-after-the-one-bit-sat-cut.md)

## An unrestricted bound using the memory on the same pair

There is a bound that uses the actual common prefix of the two files, with no assumption about the solver's address ranges on its other inputs. Fix a sufficiently small absolute $\epsilon>0$. For a local $s$-row cut of native width $w_s$, let
$$
 m_s=\lfloor\epsilon s/w_s\rfloor,\qquad
 H_s=\min\{\text{total number of word positions in at most }m_s\text{ address intervals covering all nonzero old work cells}\}.
$$
A word position in a gap inside a chosen interval counts towards its length. Use zero for empty memory. At the sizes in the theorem $m_s\ge1$, and even the full native address range is an eligible interval. Use numerical addresses in the RAM's ordinary linear order. Immutable input and the bounded controller are accounted for separately.

**Every exact deterministic SAT decider has arbitrarily large one-bit opposite pairs on which both continuations incur**
$$
 \Omega\!\left(\frac{R_s}{\log\log N_s+\log(2+H_s/N_s)}\right)
$$
**charged instructions, where $H_s$ is measured on that pair's own common prefix.** For a nearly linear cover length $H_s=N_s\log^{O(1)}N_s$ or less this is $\Omega(N_s/\log^2 N_s)$. For any native memory $H_s\le 2^{w_s}$, recovering $\Omega(R_s/\log N_s)$ even on the scattered case. A densely allocated region starting at an arbitrary data-dependent address counts by its length. No description of a different run is substituted for $H_s$.

For the proof, select the lexicographically first minimum disjoint interval cover of the nonzero work cells at every node and database. Endpoints use two native words per interval. The field for the count and unused entries can be padded to $2w_s m_s+O(w_s)\le2\epsilon s+O(w_s)$ bits. Include these fields in each completed path type, in addition to the earlier physical headers and controllers. Since $\sum_{s\text{ on a path}}s<2k$, there are at most $2^{4\epsilon k+o(k)}$ types. Supply the cover to the local symbolic simulation as extra query-independent metadata. Charges may even use this larger public transcript if they are recomputed under that stronger convention. For claims using the original convention, keep its standalone charges and grant the cover only to the simulating decision tree.

For a fixed type and visited internal node $j$, allocate a separate block of $U_j=O(N_s+w_s H_s+w_s)$ old bit features. It contains the entire physical input at the cut with public placeholders in pending positions, the bounded controller, and just the work addresses in the specified intervals. Their default elsewhere is zero. The cover is fixed for this type across every query column. Its actual consistency with a particular database is imposed by the type's row-only mask. Feature functions can be extended arbitrarily to rows inconsistent with that type.

Set $L_s=\log\log N_s+\log(2+H_s/N_s)$ and use the local cutoff $\lfloor\eta s/(w_s L_s)\rfloor$ on each of the two suffixes, with $\eta>0$ fixed and small. For fixed type and query, a simulated charged step resolves at most $O(w_s)$ old bits by affine tests on the current node's features. Every local test uses **only that node's block**. Prior replies can choose coefficients or which child to visit, but the child is simulated from its own actual cut, with its own cache. The total number of tests of block $j$ along any one path is at most $a_j=C\eta s/L_s+O(w_s)$, counting both tags and their final output. Direct leaf lookup can be treated separately with $O(\sqrt k)$ bit tests among $O(M)$ raw features.

Expand the indicators of the accepting paths into products of affine forms or their complements. Reducing squares, the degree **in block $j$** is at most $a_j$ on every path. Thus for this type the query columns lie in the span of products of squarefree monomials, one per block, of total dimension at most $\prod_j D(U_j,\lfloor a_j\rfloor)$, with $D$ defined below. The features need not vary independently on actual inputs. Lean verifies the product expansion and rank sum for type-dependent blocks and masks. [Blockwise rank proof](AffineCutRank.lean) Different types may use different bases. The rank of their masked sum is at most the sum of these individual bounds. A prescribed type on an incorrect path contributes zero by checking the next-node and stopping guards.

Uniformly for $s\ge\Theta(\sqrt{k})$, $L_s=O(\log N_s)$, so the additive $O(w_s)$ fits in $C\eta s/L_s$ for large $k$. Pad $U_j$ to at least $s$ if necessary. Bound the squarefree count at depth $a_j^*=\lceil2C\eta s/L_s\rceil$. Since $N_s=\Theta(sB)$ and both $w_s$ and $L_s$ are $O(\log N_s)$, we have
$$
 \log(eU_j/a_j^*)\le C' L_s+O(\log(1/\eta)).
$$
The rank of each type therefore has logarithm at most $O(\eta k)+o(k)$ for any fixed sufficiently small $\eta$ as $k$ tends to infinity. The leaf contributes $O(\sqrt{k}\log M)=o(k)$. Choose $\epsilon$ and $\eta$ so the sum over all types has rank at most $2^{k/2}$. Here the test budget at each visited node has been chosen using that node's own cover. If a master database had no opposite pair over its local cutoffs, the one-child procedure would compute equality on it for every query. The identity restricted to such rows now finishes the proof exactly as before, including the multiplicity conclusion below.

The linear-clock scanner uses a common $O(N_s)$-word dense arena on all of its promised prefixes and reaches the compact rate. On the other side of the formula, the addresses available to a native RAM grow polynomially with $N_s$. Long cover length can coexist with few writes. The theorem puts the two costs on one actual pair without establishing a superlinear total clock.

## Either the common prefix makes many variable writes, or both continuations pay

The proof just given actually works for any fixed public decoder of address sets. At size $s$ allow codes of length at most $\epsilon s$ bits; include the whole native range as a fallback. In the same-pair inequality substitute the smallest cardinality of a decoded set containing the cut's nonzero work cells for the interval-cover length $H_s$. A type fixes its codes, so precisely the same feature-block and header estimates apply. The decoder may depend on the program and public parameters, and the charge convention need not give it to the solver. A finite union of specific decoder formats costs only a fixed number of extra type bits per node.

Here is a consequence that uses **the addresses of writes actually executed in the common prefix**. At a local size form the trie of sequences of first writes to distinct native work addresses among the binary database prefixes, appending an end symbol to each sequence. The order is chronological. A node with only one possible next symbol needs no description. At a node with alternatives, encode the next address or end symbol in $w_s+1$ bits. All forced moves can be reconstructed from previously supplied choices. The trie is fixed before the query and is finite by totality; no efficient method of traversing it is needed. Every ambiguous nonterminal choice on a path corresponds to an actual first write on that prefix. Its address, or whether any further fresh address is written at all, could differ on a database agreeing on the sequence of all earlier first-write addresses. At most one additional choice encodes the end symbol.

Suppose the number of distinct writes per relevant prefix is $O(N_s\log^K N_s)$ for fixed $K$, as holds in particular for a putative linear-time solver. Choose the decoder above to include the trie. On one and the same opposite one-bit pair, at least one of the following holds.

* Its common prefix executes $\Omega(R_s)$ first writes for which the next discovery was ambiguous given the preceding sequence of first-write addresses.
* Both continuations execute $\Omega(N_s/\log^2 N_s)$ affine-charged steps.

Indeed, if there are fewer than a sufficiently small constant times $s/w_s$ ambiguous first writes, the whole list has a code of at most $\epsilon s$ bits. Its decoded set contains every nonzero work cell and has nearly linear size. The compact case of the same-pair bound applies. This argument counts a real write even when the alternative at that trie node is the end symbol; the possible end on the actual path is excluded from the reported write count. A trie branch can be implemented by writing at an address obtained directly from a single input word. Thus a long sequence of these choices is compatible with a linear-time solver. The statement quantifies the alternative to charging both continuations when the workspace may occupy arbitrary native addresses.

## Compressing the feature vector without charging for indirect reads

Use the $k$-row master database, $M=kB$, and the dyadic one-child recursion down to $s=\Theta(\sqrt{k})$ from the main proof. Each local file has $N_s=\Theta(sB)$ bits, logarithmic-width words, and $R_s=\Theta(s/\log N_s)$ unread packets at its cut. Use the binary balanced-row subfamily inducing the equality matrix. It is enough to impose the bank hypothesis on the prefix states of this subfamily. The machine remains a correct solver on ordinary SAT.

At each node list the chosen bank in a predetermined order. Give each listed slot a position in a common feature vector of fixed maximum length for this node. The slot contents, and even which native address a slot denotes, may depend on the database. The features are arbitrary functions of the database alone. For a fixed choice of bank the simulator knows the entire map from native address to slot. Native work addresses outside the bank start with known zero at the cut. The simulator still tracks all later writes and resolves old-dependent addresses when they are actually used. The input packets and controller are stored as in the unrestricted proof. This charges no probe for looking up the map.

Fix a common budget factor $1\le A\le M^{C_0}$ for one master size, and bound each bank by $O(N_s A)$ words. A level has $O(M A)$ slots and there are $O(\log M)$ levels. Including the physical input and the controller, a single vector of
$$
 U=O(M A\log^2 M)
$$
bit features suffices. Padding this bound to at least $k$ only increases the ensuing rank upper bound. A completed descent type specifies its path, cut controllers, physical placement headers, and chosen bank indices. The ordinary headers contribute $o(k)$ bits along a path. The bank indices add $o(k)$ because the local sizes form a decreasing geometric sequence with smallest size tending to infinity. The number $J$ of types is therefore $2^{o(k)}$. Overlapping types are allowed. Row-only indicator functions impose header consistency, and only the actually followed terminating path contributes on a valid database.

## A squarefree rank count

For bit features, a monomial loses nothing by using each feature once. A tree of $a$ adaptive affine tests thus lies in the common span of at most
$$
 D(U,a)=\sum_{i=0}^{\min(a,U)}\binom Ui
$$
squarefree monomials. Multiplying by the $J$ row indicators gives rank at most $J D(U,a)$. The actual features and the indicators may both be nonlinear functions of the database. For $1\le a\le U$, $D(U,a)\le(eU/a)^a$: multiply the binomial expansion of $(1+a/U)^U$ by $(U/a)^a$ and keep the first $a+1$ terms. [Parity decision trees](https://arxiv.org/abs/1810.08668) · [Lean rank formalization](AffineCutRank.lean)

Let $L=\log\log M+\log(2+A)$. At an $s$-row node truncate each of the two actual continuations at $\lfloor\eta s/(L\log(sB))\rfloor$ charged word steps. Resolving a charged step uses $O(\log(sB))$ affine bit tests. The path sum, terminal tests and direct leaf lookup bound the resulting depth by
$$
 a\le C\eta k/L+O(\sqrt{k}+\log^2 M).
$$
For fixed small $\eta$, round this bound up to $a_*=\lceil 2C\eta k/L\rceil$ for large $k$. It is legitimate to use $a_*$ in the rank estimate even if the actual tree is much shallower. Since $B=O(\log M)$ and $L=O(\log M)$, we have $\log(eU/a_*)\le C' L+O(\log(1/\eta))$. Thus $\log_2(JD(U,a_*))\le k/2$ for sufficiently small $\eta$ and sufficiently large $k$. Logs in asymptotic expressions may be taken to base two.

As in the unrestricted proof, every database with no expensive opposite pair anywhere in its dyadic tree computes equality for every binary query under the truncated procedure. The identity submatrix on such databases has rank equal to their number. At most $2^{k/2}$ of the $2^k$ databases have this property. Consequently there is an opposite one-bit pair on which **both** runs incur $\Omega(R_s/L)$ charged instructions at the chosen node. If $A$ is a fixed power of $\log M$, this is $\Omega(R_s/\log\log N_s)=\Omega(N_s/\log^2 N_s)$. The lengths $N_s$ grow because $s\ge\Theta(\sqrt{k})$. The same counting argument as in the main note gives at least $c2^s/s$ distinct pair-bearing local payloads at a single node for some fixed $c>0$.

At any fixed master size the cutoff and lower bound use the **same** $A$ across its nodes. The packed algorithm in the main note uses $O(N_s A)$ ordinary steps and at most that many words in fixed address ranges, with $O(1+R_s/\min\{\log N_s,\log\log N_s+\log(2+A)\})$ charged steps. Since all local logarithms are within constant factors of $\log M$, this matches the lower rate for the stated polynomial range of $A$. The linear-time construction uses $A=1$ uniformly, without knowing the master size in advance. At a general budget, the upper bound assumes its parameter can be supplied or computed within the stated time.

## Why counting writes gives a different answer

Take the binary subfamily and partition the $s$ rows into $G=s/r$ groups of $r$ consecutive rows aligned within their segments. Every binary selector within a group can occur on a walk, and every binary database subpayload occurs. Suppose a prefix represents the all-good flag for **each** group and each selector as an affine function of $U_0$ common feature bits. The features can depend on all groups jointly. Then
$$
 U_0\ge G(2^r-1).
$$
Compare the all-zero payload with each payload obtained by changing just one group to one specified nonzero $r$-bit string. In coordinates indexed by (group, nonzero selector), all flags vanish on the default payload and those single changes give the identity matrix. Subtracting the default feature vector removes decoder biases. The identity factors through $U_0$ coordinates, giving the inequality. In particular $U_0=O(N_s\log N_s)$ implies $r\le 2\log_2\log N_s+O(1)$: first $r=O(\log\log N_s)$ from $2^r=O(r B\log N_s)$, then use $B=\Theta(\log N_s/\log\log N_s)$. This argument uses only the default and the single-group perturbations. [Lean direct-sum bound](DenseGroupFlagRank.lean)

There is also a consequence for **issued writes** in this group-flag method. Use the actual raw input and cut-state bits with a fixed input layout and no extra payload-dependent advice. The $G(2^r-1)$ difference rows of the old states are linearly independent. A nonsingular square minor has a nonzero determinant term, assigning a different bit position to each perturbation where it differs from the baseline. Discard the matches in the $O(N_s)$ immutable and controller bits and in the $O(wT)$ bits of work addresses written by the baseline in at most $T$ steps. Each surviving matched bit lies at a work address actually written by its perturbed prefix and untouched by the baseline. At most $w$ matches occupy one address. If all prefixes take $T=O(N_s\log^K N_s)$ steps and $r=\Theta(\log N_s)$, one fixed time and instruction write port therefore assumes at least $2^{r-O_K(\log\log N_s)}$ different native addresses on these individual perturbations. The calculation divides the surviving address count by the $O(T)$ possible times and bounded ports. It forces extensive variation of one issued address under the affine group-flag hypothesis, while a single RAM write can realize exactly that kind of variation.

On the equality subfamily, one actual write suffices to place a sentinel at (group, payload value). A query then retrieves its equality flag at the known address (group, query value). A count of the words written in one run allows a much larger common feature space than the compact banks in the theorem. The stronger lower bound here still leaves the unrestricted logarithmic-word RAM time milestones open.

Lean checks the algebraic rank arguments. The bank encoding, sparse-address consequence, asymptotic estimates, and passage to the physical DIMACS pair use the proofs in this note and the accompanying cut construction.
