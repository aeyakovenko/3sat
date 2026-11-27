# Field ranks of one permutation walk

Let each of $L$ layers carry its own permutation $P_i$ of $[m]$. Start at 1, use the tables in order, and return the bit $[P_L\cdots P_1(1)=1]$. Alice holds the odd layers and Bob the even layers. Let $F$ be the communication matrix of this bit, with their complete inputs indexing the rows and columns. For every field $K$ and $L\ge2$,
\[
 \operatorname{rank}_K F =
 \begin{cases}
   1+(m-1)^{L-1}, & m\ne0\text{ in }K,\\
   2+\displaystyle\sum_{j=1}^{L-1}(L-j)(m-2)^j, & m=0\text{ in }K.
 \end{cases}
\]
For $L=1$ the rank is one. For a general layer ownership order, compose each maximal run of layers belonging to the same party. Its product ranges over all permutations, since every other factor can be the identity. The full communication matrix consequently differs from the matrix for the compressed order only by row and column duplications and permutations. Here $L$ in the formula counts **runs**. Independence of the layer tables is essential. The standard pointer-chasing problem reuses one function per party. [Nisan and Wigderson](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/NW91/proc.pdf) · [Fischer, Oshman, Rosen and Roth](https://arxiv.org/abs/2508.19158)

## Proof

Write $e$ for the all-ones vector, $c$ for coordinate summation on $V=K^m$, and $e_i$ for the standard vectors. The span of the permutation matrices consists of exactly the matrices $G$ satisfying $Ge=\lambda e, cG=\lambda c$ for some common scalar. Indeed, subtract $\lambda I$. A matrix with zero row and column sums has the basis
\[
     (e_i-e_m)(e_j-e_m)^\top,\qquad 1\le i,j<m.
\]
Its upper-left block provides the coefficients. Each displayed matrix is the difference of two permutations agreeing outside rows $i,m$, which exchange columns $j,m$ there. This argument works in every characteristic. The real span is also recorded by Li, Tam and Tsing. [Section 2 of their paper](https://cklixx.people.wm.edu/tsing.pdf)

Replace the first table by $v=P_1e_1$, which ranges over a spanning set of $V$, and the last by $u=e_1^\top P_L$, which spans $V^*$. The intermediate slots span the matrix space just identified. The endpoint bit is the multilinear expression $uG_{L-1}\cdots G_2v$. Its coefficient matrix, using one tensor-product basis per party, has the same rank as $F$. Indeed independent inputs span every tensor-product domain, so evaluating on spanning sets preserves the rank of the bilinear pairing. In particular each party's distinct products of one basis coordinate per slot give separate row or column indices, over finite fields as well.

If $m\ne0$ in $K$, then $V=Ke\oplus\ker c$ and every intermediate matrix is a direct sum of a scalar and an arbitrary matrix on the $(m-1)$-dimensional second space. Expand the product as a sum over its $L-1$ intermediate basis indices. One term uses the scalar index everywhere. Each of the $(m-1)^{L-1}$ index strings in the second space contributes a single coefficient one. Every intermediate index is incident to a slot held by each party, and that slot's basis coordinate identifies the index. Thus the terms occupy different rows and different columns. This also works for $m=1$ or for $L=2$, when there are no intermediate matrices.

If $m=0$ in $K$, put $d=m-2$. Choose a basis with first vector $e$, then $d$ vectors completing a basis of $\ker c$, then a vector of coordinate sum one. In this basis the intermediate matrices have the form
\[
             \begin{pmatrix}
                 \lambda & a & b\\
                 0 & M & y\\
                 0 & 0 & \lambda
             \end{pmatrix},
\]
with every indicated parameter independent. Call the first and last basis positions top and bottom.

Consider a nonzero term of the index expansion which uses a middle index. In chronological order its $j\ge1$ middle indices form a single interval. Before this interval all indices are bottom and afterwards all are top. Either party's tuple of slot coordinates determines **every** middle position and its basis index. Each position is incident to exactly one of that party's slots, and coordinates involving a middle index always distinguish their incident indices. Thus the remaining outer positions are also determined. Each such term gives a coefficient one at a distinct row and column, disjoint there from all terms having no middle positions. There are $(L-j)d^j$ terms with interval length $j$.

It remains to find the rank when the index string stays in the two outer positions. The restricted gates are $\lambda I+bE$, where $E$ maps bottom to top and $E^2=0$. For each side $S$ write $p_S=\prod_{i\in S}\lambda_i$ over its **internal** slots and $q_S=\sum_{i\in S} b_i\prod_{h\in S, h\ne i}\lambda_h$. An empty side has $p_S=1, q_S=0$. The product of its restricted gates is $p_S I+q_S E$. All these gates commute.

For even $L$ the starting vector belongs to Alice and the final covector to Bob. The two Alice features are $v_t p_A+v_b q_A, v_b p_A$, and the paired Bob features are $u_t p_B, u_b p_B+u_t q_B$. Each pair is linearly independent by its endpoint coordinates. For odd $L\ge3$ both endpoints belong to Alice. Bob's features $p_B,q_B$ are independent because he has an internal gate. The paired Alice features are $(u_t v_t+u_b v_b)p_A+u_t v_b q_A, u_t v_b p_A$, again independent. In both parities this block has rank two. This proves the formula, including $m=2$ in characteristic two. For $L=2$ and $L=3$ the formulas happen to agree in all characteristics. At $m=4,L=4$ the ranks are 28 in characteristic zero and 24 in characteristic two.

## Which words must a real algorithm read?

The real rank gives a deterministic worst-case communication lower bound of $\log_2(1+(m-1)^{L-1})$ bits under the usual monochromatic-leaf convention. The owners can send the current state at every change of ownership, then communicate the verdict if necessary. A RAM with joint access to the forward tables follows the same walk with exactly $L$ data probes and $O(1)$ working words on promised inputs. Each entry occupies a separately addressable word. This measures how the successive **values** choose the addresses.

The same exact field ranks persist under a much smaller promise: every layer moves at most **three states**. For the basis difference indexed by $i,j<m$, choose the transposition $(i\ j)$ fixing $m$ as the first permutation, with the identity for $i=j$. Exchange its outputs in rows $i,m$ for the second permutation. Both fix every point outside $\{i,j,m\}$. Along with the identity they span the full matrix space in the proof. Transpositions also give every endpoint basis vector. For alternating layers the multilinear rank calculation therefore carries over without any change. For consecutive layers of one owner, restrict all but one of that run's layers to the identity for the lower bound and use the unrestricted formula as an upper bound. This allows each layer to be supplied in $O(\log(m+1))$ bits as a list of up to three moved labels and their local permutation. A RAM can now read the descriptors **strictly sequentially**, testing only equality with its current state to evaluate each layer. It uses $O(L)$ operations on word-sized descriptors. Thus the rank persists even when the physical input addresses of a matching linear-step algorithm are fixed in advance.

There is a stronger per-execution statement in that forward-entry model. Let $m\ge 3$. Any deterministic algorithm correct on all permutation inputs, on any accepting input with fewer than $m-1$ total data probes, must read all $L$ actual path entries. If it misses the path row at a layer, a second unread row exists there. Exchange those two outputs. The transcript is unchanged and the subsequent permutation product sends the changed state to a different endpoint.

For uniform random permutation inputs conditioned on acceptance, let $T<m-1$. With probability at least $1-T/(m-T)$, no path entry is discovered out of order in the first $T$ probes. In particular any algorithm halting within $T$ probes on such an input has discovered its whole accepting path in chronological order on this event.

To see the probability bound, plant the path using $z_0=z_L=1$, draw $z_1,\ldots,z_{L-1}$ independently and uniformly, and independently fill each permutation uniformly subject to $P_i(z_{i-1})=z_i$. All accepted inputs have the same probability. Condition on a partial transcript, on its discovered path prefix through layer $k$, and on having found no later path entry so far. The prefix states are known. For $k<j<L$, any possible $z_j$ avoids the queried images in layer $j$ and the queried input rows in layer $j+1$. The conditional distribution on these remaining choices is uniform and independent across $j$. Indeed for any permitted sequence of hidden states each unfinished table with $h$ distinct queries admits exactly $(m-h-1)!$ completions once its planted pair is fixed. Finished tables also contribute a constant number. Thus an attempt to discover the path edge of layer $i>k+1$ guesses $z_{i-1}$ from at least $m-T$ labels. Summing the conditional probabilities over at most $T$ probes proves the bound. It applies unchanged to adaptive private workspace and arbitrary computation between probes. This part uses the explicit forward table encoding.

A useful deterministic complement concerns a rejecting transcript with fewer than $m$ data probes. Let $i$ be the first unobserved actual forward path entry and $j$ the first unobserved entry when tracing *backwards* from the target in the given tables, indexed by forward layer number. If either search observes the whole walk, its path alone certifies the verdict. Otherwise, necessarily $i>j$. If $i=j$, both the forward-prefix row and backward-suffix image are free and can be paired. If $i<j$, the possible states just after layer $i$ number at least $m-h_i$, where $h_i$ is its number of known rows. Propagating any fixed compatible permutations through the layers before $j$ preserves that size. The possible states just before layer $j$ reaching the target number at least $m-h_j$. They intersect since $h_i+h_j<m$. In either case one can complete the tables to accept with the observed transcript. Thus whenever the last layer's target image was never returned by a probe, a rejecting transcript of this size has read the entire actual forward path.

## Several speculative discoveries on the same run

The preceding probability estimate stops at the first lucky guess. The following version charges **every** speculative start, including on a run much longer than the width. Allow an exact algorithm to issue batches of forward-table queries, each batch chosen from the earlier replies. Take the uniform accepting distribution as above. Write $Q$ for its total number of queries, $M$ for the number of layers whose actual path entry it never reads, and $S$ for the number of layers $i>1$ whose path entry is first read in a batch before the predecessor entry has been returned. Two first reads in the same batch count as a start at $i$. The same definition applies to sequential probes by taking singleton batches. For every such algorithm that halts,
\[
        M\le Q/(m-1),\qquad \mathbb E S\le 6\,\mathbb E Q/m .
\]

The exchange argument gives the first inequality per input, since each missed layer must contain at least $m-1$ queried rows. For the second, enrich the past transcript for analysis with flags saying which earlier queries read the planted path. Conditional on these flags and the replies, each $z_j$ with neither adjacent planted edge discovered is uniform outside the known images of layer $j$ and the known rows of layer $j+1$. The same factorial count as above proves this even after several out-of-order discoveries. Each previously found edge fixes its two incident labels. For every other edge the row and image exclusions are separate unary restrictions on the adjacent labels. The number of completions is a product of constants over the permitted choices.

Write $h_i$ for the number of distinct rows already read in layer $i$. At the beginning of a batch, a query in layer $i>1$ with both its edge and its predecessor undiscovered has probability at most $2/m$ of hitting the true path if $h_i+h_{i-1}<m/2$. Sum over that batch's preselected queries, using their marginal probabilities before any answer in the batch is returned. Sum over batches to bound the expected number of such starts by $2\,\mathbb E Q/m$. The number of remaining starts is at most $4Q/m$ per execution. Each contributes a different index $i$ with final $h_i+h_{i-1}\ge m/2$, and $\sum_{i>1}(h_i+h_{i-1})\le2Q$. This proves the expectation bound, including data-dependent stopping.

In $r\ge1$ adaptive query rounds, consecutive layers whose first-return rounds strictly increase form chains of length at most $r$. The chains start at the first layer or at one of the $S$ starts. A missed layer can count as a separate singleton. Thus $\lceil L/r\rceil\le1+S+M$, giving
\[
     \mathbb E Q\ \ge\
      \frac{m(\lceil L/r\rceil-1)}{6+m/(m-1)}
\]
for $m\ge2$. There is also a direct $\mathbb E Q\ge L$ bound: every layer either contributes its path probe or requires at least $m-1$ other probes. This is a distributional statement on one polarity for algorithms exact on the full permutation promise. Pointer following has long been used for adaptivity lower bounds, including in decision trees. [Canonne and Gur](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2017.27)

For $m\ge2$, in one nonadaptive batch the exact optimum on the raw tables is $1+(L-1)(m-1)$ probes. Query the starting row and all but one row in every subsequent layer. For the converse, a fixed query set missing two rows in any layer $i\ge2$ can be fooled. Pick earlier permutations sending the starting point to the first missed row. Choose the two unseen images so that the remaining permutation product sends exactly the first image to the target. Swapping them preserves every query and changes the verdict. The very first layer also needs at least one probe since its action can change the answer with all other layers fixed.

## Transfer to proper DIMACS

For every layer $i=0,\ldots,L$ use $m$ variables $X_{i,j}$ with consecutive variable numbers. Add units asserting $X_{0,1}$ and forbidding $X_{L,j}$ for every $j\ne1$. Each table entry occurs in one implication
\[
             X_{i-1,j}\ \Longrightarrow\ X_{i,P_i(j)} .
\]
Pad implications with a false variable and units with two distinct false variables. For example, force three new variables to zero with the seven ternary clauses each forbidding one of their nonzero settings. Every clause now has three distinct variables and no opposite pair. Every variable in the header is used. When the actual path ends at 1 the entire satisfying assignment is unique. Its path variables are forced true from the start. Every other variable has a forward path to a forbidden terminal by injectivity and is forced false. If the path misses 1, it reaches a forbidden terminal and the file is unsatisfiable.

Represent each variable token as ordinary decimal with enough leading **spaces** to give all token fields equal length, including any minus sign. The clause positions and encoded length $N=\Theta(Lm\log(Lm+2))$ bits are public. Only the positive head field of an implication depends on its own table entry. A native input word of $O(\log N)$ bits intersects at most $C=O(1)$ such fields, for a fixed word-width constant. A table-query algorithm simulates any physical input probe by reading those entries in a single batch and reconstructing the word locally. The source simulation records a whole entry even if the machine needed just one of its digits. Its ordered discoveries consequently describe intersections with the corresponding physical fields. The other input bits and all work RAM require no table probes in this comparison.

It follows, for instance, that every globally correct SAT algorithm making at most $r$ batches of native input queries takes on average $\Omega(L+m(\lceil L/r\rceil-1))$ such queries on these uniformly generated uniquely satisfiable files. On sequential executions, the bound on $\mathbb E S$ with $Q$ at most $C$ times the true probe count describes how often an input word can first intersect the actual path ahead of its predecessor. No restriction on private work or memory is needed. The original unrestricted timing problem permits any number of adaptive rounds. Following the path uses $L$ table probes on promised inputs, and validating its DIMACS template by scanning the file also takes at most linear encoded time. [Related two-scan construction](all-tree-prefix-scans.md)

The accompanying NumPy audit constructs the physical matrices, performs prime-field elimination, and checks 148 ownership patterns in characteristics 2, 3 and 5. The general proof above is on paper. Priority of the two field formulas has not been established. [Reproducible audit](../audits/permutation_walk_rank_audit.py)
