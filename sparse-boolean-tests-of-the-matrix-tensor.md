# Sparse Boolean tests of the matrix multiplication tensor

For three binary $d\times d$ matrices define the bit

$$
T(A,B,Z)=\bigoplus_{i,j,h} A_{ij}B_{jh}Z_{ih}.
$$

For $1\le k\le d^2$ there is a bounded-fan-in Boolean circuit of size $O((d^2+k^{3/2})\operatorname{polylog}(d+2))$ that computes $T$ whenever each block has Hamming weight at most $k$. In particular $k=\lfloor d^{4/3}\rfloor$ costs only $d^2\operatorname{polylog}(d+2)$ gates. The circuit can output zero on failed weight tests. For $k<d^2$ this choice genuinely changes the function: take $A$ with more than $k$ ones including $A_{11}=1$ and take $B=Z$ to have its sole one at $(1,1)$.

## A fixed circuit for the sparse calculation

Form a simple tripartite graph on three copies of $[d]$. The edges from the first block go between the first and second parts, those from the second block between the second and third, and those from the last block between the first and third. Its triangle count modulo two is exactly $T$. The $m^{3/2}$ triangle-listing bound and degree-order algorithms are classical. [Chiba and Nishizeki](https://www.cs.cornell.edu/courses/cs6241/2020sp/readings/Chiba-1985-arboricity.pdf) · [Schank and Wagner](https://i11www.iti.kit.edu/extra/publications/sw-fclt-05_wea.pdf)

Compute the degree of each vertex and the three block weights with ordinary Boolean adders on the dense input, in $O(d^2\log(d+2))$ gates. The promised graph has at most $M=3k$ edges. In each of the $3d^2$ public edge slots put a presence flag, the endpoint identifiers and their degrees. Sort the records with active flags first and keep the first $M$ slots, retaining flags for padding. Use the order (degree, vertex identifier) on vertices and orient every active edge forward. A vertex of degree $g>0$ has outdegree at most $\min(g,2M/g)$: every forward neighbor has degree at least $g$, and the sum of degrees is at most $2M$. Thus the maximum outdegree is at most $H=\lceil\sqrt{2M}\rceil$.

Sort the oriented active edges by tail and then head, putting inactive records last. For every slot $p$ and every public offset $1\le j\le H$ allocate one candidate record using the fixed wires from slots $p$ and $p+j$, with an inactive sentinel beyond the end. Keep its flag only when both edges are active and have the same tail. Its key is the unordered pair of heads, in canonical order. Every pair of forward edges from a common tail occurs exactly once: its positions are in the same run of at most $H$ records. A triangle occurs at its unique smallest vertex, so it suffices to XOR the flags of candidates whose head pair is an edge.

For this membership test sort the candidates together with the original active undirected edge records, by their full keys, with edge records before requests at the same key. A fixed sequential scan of the sorted wires resets a presence bit on a new key, sets it at a valid edge record, and answers all matching requests. Inactive records contribute no bit. The construction handles repeated requests for a key with one edge record and distinct candidate flags. All records have $O(\log(d+2))$ bits. A Batcher network on $N$ records uses $O(N\log^2(N+2))$ compare-exchanges after padding, each realized with a linear number of gates in the record width. The largest arrays have $O(d^2+MH)$ records. All copies, positions and scan stages are fixed when $d,k$ are fixed. [Batcher, sorting networks](https://doi.org/10.1145/1468075.1468121)

The known high/low-degree split strengthens the exponent. Suppose binary square matrix multiplication has circuits of size $O(n^\alpha\operatorname{polylog}(n+2))$ for a specified $\alpha\ge2$. Count the triangles touching a vertex of degree at most $t$ at their smallest vertex using the same oriented lists, keeping only those tails and offsets up to $t$. This costs $\widetilde O(Mt+d^2)$. In each part, at most $2M/t$ vertices have degree above $t$. Give those vertices consecutive ranks by a prefix count on the public list of vertex identifiers. Reindex the retained high–high edges using these ranks and fill three zero-padded dense adjacency arrays of side $\lceil2M/t\rceil$ by the same sort-and-lookup operation, with one request per matrix entry. Multiply the first two arrays over $\mathbb F_2$ and take the bitwise inner product with the third. This counts every high-only triangle once. Taking $t=\lceil M^{(\alpha-1)/(\alpha+1)}\rceil$ gives size $\widetilde O(d^2+k^{2\alpha/(\alpha+1)})$, covering $k\le d^{1+1/\alpha}$ in near-quadratic size. Strassen's actually achieved $\alpha=\log_2 7$ suffices unconditionally. An infimum for the matrix multiplication exponent yields the statement for each strictly larger achievable exponent, without promising a polylogarithmic loss at the infimum. [Alon, Yuster and Zwick](https://www.tau.ac.il/~nogaa/PDFS/ayz4.pdf) · [Strassen](https://doi.org/10.1007/BF02165411)

## Two sparse blocks and a dense third block

If $A$ and $B$ have respective weights at most $u,v$, keep their compact lists and enumerate the $uv$ ordered pairs of slots. An active pair $(i,j),(j',h)$ requests $Z_{ih}$ precisely when $j=j'$. Join these requests to the full $d^2$-entry table of $Z$ by sorting with the data first at each key, broadcasting its bit within the run, and XORing the flagged answers. Thus the size is $\widetilde O(d^2+uv)$ with no promise on $Z$. In particular two blocks of weight at most $d$ suffice. Relabeling the three parts covers every choice of two sparse blocks. If the input does not specify which choice works, use the weight tests and give the three cases a fixed priority.

## What the tested coefficients say

Every Boolean circuit function $F$ has a unique squarefree polynomial over $\mathbb F_2$. The coefficient indexed by entry sets $(I,J,H)$ in its three blocks is

$$
\bigoplus_{I'\subseteq I,\ J'\subseteq J,\ H'\subseteq H}
     F(\mathbf1_{I'},\mathbf1_{J'},\mathbf1_{H'}).
$$

This follows because a squarefree monomial contributes an odd number of times to this sum precisely when its support is exactly $(I,J,H)$. The first construction therefore agrees with the true contraction on **every coefficient with each block degree at most $k$**. The two-sparse construction agrees on all coefficients with the specified two block degrees at most $u,v$, regardless of the third degree. Dense Boolean agreement would require control of the remaining coefficients. The sparse tests alone already admit the small circuits above.

At singleton weight there is a sharper bound when only AND gates are charged. In each block obtain a presence bit by XORing all its entries. Extract each bit of the row and column of its selected entry by XORing the entries whose index has that bit set. On a zero block these words are zero, and on a singleton they are the true indices. Compare the three pairs of shared endpoint indices bit by bit using XNOR. The conjunction of these $3\lceil\log_2 d\rceil$ equality bits and the three presence bits is $T$ on every promised input. With free affine Boolean operations, at most $3\lceil\log_2 d\rceil+2$ binary ANDs suffice. This only interpolates Boolean data on the stated tests. It supplies neither a low-rank decomposition of the matrix tensor nor a time bound for a general SAT solver.
