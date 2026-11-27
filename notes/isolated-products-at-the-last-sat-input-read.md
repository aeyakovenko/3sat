# Isolated binary products give almost as many last-read pairs as exact products

Let $d\ge1$ and $D=d^2$. In the cube of $3D$ binary matrix entries put $\mathcal G_d=\{(A,B,C):AB=C\}$, with multiplication over $\mathbb F_2$. Exactly
$$
                  g_d=\big((2^d-d-1)_d\big)^2
$$
of its points have Hamming distance at least three from every other graph point. The falling factorial counts injections, giving zero when the alphabet has fewer than $d$ elements. In particular $g_d=(1-O(d^2/2^d))2^{2D}$.

For **each correct deterministic SAT RAM** there are at least $g_d$ disjoint opposite-verdict pairs of proper, dense DIMACS files at encoded length $N=\Theta(D)$, with the following properties.

* In the bit-once projection the two files differ in exactly **one physical bit**. Their runs coincide through the address of the load that first completes exposure of all $3D$ source bits. Both runs expose them all. The UNSAT input is an exact product; the SAT input has residual of binary rank one.
* In the first-error projection the SAT file in each pair has **exactly one satisfying assignment**. The files differ by a single underlying matrix bit, which can change up to three physical bits. Every underlying bit is exposed on both runs, meaning the solver reads at least one originally differing copy of each such bit. The solver and its last read may give different partners under the two projections.

The upper bound $|\mathcal G_d|=2^{2D}$ on the number of such disjoint pairs is immediate from the distinct necessary UNSAT endpoints. The counting result therefore attains a $1-o(1)$ fraction of this upper bound. It concerns the fraction of exact products with partners, not a large fraction of all $2^{3D}$ triples. Each step still can read a logarithmic number of original bits. [Bit-once physical projection](compact-bit-projection-of-matrix-mismatch.md) · [Rank-sensitive unique-witness projection](compact-first-error-matrix-projection.md) · [Earlier last-load pairing](one-bit-sat-pairs-at-the-last-input-load.md)

## The exact isolation test

The necessary and sufficient conditions are that the columns of $A$ are pairwise distinct and each has weight at least two, and the rows of $B$ satisfy the same conditions. If a $B$ row is zero or a unit vector, changing one entry in the corresponding column of $A$ changes at most one entry of $AB$. If two $B$ rows agree, flipping two entries in their columns of the same $A$ row leaves $AB$ fixed. Each violation therefore gives another graph point at distance at most two. Transpose for the $A$ columns.

Conversely, a single changed factor bit affects at least two product entries. Two edits in $A$ alone cannot leave $AB$ unchanged. In one row this would require two equal $B$ rows, and in separate rows it requires zero $B$ rows. The transposed argument handles two edits in $B$. With one edit $A_{ik}$ and one $B_{\ell j}$, the change in row $i$, outside column $j$, is exactly row $k$ of $B$ outside $j$. This contains a one. These cases exhaust every pair of graph points at distance at most two, since changing only $C$ cannot stay on the graph.

Each ordered row or column family has $(2^d-d-1)_d$ possible choices from the nonzero, nonunit words. The two families are independent and $C$ is determined. Equivalently, random uniform independent factors fail the test with probability at most $(3d^2+d)/2^d$ by the union bound over light words and equal pairs.

## Actual paired executions

On an isolated exact triple, flipping any one underlying bit changes the correct verdict. A correct deterministic program must read some original copy of each bit, since otherwise the changed file gives exactly the same execution. With writable input, a load after the relevant word was unconditionally overwritten conveys no copy of its initial content. The same indistinguishability argument applies. The argument allows unrelated workspace accesses and arbitrary running time.

Choose any source bit first exposed in the final load that reveals previously unexposed source bits. Flip it at all prescribed positions. Up to that load's address the two executions are identical. That load still completes the exposure on the changed file. A factor flip changes one row or column of $AB$ by a nonzero vector, and a $C$ flip changes one entry, so the partner always has a nonzero rank-one residual. No two chosen exact centers can have the same erroneous partner, since that would place two graph points at distance at most two. This proves the claims for either encoding. The pair gives a lower bound of order $N/\log N$ word loads on each endpoint. It gives no unrestricted superlinear clock.

## A one-dimension successor with the smallest possible change to old entries

There is a sharp obstruction to adjoining one row and column while leaving all three old top-left blocks unchanged. For any extension $A',B'$ write $u$ for the first $d$ entries of the new $A'$ column and $v^\mathsf T$ for the first $d$ entries of the new $B'$ row. The old block of $A'B'$ is $AB+uv^\mathsf T$. If an exact triple extends to an exact triple with the old $C$ literally preserved, then $uv^\mathsf T=0$. Hence $u=0$ or $v=0$. The corresponding new full column or row has weight at most one, so the extension fails the isolation test.

Complementing one fixed old bit suffices. For a standard unit column $e$ of length $d$ set
$$
 A'=\begin{pmatrix}A&e\\0^\mathsf T&1\end{pmatrix},\qquad
 B'=\begin{pmatrix}B&0\\e^\mathsf T&1\end{pmatrix},\qquad
 C'=\begin{pmatrix}C+ee^\mathsf T&e\\e^\mathsf T&1\end{pmatrix}.
$$
For every triple the new residual is $\operatorname{diag}(AB-C,0)$. Old columns of $A$ and rows of $B$ gain zero as their final coordinate. Each new column or row has weight two and is distinguished from all its predecessors by its last coordinate. Every isolated center remains isolated. This transformation preserves Hamming distance between all input triples. Thus the optimal number of old coordinates one has to change to lift an isolated center by one dimension is exactly one under the stated top-left embedding.

If preserving every old entry is mandatory, two new dimensions suffice for all $d$. Let $J$ denote the $d\times2$ all-ones matrix. Take
$$
 A'=\begin{pmatrix}A&J\\0&I_2\end{pmatrix},\quad
 B'=\begin{pmatrix}B&0\\J^\mathsf T&I_2\end{pmatrix},\quad
 C'=\begin{pmatrix}C&J\\J^\mathsf T&I_2\end{pmatrix}.
$$
Now $JJ^\mathsf T=0$ over the binary field, so the residual is again the old one bordered by zero. The two new columns and rows are separated by their two-bit tails. These are successors for the algebraic isolation and exposure of every exact center. A particular SAT partner chosen by a solver's last read need not remain its last-read partner after the lift.

The finite audit exhausts the distance-two test on every exact triple through side three, separately from the row and column characterization. It checks injective rank-one partners under two deterministic, value-dependent schedules of original bit or packet reads, and verifies both successor maps on all triples through side two and on all matched pairs in the side-three experiment. [Reproducible audit](../audits/isolated_product_read_audit.py)
