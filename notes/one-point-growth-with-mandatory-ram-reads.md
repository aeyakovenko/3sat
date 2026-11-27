# One-point growth with a growing lower bound on executed SAT instructions

**Theorem.** There is an explicit sequence of simple permutations, one at every order size $M\ge20$, in which deleting one specified point recovers the previous order. Every graph formed by the two paths is uncolorable with three colors. Every uncolorable subgraph needs $\Omega(M)$ edges. Every correct deterministic logarithmic-word RAM program takes $\Omega(M)$ instructions on each sufficiently large member, both on the represented permutation problem and on its ordinary proper 3-SAT file. In either format the physical input has $N=\Theta(M\log M)$ bits. One globally correct program per format attains $O(M)$ instructions on the whole family, including the disjoint swaps described below.

The induction parameter is the number of permutation entries. Across the family the time bound grows as $\Theta(N/\log N)$. The quantifier ranges over programs of arbitrary size and unrestricted workspace. It gives the same negative file against all of them at each designated size. A smaller chain can preserve uncolorability starting at seven while retaining a contradiction of fixed size. The present construction makes a fixed-size contradictory subformula impossible. [Earlier ladders and physical certificate](one-point-growth-of-two-path-coloring.md) · [SAT reductions and file format](sat-on-a-single-simple-permutation.md)

## Three gaps in a fixed permutation

Use zero-based anchor ranks. The red order is the identity and the blue order is

```
16 8 5 3 13 4 2 10 17 15 0 9 11 6 12 7 14 1
```

Delete the red edge $(R_0,R_1)=(13,14)$ and the blue edges $(A,B)=(8,5)$ and $(C,D)=(15,0)$. The remaining graph admits exactly 48 proper three-colorings. The boundary always has the pattern
$$
             (R_0,R_1,A,B,C,D)=(1,0,2,1,2,1)
$$
up to a global permutation of the colors, and each of its six renamings occurs eight times. This small finite claim can be checked by choosing any uncolored vertex, trying each color absent from its assigned neighbors, and recording the six boundary entries on completed colorings. The original anchor is simple by direct enumeration of all consecutive slices. The anchor also has a short proof by repeated use of diamonds: two common neighbors of the ends of an edge must have the same color. Vertices 2, 5 and 13 see the edge $(3,4)$ and have common color $U$. Vertices 7 and 11 see the edge $(6,12)$, as does color $U$ through its representatives 5 and 13. Hence 7 and 11 also have color $U$. Both 8 and 10 see the adjacent colors of 9 and $U$, so they have one color $V$. Both $V$ and 15 see the edge $(16,17)$, hence 15 also has color $V$. Vertex 1 and color $V$ see the adjacent colors of $U$ and 14, so 1 has color $V$. Finally 0 and $U$ see the adjacent colors of $V$ and 9, hence 0 has color $U$. The edges $(7,14),(14,15),(7,8)$ distinguish $U,V$ and the color of 14. The witness in red order is `1 2 1 2 0 1 2 1 2 0 2 1 0 1 0 2 1 0`. The number 18 is a construction size. The minimum for such an anchor has not been determined. [Complete anchor enumeration](../audits/one_point_strip_audit.py) · [Lean anchor, simplicity test and all-length coloring obstruction](../lean/OnePointStrip18.lean)

For $m\ge2$, insert $x_1,\ldots,x_m$ in the red gap in that order. In the blue gap $(A,B)$ insert the odd-indexed vertices in increasing order. Insert the even-indexed vertices, also in increasing order, in $(C,D)$. There are $M=18+m$ vertices. Erasing $x_{m+1}$ from both orders at the next stage recovers the exact predecessor after standardizing the ranks.

Every resulting permutation is simple, even if either blue list is reordered internally. Intersect a common interval with the old vertices. This intersection is consecutive in both old orders. Two or more old vertices force all the old vertices by anchor simplicity, including the red endpoints on both sides of the entire new strip. An interval containing just new vertices lies in a single blue gap and hence consists of red ranks of a single parity. It can contain at most one. If an interval contains one old vertex and some new ones, the old vertex must border the red gap and must also border a blue gap. All six endpoints are distinct, so this last case is impossible.

## The three-color obstruction

Identify colors with residues modulo three and normalize the anchor by its boundary table. In the strip every pair at distance one is a red edge and every pair at distance two is a blue edge. The left boundary forces $x_1=0$ from neighbors $R_0,A$ and then $x_2=1$ from $x_1,C$. Every three consecutive strip vertices form a triangle. Hence $x_i=i-1\pmod3$ along the whole strip. At the other end $x_m$ is adjacent to $R_1$ and one of $B,D$, so $x_m=2$. The vertex $x_{m-1}$ sees $x_m$ and the other of $B,D$, so $x_{m-1}=0$. The ordered pair $(0,2)$ cannot occur consecutively in the forced forward rotation.

To measure the size of a contradiction, choose any cut $2\le j\le m-2$. Take one actual coloring of the anchor left after deleting its three edges. Give the strip the colors
$$
 h_i=\begin{cases}
 i-1 \pmod3 & i\le j,\\
 2+m-i \pmod3 & i>j.
 \end{cases}
$$
Both boundary pairs are satisfied. Put $U=h_j,V=h_{j+1}$. Precisely one of the three edges crossing the cut fails. The edge $(j,j+1)$ fails for $V-U=0$, the edge $(j-1,j+1)$ for $V-U=-1$, and the edge $(j,j+2)$ for $V-U=1$. All other edges are proper. Consequently the failing edge must occur in every uncolorable subgraph. Since $V-U=j+m+2\pmod3$, each three consecutive cuts give one distance-one edge and, up to the end effects, one distinct distance-two edge. More explicitly, a cut of residue $+1$ shares its distance-two edge only with the immediately following cut of residue $-1$. This gives at least $2m/3-O(1)$ indispensable edges.

The ordinary fixed-width DIMACS renderer uses three color flags per vertex and a common pin $Z$. Each edge has two clauses per color, with opposite signs of $Z$, and each vertex has an at-least-one-color clause. For each indispensable strip edge produced by a cut, permute the coloring to put its unique conflict at any chosen color. Fix $Z$ so that only a chosen one of the two padded clauses fails. Every other clause of the entire file is satisfied. Flipping one negative endpoint literal in this clause makes the file satisfiable. The proper three-distinct-name syntax and byte length are preserved by replacing its minus sign with a space. In particular every one of the six clauses of that edge is indispensable to any unsatisfiable subformula. There are $\Omega(m)$ disjoint input locations at which a fixed negative file can be made positive by changing one byte.

## Repairs that remain simple permutations

There is also a direct lower bound with a promise of valid simple permutations. Choose all even cuts $6\le j\le m-3$ with $j+m+1\equiv0\pmod3$. They are spaced six apart. At one such cut the splice fails only the blue edge $(x_j,x_{j+2})$. In the even blue list swap the consecutive entries $x_{j-2},x_j$. The two outside edges become $(x_{j-4},x_j)$ and $(x_{j-2},x_{j+2})$. Writing $U=h_j$, the colors in even-list order around the failure were $U+2,U+1,U,U,U+1$. After the swap they are $U+2,U,U+1,U,U+1$. Every edge is now proper.

Any nonempty subset of these swaps is feasible. Choose the splice at one selected cut. All other selected substitutions introduce only edges of distance four wholly inside a forward- or backward-rotating part. Such endpoints have different colors. The swaps are internal to the even blue list, so the preceding simplicity proof applies unchanged. Their index pairs are disjoint. This gives an exact OR of $m/6+O(1)$ switches on legitimate simple instances.

Consider the deterministic run on the unchanged negative file. If it never reads any input word meeting the fields of one switch, the run on that positive neighbor has the same history up to the answer. This remains true if the program writes memory, by induction until a differing original input value is read. One instruction reads only a constant number of words. A word has $\Theta(\log N)$ bits and meets only constantly many fixed-width rank fields. Hence at least $\Omega(m)$ instructions execute on this particular input, even with unlimited workspace. For the DIMACS representation the one-byte changes above occur in distinct constant-width edge records of $\Theta(\log m)$ bits. The same word argument applies. The individually swapped simple permutations also have legitimate color-CNF renderings: each changed entry occupies disjoint endpoint-token slots, with possible shared clauses using separate slots.

For the matching algorithm recover $m$ from the order length or the canonical DIMACS header. Generate the two paths and the allowed swaps. Read one designated field per possible swap, reconstruct the entire candidate and compare it with the physical input. If equality holds return whether any swap occurred. On other inputs use a total SAT or coloring decider. Direct indexing takes $O(m)$ word operations. In DIMACS precompute the packed, padded signed decimal names through $3M+1$ in $O(M)$ operations by appending one digit to the spelling of the parent name. Each field spans a bounded number of words. The complete file comparison thus also takes $O(m)$ word steps. [Packed spelling and validation details](sat-on-a-single-simple-permutation.md#the-same-mandatory-reads-on-proper-dimacs-files)

## Verification and scope

The physical audit enumerates the anchor colorings, deletes the designated point on each of the first 79 constructed orders, and checks 2,656 positive witnesses including simultaneous switches on the resulting full permutations. It tests the one-byte repair against every clause of the selected physical cases. The graph construction uses the standard incidence graph of a permutation and the usual notion of simple permutations. Priority for this particular nested coloring and RAM-witness construction is unestablished. [Reproducible audit](../audits/one_point_strip_audit.py) · [Berendsohn, Kozma and Marx](https://doi.org/10.1007/s00453-021-00812-z) · [Brignall, Ruškuc and Vatter](https://arxiv.org/abs/0911.4378)
