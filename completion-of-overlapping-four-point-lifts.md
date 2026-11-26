# A finite obstruction to gaining one point while growing the uncolorable subgraphs

Consider the uncolorable sequence $G_r$ on the 3142 seed above. It gains four vertices per step and has $r$ indispensable edges. Allow a one-point construction to look arbitrarily far ahead. It can take any subset of vertices from any finite number of later layers on top of the intact $G_r$, in their eventual red and blue orders. Write the subset at a layer as a four-bit mask, from least to most significant in the order $a,b,c,d$. When the first outstanding layer becomes full, increase $r$ and shift the pending masks down one layer.

**Completion theorem.** Consider a single insertion which completes the first outstanding layer, for any $r\ge1$ and any choice of later partial layers. Suppose the orders immediately before and after the insertion are simple and uncolorable. Then at least one of these two instances already contains an uncolorable subgraph using only the selected future points and four vertices of $G_r$. In particular, if the construction keeps at most $L$ future layers open, any infinite one-point chain of simple uncolorable orders in this scheme repeatedly has an uncolorable subgraph of size at most $4L+4$. This holds for adaptive choices of the sites and for every fixed $L$. In unrestricted lookahead the four-old-vertex conclusion still holds, while the number of selected future points may grow. This result concerns the canonical embeddings of these particular lifts.

**The four boundary colors.** Temporarily cut the old blue edge that will receive future central insertions. A suffix sees four boundary colors $(x,u,v,h)$: the red endpoint, the left and right endpoints of the blue cut, and the old first blue vertex. At the top of $G_r$, the corresponding vertices are $(d_r,a_r,d_r,b_r)$. The old red edges $a_rb_r,b_rc_r,c_rd_r$ and old blue edge $c_ra_r$ survive every future mask. If $a_r=d_r$ in color, then $b_r\ne d_r$. If $a_r\ne d_r$, then $c_r$ has the third color and $b_r=d_r$. Thus after renaming colors the only possible boundary states are $B=(0,0,0,1)$ and $C=(0,1,0,0)$ even on these four old vertices alone. The defective coloring of $G_r-f_r$ realizes $B$. The colorings of $G_r-e_i$ for each indispensable $e_i$ realize $C$. A negative phase necessarily rejects $B$. If it rejects $C$ also, the future suffix together with the four old vertices gives the claimed obstruction. Call a suffix eligible when it rejects $B$ and accepts $C$.

**Exact enumeration for an arbitrary suffix.** Modulo renaming the three colors, there are 14 types of four boundary colors. A suffix accepts a subset of these types. The empty suffix accepts exactly $u\ne v$, putting the cut edge back. To prepend one layer, guess colors for the selected points of that layer and check the edges in four paths:

- the red path starting with $x$ and then the selected part of $a,b,c,d$;
- the blue path starting with $u$ and then the selected part of $c,a$;
- the blue path ending at $v$, preceded by $d$ if selected;
- the blue path ending at $h$, preceded by $b$ if selected.

Pass the last vertex of the red path, the last of the left blue path, the first of the right blue path, and the first of the blue head path to the remaining suffix. A state is accepted if some guess is proper on the displayed paths and is accepted by the remaining suffix. This is exact by restriction and gluing. It deals with identities among the four actual boundary vertices by passing their actual colors.

The closure of the empty-suffix relation under all 16 prepending maps has exactly 22 relations. Each is reached in at most three prepends. Using 14-bit masks ordered by the lexicographically sorted restricted-growth encodings of the types, their integer codes are

$$
0,879,2047,7039,8191,11247,12287,14588,15359,15838,15866,
15868,16063,16119,16311,16367,16375,16376,16378,16380,16382,16383.
$$

For each of these 22 suffixes, prepend a full layer and a layer missing just one chosen point. The number for which both resulting relations are eligible is respectively $0,4,0,0$, with missing point $a,b,c,d$. The enumeration is certified by the finite transition calculation in `layer_completion_audit.py`. Closure under each map makes the result apply to every finite suffix length. In the only surviving case $b$ is missing, so the selected $a,c$ are consecutive in both red and blue orders. Later insertions lie after $a$ in the blue central word and have greater red ranks. This gives a forbidden common interval immediately before completion. Thus simple negative phases on both sides of a completion cannot both be eligible. For a bounded window, infinitely many new points require infinitely many completions, proving the consequence.

**A positive test of the model.** A lookahead of five layers admits a one-point cycle of simple negative phases. Write the normalized masks in hexadecimal with the nearest layer in the least significant nibble. The following pairs give the current mask and the zero-based bit to add:

$$
(7171,1),(7173,2),(7177,3),(717,18),(40717,17),(60717,12),(61717,16),(71717,3).
$$

After each insertion, shift right by four bits while the low nibble is full. The cycle returns to its starting mask after eight insertions and advances two complete layers. Each displayed phase actually rejects every possible boundary assignment with $x=v$, so it has a bounded local contradiction. For simplicity, it suffices to check the eight phases above one representative simple base $G_1$. To see why this applies at all bases, project a common interval to the old simple order. If it contains all old vertices, it must contain all new central vertices, and the prospective choices of blue prefix tail and red rank interval depend only on the relative ranks of new vertices. If it contains exactly one old vertex and a new vertex, the old vertex must be the red maximum. The blue segment then lies in the central word ending at that maximum, separated from the new prefix by nonempty old vertices. If it contains no old vertices, it lies in a single run entirely of new vertices. In all three cases, the existence of a nontrivial proper common interval for a nonempty mask depends only on the mask. The explicit cycle illustrates why following negative one-point examples alone does not guarantee a growing certificate.

The canonical growth rule and defective colorings used here are in the [four-point proof](one-point-growth-of-two-path-coloring.md). Lean checks closure of the possible four-vertex relations for suffixes of arbitrary length, and checks the last-site implication derived from them. The separate strip construction achieves literal one-point growth with growing contradictions using a different embedding. [Lean closure proof](LayerCompletion.lean) · [Independent transition calculation](layer_completion_audit.py) · [The one-point strip](one-point-growth-with-mandatory-ram-reads.md)
