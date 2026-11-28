# The three largest normalized model densities of proper 3-CNF

Let $E$ be any finite CNF whose clauses have exactly three distinct variables, with arbitrary signs and duplicates. Write $\mu(E)$ for the fraction of assignments satisfying it, $\tau(E)$ for the minimum number of variable names hitting every clause, and $D(E)=\mu(E)/(7/8)^{\tau(E)}$. The three largest possible values of $D(E)$ in descending order are
$$
                         1,\qquad 46/49,\qquad 13/14 .
$$
Every one is attained. In particular $320/343$ falls in a genuine gap. This excludes a proposed five-edit encoding in the common-pin case and, together with a structural algorithm, gives a linear-time result for edited files without knowing their precursor.

## Bounding a connected collection of supports

Put $q=7/8$. The basic bound is $\mu(E)\le q^{\tau(E)}$. More generally, first align all signs in the full formula so zero satisfies each literal. This can only increase the density and leaves every support unchanged. Consider a collection $G$ of distinct supports from that formula. Read selected bits until each edge of $G$ contains an observed zero or an edge has failed. On a successful branch with $z$ zeroes, every support already satisfied has been hit by one of those zeroes. A transversal of the residual edges together with those $z$ variable names hits the whole original formula. The residual rank is at most three, so its model fraction is at most $q^{\tau(E)-z}$. All unqueried bits are still independent fair bits. [Transversal bound, including reduced widths and sign alignment](model-density-and-a-transversal-of-ternary-sat-clauses.md)

It follows that $D(E)\le B(G)$ where $B$ is the least expected $q^{-z}$ on successful leaves, counting a failed leaf as zero. For a list of currently unhit edges use
$$
 B(\varnothing)=1,\qquad B(G)=0\text{ if }\varnothing\in G,\qquad
 B(G)=\min_{v\in\bigcup G}\frac{q^{-1}B(G_0)+B(G_1)}{2}.
$$
Here $G_0$ discards edges containing $v$ and $G_1$ deletes $v$ from each edge. These are distinct rules for the observed zero and one. The proof only needs *one* selected subfamily with a low score to bound the entire formula. It does not require the computed score to equal the actual model density.

A new edge in a connected ordering shares one, two, or three names with the preceding edges. Choose those names amongst the old ones, and give any new names consecutive unused labels. Start with one edge. At every stage ignore a prefix whose score is at most $13/14$ because that prefix already bounds every formula containing it. Independent integer and rational recursions give the following census, with isomorphic unlabelled support systems counted once in the table.

| Distinct supports | Connected extensions of surviving prefixes | Score above $13/14$ |
| --- | ---: | ---: |
| 2 | 2 | 2 |
| 3 | 9 | 2 |
| 4 | 26 | 0 |

The two surviving three-edge types are $abc,ade,bcf$ and $abc,ade,bcd$. Both have transversal number two. The two-edge types have transversal number one and at most five variables. Any connected component with four or more edges contains a connected four-edge subfamily, by taking an initial segment in a traversal of its edge intersection graph. The [Python census](../audits/three_largest_normalized_ternary_densities.py) identifies types by their incidence columns up to edge permutation. The [Lean census](../lean/TernaryDensityGapAtFiveEdits.lean) checks the score directly on labelled extensions.

Distinct components use disjoint variables, so normalized densities multiply. Each component with at least two intersecting supports has $D\le46/49$, and $(46/49)^2<13/14$. An isolated support with several distinct sign patterns has normalized density at most $6/7$. Hence above $13/14$ there can be at most one component with more than one support, and every other component contributes exactly one. For the exceptional component with $n$ variables and transversal number $t$, its normalized density is an integer multiple of $2^{-n}(8/7)^t$, irrespective of the number of signs on each support. For $t=1$, $n\le5$ makes this a multiple of $1/28$, with no value in $(13/14,46/49]$. For $t=2$, $n\le6$ makes it a multiple of $1/49$, with just $46/49$ in that interval. This proves the classification. A single signed triple attains one. The three all-positive clauses $abu,abz,uzt$ attain $46/49$. Two all-positive clauses $abu,abz$ alone have density $13/16$ and transversal one, attaining $13/14$. [Intersecting-pair inequality and its sharp example](a-sharp-density-loss-for-intersecting-ternary-clauses.md)

## The highest accumulation point

For every fixed $\eta>0$ only finitely many normalized densities exceed $6/7+\eta$. In any formula above this level, the intersecting-pair bound implies that a maximal family of vertex-disjoint intersecting pairs has bounded size, since each pair contributes a factor at most $46/49$. Call their union of variables $U$. All supports disjoint from $U$ form a matching.

Every name belongs to a bounded number of distinct supports. To see this, consider $L$ triples with exactly the same core of $c$ names and with nonempty pairwise disjoint petals, where $c=1$ or $2$. Expose the core up to its first zero. If no zero occurs, expose each petal up to its first zero. The normalized multiplier is
$$
 \frac{1-2^{-c}}{q}
      +2^{-c}\left(\frac{1-2^{-(3-c)}}q\right)^L.
$$
As $L$ grows these bounds tend to $4/7$ and $6/7$, respectively. Choose $L$ so both are at most $6/7+\eta$. For a fixed name $x$, the other two names in each triple through $x$ form a graph. A matching of size $L$ gives the forbidden one-name core. A vertex of degree $L$ gives the forbidden two-name core. The endpoints of a maximal matching therefore cover this graph with fewer than $2L$ vertices of degree below $L$. This bounds the number of distinct triples through $x$.

Only boundedly many supports now meet $U$. Any support outside $U$ in a nontrivial component touches one of those boundedly many supports, since the outside supports form a matching. This bounds the size of the union of all nontrivial components. An isolated triple with two or more sign patterns would already cost a factor at most $6/7$. The remaining single-sign isolated triples contribute exactly one and can be discarded without changing $D$. Up to permutations of names we are left with finitely many signed formulas. Conversely, the $L$ clauses $a\lor b\lor x_j$, with distinct $x_j$, have transversal one and normalized density $(3/4+2^{-L}/4)/q$. These distinct values decrease to $6/7$. Thus $6/7$ is the largest accumulation point of the normalized spectrum.

## The missing five-edit case

As in the [joint-edit construction](joint-edits-at-the-sharp-model-density-threshold.md), let $F$ result from changing one variable name in each of $r$ distinct clauses of $E$, with both files proper, and put $K=(4/7)^4$. Every edit loses easy models only on one specified four-variable assignment. The maximum lost mass of an individual edit is $M=Kq^{\tau(E)}$.

**Theorem.** For every fixed $r\ge5$ and $0\le\delta<3/49$, there is a globally correct deterministic log-word RAM SAT solver that takes $O_{r,\delta}(N)$ time on every such $F$ with $D(E)\ge(r-\delta)K$. Its sole input is $F$. This includes both verdicts. The one- through four-edit constructions encode arbitrary proper 3-SAT at $D(E)=rK$ by linear-time, linear-length reductions. At a fixed number of edits from five onward, the same threshold regime admits a global solver with the stated linear running time.

The [no-common-pin theorem](a-gap-below-the-joint-edit-threshold.md) handles all $r$ when the four-variable assignments share no signed pin, and all $r\ge6$ even when they do. For the remaining case take $r=5$ and one signed pin shared by every edit. Write $t=\tau(E)$ and $S=\Pr[E\text{ and the shared pin holds}]/q^t$.

For **any** one pin in any proper $E$, either $S\le26/49$ or $S\ge(4/7)(46/49)$. To see this, let $H$ be the old clauses avoiding the pin variable. Then $\tau(H)\ge t-1$. If $\tau(H)\ge t$ the conditional model fraction is at most $q^t$, so $S\le1/2$. Otherwise $\tau(H)=t-1$. If a clause loses its pin literal because that literal is false, the restriction also includes a binary clause. Align the whole restriction and use this single binary as the exposure family. Reading its two bits until the first zero gives expected multiplier $(3/4)/q=6/7$, with the restriction's transversal at least $\tau(H)$. Thus $S\le(4/7)(6/7)$. In the remaining case all clauses involving the pin have been satisfied and $S=(4/7)D(H)$. The three-value classification yields the stated alternatives. In particular
$$
       26/49=5K-6/2401,\qquad (4/7)(46/49)=5K+8/2401.
$$

If one edit loses less than $M$, it loses at most $(46/49)M$, by the [one-cylinder saturation lemma](a-gap-below-the-joint-edit-threshold.md). The easy models surviving all edits then have mass at least $(3/49-\delta)M$. Suppose instead that all five individual losses attain $M$. If two of their sets intersect in easy models, this intersection has mass at least $3M/49$. Indeed within one saturated loss set the unpinned coordinates are a product of seven-element ternary blocks and free bits. The shared pin means the other set fixes at most three further coordinates. The least positive conditional probability over the possible partitions of three coordinates is at least $3/49$, from two coordinates in one block and one in a second. Again the surviving easy mass is at least $(3/49-\delta)M$.

If the five loss sets are disjoint, their union has mass $5M$, all inside the shared pin, hence $S\ge5K$. The slice gap forces $S\ge5K+8/2401$. The models of $E$ inside this slice that survive all edits consequently have mass at least $(8/2401)q^t$. In each case $\tau(F)\ge t-5$ gives a fixed positive lower bound on $D(F)$. The [global positive-density solver](two-models-from-positive-normalized-density.md) decides $F$ in linear time there. Running it with the bounded search for the no-common-pin cases gives one solver on the edited input alone. Nothing about recognizing the promise or measuring model density is required.

This classifies the four-to-five change for the normalized-density promise. An unrestricted SAT solver need not reconstruct an easy precursor or its models. The ordinary worst-case superlinear RAM lower bound remains open. Tantau established spectral gaps for the unnormalized satisfaction probabilities of bounded-width CNF. Bonato, Brown, Mitsche and Prałat studied independence densities of hypergraphs. The normalization by the variable transversal changes the value even along a sequence of disjoint identical clauses. Historical priority for this exact normalized spectrum has not been established. [Tantau](https://arxiv.org/abs/2201.08895) · [Bonato et al.](https://arxiv.org/abs/1308.2837)
