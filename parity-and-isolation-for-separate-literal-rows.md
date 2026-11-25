# Exact parity and model multiplicity with one row per literal

Suppose a uniform local replacement for a ternary clause has three positive port bits, each occurring once in a different proper clause. Its other variables are fresh. It must project to OR on all eight settings. Suppose further that its **ordinary, unweighted** number of satisfying extensions, reduced modulo a prime $p$, equals the decision bit of the clause. If $t\ge1$ ports are true, the minimum possible number of extensions is
$$
                      1+p(2^{t-1}-1).
$$
A single replacement attains the minimum at every setting. For $p=2$ there is an **eight-row** proper gadget doing this with every row essential at the all-zero boundary. Eight rows and four fresh variables are both optimal for attaining those exact counts. Without the congruence requirement the simultaneous minimum is $t$. [Separate-row model count and its eleven-row optimum under irredundancy](exact-ambiguity-of-clause-local-3sat-replacements.md)

## The lower bound counts auxiliary witnesses by their failed port rows

For an assignment satisfying all ungated rows, let $S\subseteq\{1,2,3\}$ be exactly the set of port rows it would falsify when all three ports are false. Let $d_S$ count such assignments. If the true ports are $T$, the number of models is exactly
$$
                 f(T)=\sum_{S\subseteq T}d_S.
$$
Since the projection is OR, $d_\varnothing=0$. Möbius inversion of $f(T)=[T\ne\varnothing]\pmod p$ gives $d_S\equiv(-1)^{|S|+1}\pmod p$ for every nonempty $S$. Ordinary counts are nonnegative integers. Hence each odd-sized sector contributes at least one and each nonempty even-sized sector at least $p-1$. Summing these bounds gives the formula, including $1$ when only one port is true.

Attainment for any fixed prime $p$ uses a Boolean selector for a nonempty subset $S$ and a binary counter with one code for odd $|S|$ or $p-1$ codes for even $|S|$. Use three fresh bits $x_i$ with $x_i=0$ for $i\in S$, and an additional bit $s$ fixed false. Use port rows $(a_i,s,x_i)$. All other clauses implement the selector and counter test on the auxiliary bits. A Boolean circuit of gate equivalences has a unique extension on its internal wires. Pad short constraints to proper ternaries with distinct forced-false bits, whose common truth values can be forced by the seven clauses excluding all other assignments of three reserve bits. For $p=2$ no counter choices are needed. The construction for general $p$ asserts exact multiplicities with fresh variables and separate ports. The following sharper realization for $p=2$ also makes every row essential.

## Eight clauses for parity

Write the port rows as $(a,s,x),(b,s,y),(c,s,z)$. Add five ungated rows
$$
 (\neg x,\neg y,\neg z),\quad(\neg s,x,y),\quad(\neg s,x,\neg y),
 \quad(\neg s,\neg x,y),\quad(\neg s,\neg x,z).
$$
With $s=1$ the last four rows force $x=y=z=1$, excluded by the first. With $s=0$ each nonempty subset of the true ports is realized once, by the zero coordinates of $(x,y,z)$. Thus $f(T)=2^{|T|}-1$. On boundary $000$ deleting a port row admits its singleton subset. Deleting the first ungated row admits $s=0,x=y=z=1$. With $s=1$, the forbidden sets of the last four rows on the $xyz$ cube are the edges $00*,01*,10*,1*0$. Each edge has a private endpoint other than $111$. That endpoint repairs the corresponding deletion. [Lean checks of the count and the eight private deletions](LocalClausePorts.lean)

At the simultaneous minimum each of the seven nonempty sectors has size one. For any one port row its auxiliary falsifying face must contain the four witnesses for the subsets containing that port. A proper port row fixes two distinct auxiliary coordinates on its falsifying face. It therefore needs $2^{d-2}\ge4$, or $d\ge4$ fresh variables. On the all-true input precisely seven assignments may survive. With at most seven rows in total there are at most four ungated proper ternaries. They can cover at most half the auxiliary cube, leaving at least $2^{d-1}\ge8$ models. This proves both minima without a search.

The optimum still holds if each auxiliary must occur at least twice in **each** polarity. Replace the row $(\neg s,\neg x,y)$ by $(\neg s,\neg x,\neg z)$. With $s=1$ the four guarded rows are two opposite-$y$ clauses forcing $x$ and two opposite-$z$ clauses forcing $\neg x$. Their four forbidden edges partition the cube, each with a private endpoint different from $111$. The $s=0$ computation is unchanged. The positive/negative counts for $s,x,y,z$ are $(3,4),(3,3),(2,2),(2,2)$. [Lean proof for the balanced eight rows](LocalClausePorts.lean)

The same eight-row syntax with a signed weight realizes exact OR in every field. Give a selected nonempty $S$ weight $(-1)^{|S|+1}$ using a global minus sign and unary factors on the three selector bits. The sum over all nonempty subsets of a nonempty $T$ is one. Over a characteristic-zero field, a plain count in this separate-row model could not achieve the value one on every nonempty $T$, since the distinct single-port witnesses all survive. Signed weights address the local clause evaluation. After summing over a full formula's assignments the unweighted SAT decision still differs from its model count.

On $m$ disjoint triples take, for each triple, the seven clauses forbidding every assignment except $111$. The resulting file has one model. On that model one row has three true literals, three have two and three have one. Under any independent replacement satisfying the local hypotheses modulo $p$, the file therefore has at least
$$
                  \big((1+3p)(1+p)^3\big)^m
$$
actual models. The constructions attain equality. In characteristic two the optimum is $189^m$. Requiring only preservation of SAT with separate literal rows gives $24^m$ on the same input. This concerns local unweighted replacement. General tensor networks can use cancellation, globally shared witnesses and the earlier one-sort promised decision. [Exact clause-wise multiplicity](exact-ambiguity-of-clause-local-3sat-replacements.md) · [Global sharing and signed enable tests](shared-witnesses-for-masked-literal-occurrences.md) · [One-sort decision with at most two models](one-sort-for-bounded-ambiguity-sat.md)
