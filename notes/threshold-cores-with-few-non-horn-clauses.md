# How many original clauses must a 3-SAT certificate retain?

**Research journal, 25 November 2026.** On $v$ variables, let at most $h$ clauses of a width-at-most-three CNF have two or more positive literals. The largest possible minimum size of an unsatisfiable subformula is

$$
                 \Theta\!\left(v\min\{3^h,v^2\}\right).
$$

The same bound holds for one subformula that must preserve SAT at **every clause-weight threshold** and after **every addition of negative clauses**. At roughly $2\log_3 v$ exceptional clauses, cubically many original clauses can already be indispensable for a single rejection. These are clause counts. Here $v$ counts variables, whereas the RAM time question uses the encoded input length.

## The threshold certificate

Give each clause $C$ a weight in a totally ordered set, and write $F_{\le t}$ for the clauses of weight at most $t$. A negative clause has only negative literals. It can have any width, including zero. The added queries $D$ below use the same variables as $F$.

**Upper bound.** Suppose the non-Horn clauses are $C_1,\ldots,C_h$, of widths $a_1,\ldots,a_h$. There is a subset $S$ of the original weighted clauses with

$$
 |S|\le h+(v+1)\prod_{i=1}^{h} a_i
      \le h+(v+1)3^h
$$

such that, for every $t$ and every conjunction $D$ of negative clauses,

$$
                 S_{\le t}\land D\ \text{is satisfiable}
        \quad\Longleftrightarrow\quad
                 F_{\le t}\land D\ \text{is satisfiable}.
$$

First consider a weighted Horn formula $H$. Write each clause as a rule whose head is either a variable or a distinguished symbol $\bot$. Its body consists of the variables occurring negatively in the clause. Sweep weights in increasing order. At each weight activate all its rules and close the set of marked heads under all active rules. An empty body fires without any marks. Keep the rule that first marks each head, recording an actual firing order to break ties within a weight. Continue processing variable heads even after marking $\bot$, which occurs in no rule body.

At every threshold the retained rules mark exactly the same heads. Replay their first firings in recorded order for one inclusion, and use containment in $H$ for the other. At most $v+1$ rules survive. The marked variables give the least set closed under the definite rules. A model of $H_{\le t}\land D$ exists precisely when $\bot$ is unmarked and the body of no clause of $D$ is contained in this least set. Every model must contain all the marked variables, and taking just those variables true supplies a model whenever both tests pass. Given the order of the weights, the sweep can maintain prerequisite counts and process each literal occurrence a constant number of times. The underlying Horn forward-chaining algorithm is classical. [Dowling and Gallier, 1984](https://doi.org/10.1016/0743-1066(84)90014-1)

For the general case, choose one literal from each $C_i$. Form an auxiliary Horn formula from all original Horn clauses and these selected **unit clauses**, each carrying the weight of its originating $C_i$. Make the Horn certificate for each of the $\prod_i a_i$ possible choices. Retain all $C_i$ in $S$, together with every original Horn clause retained on at least one choice. The auxiliary units are used only in the proof.

Take any model of $S_{\le t}\land D$. For each active exceptional clause select one literal it makes true. Complete the choices arbitrarily on inactive clauses. This assignment satisfies the retained Horn certificate on that branch at threshold $t$, including its active retained auxiliary units, as well as $D$. The Horn result gives a model of the full auxiliary Horn formula at $t$ with $D$. Its active units satisfy every active exceptional clause, so it is a model of $F_{\le t}\land D$. Conversely any full model satisfies the retained subset.

Equivalently, $S_{\le t}$ and $F_{\le t}$ have **the same inclusion-minimal models**, viewing a model as the set of variables set true. For a model $A$ of the subset, adjoin the negative units forbidding every variable outside $A$. The equivalence gives a full model contained in $A$. Since full models satisfy the subset, the two families have the same minimal elements. Conversely, an all-negative query is preserved upon taking a smaller set of true variables, so its satisfiability is determined by those minimal elements.

Lean verifies the weighted literal choices, their transfer to the union of retained original clauses, equality of the minimal-model families, and the implication from a private deletion witness to membership in every rejecting core. The file takes each Horn branch's simultaneous threshold-query certificate as an explicit hypothesis. The first-firing construction and quantitative bounds are proved in this note. [Lean verification](../lean/HornChoiceCertificate.lean)

In particular one can take all weights equal and $D$ empty to obtain the unsatisfiable-core bound. There is also an $O(v^3)$ bound in all regimes. Delete tautologies, simplify repeated literals, and keep just the earliest occurrence of each distinct clause. There are at most $\sum_{j=0}^3 2^j\binom vj$ possibilities. This proves the upper half of the displayed asymptotic bound for both tasks.

## Counting positive literals gives a sharper bound

Write an exceptional clause as a Horn body $B_i$ implying a disjunction of $p_i$ positive heads. In a branch choose one head $z$ and replace the clause by the **guarded Horn rule** $B_i\to z$ with the original weight. A model of an active original clause satisfies at least one such rule. If the body is false every choice works; if it is true one head is true. Conversely any chosen rule implies the original clause. The same first-firing and union proof therefore gives the stronger bound $h+(v+1)\prod_i p_i$. This positive-head branching principle has prior art in algorithms for almost-Horn minimal models. The upper bound on *retained original clauses across all thresholds* also uses the first-firing construction. [Ben-Eliyahu and Dechter, §4.1](https://cdn.aaai.org/AAAI/1993/AAAI93-001.pdf)

For limits $h_2,h_3$ on clauses with two and three positive literals respectively, the matching worst-case core count is
$$
                 \Theta\!\left(v\min\{2^{h_2}3^{h_3},v^2\}\right).
$$
To see the lower bound, use the two selector banks below with levels of radix two or three. Take up to $h_2$ copies of radix two and $h_3$ copies of radix three. Fill the first bank and then the second from this list while the number of leaves in each stays at most $Q=\lfloor v/64\rfloor$. If every radix fits, the product of the two leaf counts is $2^{h_2}3^{h_3}$. If some radix remains after both banks, each bank has more than $Q/3$ leaves, since a next radix of at most three failed to fit. A tree whose internal nodes all have at least two children uses fewer than twice as many nodes as leaves, and the total level count is $O(\log v)$. With $\lfloor v/4\rfloor$ output variables the deletion witnesses below give the asserted count. This sharpening uses width at most three, allowing positive binary clauses for the radix-two levels.

## An unsatisfiable formula attaining the parameter dependence

Use $d\le h$ ternary choices. Split them between two banks of depths $a=\lfloor d/2\rfloor$ and $b=\lceil d/2\rceil$. A bank of depth $a$ has three fresh selector variables at each level $j$ and the one exceptional clause

$$
                 s_{j,0}\lor s_{j,1}\lor s_{j,2}.
$$

Use a Boolean variable $p_u$ for every prefix $u$ of a ternary string of length $a$. Include the root fact $p_{\varnothing}$ and the Horn rules

$$
           p_u\land s_{|u|+1,e}\ \longrightarrow\ p_{ue}
                 \qquad(|u|<a,\ e\in\{0,1,2\}).
$$

Every satisfying assignment makes at least one leaf true. Any prescribed leaf can be the unique true leaf by selecting exactly its digits and setting just its prefixes true. This includes depth zero, whose only leaf is the root. Call the two banks' leaves $X_i$ and $Y_j$, and give them disjoint variables.

Take $L\ge1$ fresh variables $Z_1,\ldots,Z_L$. Include every clause

$$
            X_i\land Y_j\ \longrightarrow\ Z_k.
$$

There are $M=3^{a+b}L$ such clauses. Make the $Z_k$ the leaves of a full binary tree with fresh internal variables. For each internal vertex include the Horn rule from its two children to that vertex. Add the negative unit forbidding the root. When $L=1$ the root is $Z_1$ itself. At least one pair of bank leaves is true, so the indexed clauses force all $Z_k$, and the tree forces its forbidden root.

**Deletion witness.** Omit any particular indexed clause $(i,j,k)$. In each bank use precisely the path to its specified leaf. Set $Z_k$ false and all other $Z$'s true. Assign the internal binary-tree variables the actual conjunctions of their children. The root is false, and among the indexed clauses exactly $(i,j,k)$ fails. Thus every unsatisfiable subformula must contain all $M$ indexed clauses, even with every background clause available. There are exactly $d$ non-Horn clauses in this construction.

Each depth-$a$ bank uses $3a+(3^{a+1}-1)/2$ variables. The binary tree uses $2L-1$ variables including its leaves. For all sufficiently large $v$ take

$$
 d=\min\{h,2\lfloor\log_3(v/64)\rfloor\},
 \qquad L=\lfloor v/4\rfloor .
$$

Then each bank has at most $v/64$ leaves and fewer than $3v/128$ prefix variables. Together with $3d=O(\log v)$ selectors and the binary tree, the construction uses at most $v$ variables. An ambient variable budget may include unused variables. Also $3^d\ge\min\{3^h,(v/192)^2\}$. It follows that $M=\Omega(v\min\{3^h,v^2\})$ with an absolute constant. Giving all clauses equal weight and asking the empty query proves the same lower bound for threshold summaries.

For fixed $h$ the coefficient of $v$ in the unweighted upper bound is sharp. Use a single depth-$h$ bank and shared chain variables $z_0,\ldots,z_L$. Add $z_0,\neg z_L$ and all $3^hL$ rules $X_i\land z_{k-1}\to z_k$. On deletion of $(i,k)$ activate exactly path $i$, make $z_0,\ldots,z_{k-1}$ true, and make the rest false. There are $L+O(3^h+h)$ variables. Thus the largest minimum core has size $3^h v+O_h(1)$ for fixed $h$ as $v$ grows.

## Why sampling loses the verdict

Keep the background of the two-bank construction and sample each of the $M$ indexed clauses independently with probability $p$. The sample is unsatisfiable exactly when every indexed clause survives, with probability $p^M$. The deletion witness works even when many other clauses are omitted. Model selection and subsequent repair have their own costs. [Repairing a sampled 3-CNF with candidate assignments](sampled-clause-repair.md)

**Finite checks.** For $0\le d\le4$ and $1\le L\le5$, I evaluated every constructed deletion witness on every original clause. In all 1,815 cases the designated indexed clause was its unique violation. I also tested the weighted construction on 200 random formulas with 12 clauses, 3 to 6 variables and weights from 0 to 3. Exhaustive enumeration found identical minimal-model families for the original and retained formulas at each of the five thresholds from $-1$ to $3$, including ties. The deletion assignments and threshold proof above hold for arbitrary sizes.

## Exact bit complexity of unweighted queries with positive pins

Consider a separate, unweighted problem. An encoder reads $F$ once. A deterministic decoder receives only its binary summary, a set $P$ of at most $p$ positive unit clauses, and a conjunction $D$ of negative clauses. It must decide $F\land P\land D$ for every query. The parameters and variable names are public. The encoder and decoder may do unlimited computation. For $p\in\{0,1,2\}$, the minimum worst-case number of summary bits, over all encoders and decoders, is

$$
                   \Theta\!\left(v\min\{3^h v^p,v^2\}\right).
$$

**Upper bound.** For each of the at most $\sum_{i=0}^{p}\binom vi$ possible $P$, include its facts in each auxiliary Horn branch. Store the least-model $v$-bit mask and a consistency bit for each branch, padding the list with inconsistent entries to length $3^h$. At query time some consistent mask satisfies $D$ precisely when the query is satisfiable. Indeed every model of the query selects a branch and contains its least model, and every consistent branch model satisfies the original clauses. The decoder can scan the masks in the appropriate list without knowing the original exceptional clauses. Another encoding is the $O(v^3)$-bit presence table of all possible width-at-most-three clauses. Use the shorter format determined by the public parameters.

**Lower bound.** In the two-bank construction omit the binary conjunction tree and its forbidden root. Allow an arbitrary subset $R$ of the indexed implications $X_i\land Y_j\to Z_k$. Replace $p$ selector banks by banks of $r=\lfloor v/8\rfloor$ **free** variables each. For sufficiently large $v$, distribute

$$
                 d=\min\{h,(2-p)\lfloor\log_3(v/64)\rfloor\}
$$

choices as evenly as possible among the other $2-p$ banks. For $p=2$ there are no selectors. Use $L=\lfloor v/4\rfloor$ output variables. As in the variable count above this fits within $v$ variables. There are $M=r^p 3^d L=\Omega(v\min\{3^h v^p,v^2\})$ possible implication positions.

To query one position $(i,j,k)$, set its designated free-bank variables true using $p$ positive pins. In each selector bank, forbid the two undesired digit variables at every level using negative units. The exceptional clauses now force the designated digits and the root rules force the desired leaf. Finally include $\neg Z_k$. If the queried row is present, the two forced leaves imply $Z_k$ and the query is unsatisfiable. If it is absent, set just the desired free variables and digit paths true, make $Z_k$ false, and make all other output variables true. This satisfies every retained implication. Thus the answers recover every bit of $R$ using at most $2d+1$ negative units per query. All $2^M$ tables need distinct summaries. Even with variable-length strings, only $2^M-1$ strings have length less than $M$.

I checked this decoding by complete truth tables on two outputs per bank pair. With $p=0$ and selector depths $1,0$, all 64 relations gave the specified answers. With $p=1$, two free variables and selector depth one, all 4,096 relations passed. With $p=2$ and two free variables in each bank, all 256 relations passed. The three tests covered 51,584 query answers. This bit count applies to the whole family of future queries. For one known unweighted verdict a single precomputed answer bit suffices.

## Relation to the MST proof and earlier work

Khanna, Putterman and Song use preservation of connectivity at all weight thresholds in their certificate algorithm. In Claim 3.6 the forest path in a projected graph and the endpoint spokes certify connectivity at the larger of the edge and spoke weights. In Lemma 3.7, once a projection with a heavier spoke succeeds, the next round in the same block must see the connectivity that changes the preferred action. Lemma 3.1 bounds the total number of retained, unsupported, and recursively submitted edges by $\epsilon m+C_\epsilon\sqrt{mv}$. Negative Horn queries have a corresponding persistent witness in the first firing of each head. The two-bank construction shows how many different witnesses may be necessary when positive alternatives are admitted. For $m=\Theta(v^3)$, the indexed clauses account for $m-O(v+\log v)$ of all input clauses. Any fixed $\epsilon<1$ and $C_\epsilon$ therefore give too small an original-clause budget on those instances. [Pinned DLMST manuscript, Fact 2.5, Claim 3.6 and Lemmas 3.1, 3.7](https://github.com/Louiealbp/DLMST/blob/0072335716b145032b418760883daed2a89809db/final.pdf)

Lee proved the cubic endpoint for minimally unsatisfiable 3-CNFs in 2009 using a three-partite construction. His construction gives exact width three with distinct variables in each clause. The parameter here counts the non-Horn clauses, and the statements above use width **at most** three. Pătraşcu and Williams studied the running time of SAT with a Horn part and a few positive clauses of unrestricted length. Backdoor DNFs provide a general framework for reducing SAT to a family of tractable restrictions. Kautz, Kearns and Selman studied model-based representations of Horn theories and compared their sizes with clausal representations. I did not find the stated $h$-dependent extremal bound, the weighted negative-query certificate, or the positive-pin bit bound in the works checked. Priority for these formulations is unverified. [Lee, §3](https://doi.org/10.37236/241) · [Pătraşcu and Williams, Appendix A](https://people.csail.mit.edu/rrw/cnf-sat-feasible.pdf) · [Backdoor DNFs](https://doi.org/10.1016/j.jcss.2024.103547) · [Horn Approximations of Empirical Data, §3](https://www.cs.cornell.edu/selman/papers/pdf/horn-rel.pdf)

An ordinary solver may derive new clauses or exploit the input structure directly. On the rejection family with fixed background, a missing indexed triple can be detected by marking or counting distinct triples. The single-verdict result counts original clauses in a certificate. The bit result accounts for all future queries to one precomputed summary. The unrestricted deterministic time required by SAT remains open.

[Reproducible threshold, negative-query and relation-bit checks](../audits/horn_threshold_audit.py)
