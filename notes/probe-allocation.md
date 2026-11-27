# The best gap for probing a graph of implications

**Research journal, 24 November 2026.** I tried to strengthen the gate test for the coded diagonal computation by spending the sampling budget on the gates that carry a contradiction. For the part of the construction that propagates one bit by implications, the optimum has an exact formula. It allows nonlinear checks, arbitrary distributions over sets of gates, and inconsistent answers across different sets. The formula identifies precisely what a shortcut would have to buy. [Earlier circuit-value game](referee-certificates.md)

## The game

Take a finite directed graph. A source pin requires a bit to be zero, a target pin requires a bit to be one, and an arc u→v requires xᵥ≤xᵤ. A row is one pin or arc. Assume a source can reach a target. Let D be the least path length from any source to any target, and put G=D+1. A vertex can have conflicting pins, giving D=0.

The maximizing player names one row. Independently of that choice, the referee draws a bag of at most k vertices, k≥1. The minimizing player sees the bag and returns its bits. It can choose different values for the same vertex in different bags. The referee gives a score in [0,1] using the row, the bag, the answers, and any private coins. We require **row soundness**. On *each* full Boolean assignment satisfying a row, honest answers have expected score at most 1/2 on that row, even if other rows fail. This is a property of an individual test on arbitrary assignments. A checker allowed to use the result of global reachability could violate this requirement.

Over all such referees, the largest possible game value minus 1/2 is exactly

    min(1/2, k/G) / (G+1).                                      (1)

Other paths and outgoing branches can be arbitrarily numerous. The theorem grants the referee knowledge of the graph and a shortest conflicting path. Construction cost on a succinct graph is a separate question.

## Upper bound, including nonlinear checks

Give each vertex its shortest directed distance from the source set, capped at D, with unreachable vertices also put at level D. The G nonempty levels run from 0 to D. Every arc increases the level by at most one, all zero pins are at level 0, and all one pins are at level D. Write pᵥ for the probability of probing v and Pⱼ for the sum of pᵥ on level j. Then ΣPⱼ≤k.

Use G+1 Boolean assignments indexed by t=0,…,G, putting a one at precisely the vertices of levels at least t. A zero pin fails only at t=0, a one pin only at t=G, and an arc can fail only when it advances across cut t by one level. At a failing assignment a single endpoint change repairs the tested row. Couple the honest transcripts of the two assignments with the same coins. Their payoffs can differ only on bags containing the changed vertex, by at most one then. For an arc either endpoint can repair it. Consequently the excess on a failing row is at most cₜ, where

    c₀ = min(1/2,P₀),                 c_G = min(1/2,P_{G−1}),
    cₜ = min(1/2,P_{t−1},Pₜ)          for 0<t<G.

Rows that hold have nonpositive excess. If any cₜ is zero, its assignment defeats every row. Otherwise draw t with probability proportional to 1/cₜ. This gives a legitimate right strategy on every bag. Every row has excess at most 1/Σₜ(1/cₜ).

Each cₜ≤1/2. Also, delete any one cut t. Match the remaining G cuts to distinct adjacent levels by matching r<t to level r and r>t to level r−1. The reciprocal cap on each matched cut is at least the reciprocal mass of its level. Summing over all G+1 deletions gives

    G Σₜ 1/cₜ ≥ (G+1) Σⱼ 1/Pⱼ ≥ (G+1) G²/k.

The last step is Cauchy–Schwarz. These two estimates give (1) as an upper bound. No form for the referee's payoff was assumed beyond boundedness and row soundness.

## A referee attaining the bound

Keep one shortest path, indexed 0,…,G−1. Set λ=min(1/2,k/G). Use bags containing no two consecutive path vertices, with marginal inclusion λ at each such vertex. When 2k≥G, sample the even or odd positions with equal probabilities. Otherwise take a uniform cyclic shift modulo G of {0,2,…,2k−2}. Both procedures respect the budget.

On an arc row from i to i+1 of this path, pay the reported bit when i+1 is sampled, one minus the reported bit when i is sampled, and 1/2 otherwise. On the initial pin pay the bit if sampled, and on the final pin pay one minus the bit if sampled. For either pin, pay 1/[2(1−λ)] when its vertex is absent. This lies in [0,1]. Other rows receive constant score 1/2. For any right strategy let mᵢ be its conditional mean reply at i given its inclusion. The expected excesses on the selected rows in order are

    λm₀,  λ(m₁−m₀), …, λ(m_{G−1}−m_{G−2}),  λ(1−m_{G−1}).

This also gives row soundness on honest answers. Uniformly mixing these G+1 rows makes the terms telescope to λ/(G+1) against every right strategy, including one that chooses its answer from the entire bag. If G=1 the two pins alone suffice. This proves attainment.

## What this buys for SAT

For one probe the best gap has order 1/D² for D≥1. Even reading the whole graph leaves a gap of order 1/D in this row-sound game. If a directed path of h arcs is augmented with every valid forward shortcut of span at most s, with 1≤s≤h, its new D is exactly ⌈h/s⌉. Substitution in (1) gives the improvement for every probe budget. A single endpoint implication reduces D to one. Producing and checking sound long implications on the actual computation is the missing part. On a succinct implication graph a supplied path with D arcs is itself a certificate requiring D+1 vertex names and D edge checks.

There is a structural difficulty in applying reachability directly to the gate tableau. The relation z=x OR y cannot be the existential projection of any conjunction of binary Boolean clauses, even with arbitrarily many auxiliary bits. Satisfying assignments of each binary clause are closed under coordinatewise majority of three assignments. If the majority falsified both literals, the two groups of at least two assignments falsifying each literal would intersect. Conjunction and existential projection preserve this closure, by taking the majority of three full witnesses. The three legal triples (1,0,1), (0,1,1), (0,0,0) have illegal majority (0,0,1). This excludes faithful local replacement of that gate by implications with pins or by general 2-CNF. A simplification tailored to deciding the final bit has a different correctness requirement. Competing-prover protocols with richer access to the computation are an established approach. [Kol and Raz](https://theoryofcomputing.org/articles/v010a005/)

Lean checks the path incidence inequality used before Cauchy–Schwarz, after common-denominator scaling. The game theorem above is a manuscript proof. An exact rational experiment checks the attaining sampler against contextual responses for 78 path-length/budget pairs, and checks the cut upper bound on 1,001 inconsistent graph/sampler instances. I have not established priority for (1). [Lean](../lean/ProbeAllocation.lean) · [Experiment](../audits/probe_allocation_experiment.py)
