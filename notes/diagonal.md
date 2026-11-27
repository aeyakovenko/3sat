# Diagonalization and exact reconciliation of SAT queries

## 1. Direct time-hierarchy reduction

Let a hierarchy language on inputs of length `s` have a diagonal computation with clock `T`. For a uniform reduction with overhead `R` and adaptive SAT queries of encoded lengths `m_1,...,m_r`, a hypothesized time-`O(n^d)` solver gives the worst-path guarantee

```
O(R + sum_i m_i^d).
```

The proposed proof needs this quantity below the time excluded for the specific hierarchy language, allowing the clock and universal-simulation overhead of its model. For example, when the excluded bound is a fixed factor of a power of T smaller than T, a sufficient design target is `R + sum_i m_i^d ≤ T^(1-δ)` with the corresponding exponent gap. No lower bound for these quantities follows from the SAT hypothesis. They are the costs of the proposed simulation.

**First attempt.** Encode rejection by the simulated program as satisfiability of a tableau. Efficient Cook–Levin reductions for the usual random-access models produce quasilinear-size explicit instances in the simulated clock, up to polylogarithmic factors. An explicit one-record-per-step encoding of a padded T-step trace has at least T records. Feeding that encoding to the hypothetical routine gives a budget of order at least `T^d` when the argument charges the promised exponent. The solver might do better on this family. The assumption alone supplies no such estimate. Binary encoding of the clock shortens the clock field, while the explicit records still occupy space. [Williams, Theorem 3.1](https://people.csail.mit.edu/rrw/automated-lbs.pdf)

**Second attempt.** Pad the hierarchy input with `s^p` zeroes to give the solver more room for its clock. Writing `T=s^a` and the padded length as `N≈s^p`, the target speedup expressed in N has exponent `a/p` and the explicit-tableau query charged to its d-th power has exponent at least `ad/p`. The ratio of the two exponents remains d. A lazy representation of the padded input can avoid constructing the padding. It supplies no corresponding compression of the computation described by that input.

**Third attempt.** Enforce self-reference by giving a formula the meaning “the alleged SAT solver rejects this very formula within t steps.” A correct solver with a uniform clock `K n^d` gives a contradiction if such a formula of length n exists and `t≥K n^d`. In a compiler that allocates a distinct record per simulated step, `n≥t` already prevents the two requirements for sufficiently large n. A recursive definition of the desired formula is a specification. A construction must give an ordinary, finite formula and demonstrate this size inequality in the other direction.

## 2. Split the tableau into many small SAT instances

Suppose r subcomputations of length T/r each have explicit formulas of that scale, ignoring logarithms. The SAT calls alone then have budget `T^d/r^(d-1)` for the promised bound. For `1≤r≤T` this is at least T, even if a separate construction reconciles every boundary for free. More generally, for total query length L and r nonempty queries, convexity gives `sum_i m_i^d ≥ L^d/r^(d-1) ≥ L`. This remains valid along each adaptive execution. Hence a sub-T guarantee based only on this budget requires **sub-T total encoded query length** on each execution. It also requires sub-T overhead. A method may benefit from proving that the solver runs faster on its particular queries or reusing computation across calls, in which case a different cost bound is needed.

Independent satisfiability of blocks also loses the shared witness. The formulas `(z)` and `(¬z)` are separately satisfiable and jointly inconsistent. One repair is to have a coordinator ask arbitrarily strong adaptive questions about each block until it can determine whether their feasible boundary states agree. The following lemma tests exactly what one can gain in this repair.

### Exact local reconciliation lemma

Let b boundary bits give a universe U of `m=2^b` states. Two blocks present feasible subsets A and B of U. At each node a public deterministic protocol may ask **any** binary question of one block. It may choose the side and question using all previous replies. It may also start with an h-bit certificate of disjointness. Require that a disjoint pair have some certificate yielding a disjointness verdict, and that no intersecting pair have any certificate yielding that verdict. If every execution uses at most q binary replies, then

```
h + q ≥ 2^b.
```

For each of the `2^m` pairs `(A,U∖A)`, choose one successful certificate. For any fixed certificate, every leaf describes a rectangle in the two inputs, by induction on the history. If two different complementary pairs shared this leaf, both crossed pairs would also reach it. One of the crossed pairs intersects because one of the distinct sets has an element outside the other. This contradicts soundness. There are at most `2^h 2^q` certificate–leaf pairs. This proves the bound. It specializes the classical disjointness fooling set to the proposed SAT subroutine interface. [Roughgarden, Corollary 4.8](https://theory.stanford.edu/~tim/w15/l/w15.pdf)

For b≥2, realize **every** feasible subset by an ordinary explicit CNF on the boundary variables. For each excluded assignment u, use one b-literal clause falsified exactly by u. With a fixed slot per assignment, fill the slots for allowed assignments with a b-literal tautology. Slots can use fixed-width variable names. Each block has `O(m b log(b+1))` encoded bits. Private auxiliary variables for the usual 3-CNF conversion preserve each projected boundary relation. Thus the obstruction is exponential in interface width, yet at most linear in the explicit row count. A RAM with the two tables can scan the aligned slots and detect a jointly allowed state in time linear in the encoding length. An actual SAT solver is also free to combine both blocks in one formula.

**Formal check.** `Adaptive.lean` proves rectangle splicing for arbitrary binary adaptive protocol trees and injectivity of the complementary-pair transcripts for any exact intersection protocol. It also checks that a sound one-sided disjointness certificate and its accepting path together distinguish all complementary inputs. The finite leaf-counting step is the paper argument above. Reproduce with `lean Adaptive.lean` on Lean 4.19.0.

## 3. Which reduction could still succeed?

A compact block encoding would have to exploit the restricted relations arising from one fixed uniform RAM program. The full family of table pairs above costs a separate explicit row per candidate state. A sharper test is to restrict A and B to boundary relations with descriptions of at most L bits generated by the proposed compressor. There can then be at most `2^(L+1)-1` distinct descriptions of one block, so the complementary-pair argument alone gives at most L+1 bits of communication hardness. Indeed, the whole local description can be sent. Any attempt to turn this into a larger lower bound needs a cost for *computing with* that description. This identifies the missing lemma in the repair: a uniform method for compressing reachable boundary relations on the diagonal instances and testing their intersection within the total query budget of section 1.

A distinct option uses alternation to guess all boundary configurations and universally select a block to verify. With unrestricted memory, writing even one full boundary configuration can use T words after T updates. Short descriptions of those configurations require efficient local evaluation and a consistency check. Known speedup and slowdown rules for small-space algorithms explicitly charge the space term. Buss and Williams analyze the limits of those particular rules, leaving space for a different simulation that proves such descriptions exist on the diagonal instances. [Buss and Williams](https://mathweb.ucsd.edu/~sbuss/ResearchWeb/npProofLimits/samCCC-cr.pdf)

### Retest on deterministic prefix blocks

For a deterministic program, a prefix beginning at the specified initial configuration has a **unique** actual endpoint (including all memory needed by the suffix). Its feasible set is a singleton. On this promise the exponential communication obstruction disappears. The first party can send its b endpoint bits, after which the second returns one membership bit, for b+1 replies. There is a matching lower bound of b up to that final reply, even with singleton sets on both sides. On inputs `({u},{u})` for the intersection predicate, distinct u require distinct accepting leaves because the crossed pairs are disjoint. A two-block *deterministic* shortcut therefore has a more specific obstacle than general set disjointness: produce and compare a sufficient endpoint description quickly enough, with charged local computation. In this unlimited-local-computation protocol the first party can obtain the endpoint simply by running the prefix to completion; it can spend the entire clock doing so. For a fixed, known input x and program, unlimited preprocessing even determines the requested bit directly. This is precisely where elapsed computation must enter any speedup theorem.
