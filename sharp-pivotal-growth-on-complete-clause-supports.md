# Sharp growth of the number of individually necessary SAT clauses

For each fixed \(k\ge2\), among unsatisfiable formulas with exactly one proper signed \(k\)-clause on each \(k\)-subset of \(v\) variables, the largest possible number of individually necessary clauses grows as \(\Theta_k(v^{k-1})\). A clause is individually necessary if deleting it makes the formula satisfiable. Equivalently, it has an assignment that violates just that clause. A single negation change, on any of its literals, then makes the formula satisfiable as well. The witnesses for different clauses may be different.

The [upper bound and its proof](private-clauses-in-complete-signed-triple-families.md) apply a splitting argument to private assignments. Here is a family achieving the exponent. It describes what a sensitivity-based size successor can preserve even with one signed clause on every support.

## Two groups of choices for width three

Take five anchors \(z_1,\dots,z_5\) with the ten clauses of the uniquely all-zero seed. Introduce choices \(a_1,\dots,a_p\) and prefix bits \(s_0,\dots,s_p\). Require \(s_0=1\), \(s_p=0\), using the corresponding signed endpoint literal with \(z_1,z_2\) as padding. For each \(i\) include \(\neg s_{i-1}\lor a_i\lor s_i\). The chain forces at least one \(a_i\) true. Repeat with choices \(b_1,\dots,b_q\) and prefix bits \(t_0,\dots,t_q\). For every \(i,j\) include the target clause
\[
                 \neg a_i\lor\neg b_j\lor z_1 .
\]
These constraints are already unsatisfiable. Their supports are distinct. [All-zero seed, including its ten signed clauses](single_support_seed_census.py)

For each pair \(i,j\), set just \(a_i,b_j\) true among the choices, let \(s_r=[r<i]\), \(t_r=[r<j]\), and set all anchors zero. This assignment violates exactly the target with indices \(i,j\). Fill every unused triple with one signed clause that all \(pq\) assignments satisfy. To see that this can be done, a triple containing an anchor has a missing bit pattern because the anchor is fixed. Otherwise two of its coordinates come from the same group. As subsets of the choices in this group, the truth sets of its coordinates are singletons and tails. Any two such sets are nested or disjoint, so their two-bit projection omits at least one pattern. Extend that pattern to the whole triple and use it as the new clause's falsifying pattern.

The completed formula has \(2p+2q+7\) variables and at least \(pq\) individually necessary clauses. Balanced groups give a quadratic lower bound. Increasing either group adds a row or column of private witnesses. Filling newly introduced supports is possible at every length. Thus this particular induction succeeds for the number of pivotal clauses. Its computational meaning is limited. The completed formulas fall inside the [deterministic packed-scan upper bound](complete-csp-in-linear-dimacs-time.md).

## Fixed clause width

For \(k\ge3\), take \(k-1\) disjoint groups of the same kind. Pad the endpoint units with \(k-1\) distinct false anchors and the chain implications with \(k-3\) distinct false anchors. For each tuple of choices, one from each group, include the clause consisting of their \(k-1\) negations and one positive false anchor. All preliminary supports are distinct. Satisfying the endpoints and chains requires a true choice in every group, whose target clause then fails.

On deleting one target, pick exactly its choices with their threshold prefix bits as above. Every previously unspecified \(k\)-set either contains an anchor or has two positions in the same group. Consequently its projection of the entire family of these assignments omits a pattern, and signing that support to forbid the omitted pattern preserves every private witness. Balanced groups give \(\Omega_k(v^{k-1})\) targets. A bounded number of extra unused coordinates can be added at any length by setting them to zero in all witnesses and filling every new support with a clause satisfied by those witnesses. The original unsatisfiable subformula persists.

There are constant-size forced-zero anchor seeds for every such \(k\). On \(m\) anchors choose independently, for each \(k\)-support, a uniformly random forbidden pattern other than zero. A fixed nonzero assignment has a nonzero restriction on at least \(\binom{m-1}{k-1}\) supports containing a particular one bit. The expected number of nonzero satisfying assignments is at most
\[
 (2^m-1)\left(1-\frac1{2^k-1}\right)^{\binom{m-1}{k-1}} .
\]
For \(k\ge3\) this is less than one for all sufficiently large constant \(m=m(k)\). Some signing therefore has zero as its unique solution, and finite enumeration can fix one such signing once and for all.

At width two, four anchors are forced zero by the implications around a directed four-cycle and the clause \(\neg z_1\lor\neg z_3\). Fill its remaining anchor pair with any clause satisfied by zero. Use the endpoint pins \(s_0\lor z_1\), \(\neg s_p\lor z_1\), and one implication \(\neg s_{i-1}\lor s_i\) for every \(1\le i\le p\). All these implications are individually necessary, witnessed by \(s_r=[r<i]\). Nested tails allow every omitted pair to be filled as before. This gives the linear lower bound at width two as well.

## Reading a sign on the ordinary RAM

Place all target clauses consecutively, using dense variable names. When the groups have balanced lengths growing with \(v\), number every choice variable above a fixed positive fraction of \(v\). Changing the sign of one target literal can use the same file length, by replacing its minus with ASCII space while retaining the ordinary token delimiter. This is one changed byte position. Distinct changed positions, one per target, have spacing \(\Omega_k(\log v)\) bytes. A native \(\Theta(\log N)\)-bit input read can therefore cover only a bounded number of them, where \(N=\Theta_k(v^k\log v)\) is the physical file length. On the unsatisfiable file any correct deterministic RAM must read each such position before overwriting it. Otherwise the modified file would have the same computation and the opposite verdict. This gives \(\Omega_k(v^{k-1})\) input reads on that file. For fixed \(k\) this is below the cost of reading the complete file. No RAM processing lower bound follows from counting additional assignments that witness a change in the same position.

The finite audit checks all 103,766 signed supports against the designated 95 witnesses across six constructed formulas of widths three, four and five. CaDiCaL independently refuted all six complete formulas. The core Lean proof verifies the two-group omission for every triple, the chain endpoint implication and the identity of each failing target. The compulsory anchor gadget and general-width construction are justified above. [Finite audit](quadratic_pivotal_complete_cnf.py) · [Parametric ternary-clause lemmas in Lean](ChoiceChainPrivateWitness.lean) Priority for the extremal formula family and its sharp upper bound is unestablished.
