# Common SAT inputs that force word revisits

On an explicit distribution of proper DIMACS 3-CNFs, **almost every satisfiable file forces every solver in a fixed finite roster to execute more than a full input scan’s worth of `LOAD` instructions**. The bound is
\[
\#\mathrm{LOAD}\ \ge\ \frac Nw+\Omega\!\left(\frac{N}{w^2}\right),
\]
where \(N\) is the encoded bit length and \(w=\Theta(\log N)\). The extra loads revisit original input words or retrieve words stored during an earlier part of the same execution. The proof allows arbitrary workspace, indirect addressing, writable input, and unlimited time between loads.

The unconditional theorem that a failed charge would violate is the three-party generalized-inner-product discrepancy bound of Babai, Nisan and Szegedy. The execution argument uses three intervals chosen by the solver’s own order of discovery. A globally correct solver attains the order of the revisit charge and runs in \(O(N/w)\) time on the family. **The unrestricted \(O(N)\), \(O(N^2)\), and \(O(N^3)\) SAT questions remain open.** [Babai, Nisan and Szegedy, 1992](https://doi.org/10.1016/0022-0000(92)90047-M)

## What is charged on a run

Use an aligned RAM with separate single-word loads and stores, a fixed number of controller words per program, and \(w=32\lceil\log_2(N+2)\rceil\). The file has \(n\) designated private words, with \(3\mid n\). Cut immediately after the first \(n/3\) and \(2n/3\) distinct private words have been loaded from their original contents. A halt before a cut leaves the remaining intervals empty.

Let \(I\) count distinct private words whose **original contents** are loaded in two or more intervals. Let \(K\) count distinct numerical addresses at which a load retrieves a store from a strictly earlier interval. This includes an earlier store of zero. Arbitrarily many probes of untouched zero scratch contribute nothing. Each address is counted at most once in \(K\).

Put \(a=4096\). For a program \(P\), let \(H_P\) bound the number of its possible controller configurations, including registers, program counter, and terminal states. For any roster \(\mathcal R\) of correct deciders on this RAM, the distribution below satisfies
\[
\Pr\!\left[\exists P\in\mathcal R:
 a I_P+(3w+3)K_P\le n\right]
 \ \le\
 2(n+1)\left(\sum_{P\in\mathcal R}H_P^2\right)
 \left(\frac{1594323}{4194304}\right)^n .
\]
The base is \(0.3801163\) rounded up. For a fixed finite roster the controller factor is polynomial in \(N\). The exceptional probability is exponentially small in \(n\), including after conditioning on either verdict. Thus one actual file works for the whole roster even though its members can make different cuts and revisit different addresses.

## The distribution and the encoded length

Each of \(n\) vertices carries an independent uniform \(a\)-bit symbol. In each lane \(j\), partition the vertices into triples. Compute the AND of the three lane-\(j\) bits on each triple, then XOR all the ANDs. Every source bit occurs in exactly one AND. The SAT verdict will be this parity.

Choose the \(a\) partitions so that **every** division of the vertices into three equal groups has at least \(48n\) triples meeting all three groups, counting lanes separately. Here is an existence proof with constants. In each lane take an independent random permutation and group consecutive entries in threes. For a fixed balanced division the expected number \(X\) of such triples is at least \(2an/27\). Expose all \(an\) permutation entries. Swapping two possible next entries couples the completions and changes at most two triple indicators. The exposure martingale therefore has differences bounded by two, giving
\[
 \Pr[X<48n]\le
 \exp\!\left(-\frac{(2a/27-48)^2}{8a}\,n\right).
\]
The exponent coefficient is exactly \(185761/93312>\ln 3\). A union bound covers all \(3^n\) group assignments. One can take the first successful tuple in finite enumeration. Finding it efficiently is unnecessary for the lower bound.

For the physical encoding, use three anchors forced false by seven proper clauses. Give vertex \(v\) flags \(F_{v,s}\) for \(0\le s<2^a\) and lane variables \(X_{v,j}\). Its single private clause is \((F_{v,s_v},f_1,f_2)\). Public implications from each flag fix all its lane bits when that flag is true. Unselected flags may be false. Each triple uses two AND gates and one XOR into a running parity, costing ten proper ternary clauses. Start with a false anchor and pin the final parity true. This gives the desired verdict. Since the ANDs use disjoint independent bits, the exact probability bias between the two verdicts is \((3/4)^{an/3}\).

Give the comment, header, and each clause one padded ASCII word. The exact word count and bit length are
\[
 b=1+a2^a+\frac{10a}{3},\qquad D=10+bn,\qquad N=wD.
\]
The ten fixed records are the comment, header, seven anchor clauses, and final pin. Choose the least \(h\) with \(32hD+2\le2^h\) and set \(w=32h\). Minimality gives \(h=\lceil\log_2(N+2)\rceil\). All names are dense and at most \(O(D)\), so the decimal tokens fit in the allotted \(4h\) bytes per row for sufficiently large \(n\). The factor \(a2^a\) is enormous. It is included in every conversion from \(n\) to encoded bits.

## Why few revisits would violate discrepancy

Group the vertices by the interval of their first original load. Assign any never-observed vertices to fill the remaining groups in discovery order, obtaining three groups of size \(n/3\). Fix this group assignment, both boundary controllers, and a claimed verdict.

Suppose \(I\le i\) and \(K\le k\). Supply an \(n\)-bit mask and the \(a\)-bit symbols for the old private inputs needed outside their own group. For each of the \(K\) carried addresses, supply the address and the **last store in each of intervals one and two**, with an explicit absent flag for each. A padded slot takes \(3w+3\) bits, including its occupancy flag.

Each interval can now generate its own tentative execution from its group alone. A local store supplies later local loads. Otherwise the interval uses the latest reported earlier store, or the original word when none is reported. An original private word must be visible or listed. Each owner checks its listed symbols. Each writer checks its reported final stores, including claims of absence. Each interval checks its controller endpoint or halt. The first two intervals stop on their discovery quota or halt, so the certificate needs no timestamps. For counting purposes a public horizon can be the maximum genuine runtime on this finite family.

One check is essential. For each ordered pair of intervals \(u<v\), compare the stores of \(u\) against the loads of \(v\) that used an original or initialized value **outside the carried-address directory**, before any local store. Require the two address sets to be disjoint. This is a test on just two groups. It handles arbitrary data-dependent addresses and arbitrarily many fresh probes. On a genuine run the truthful directory passes. Conversely, when all checks pass, chronological induction gives the actual reply at every load and authenticates the claimed verdict.

Consequently each fixed certificate describes a monochromatic set whose indicator is a product of three pair functions, one for each pair of groups. Condition on all bits outside the triples meeting all three groups. The remaining verdict is generalized inner product on at least \(48n\) independent triples, up to a fixed sign. Distinct triples in different lanes use independent bits even when they meet the same vertex. The three-party discrepancy bound gives monochromatic mass at most
\[
 (3/4)^{48n/4}=(3/4)^{12n}.
\]
In the Cauchy–Schwarz proof, duplicate the first two parties’ strings independently. Averaging over the third string gives zero unless the two difference strings have disjoint support, an event of probability \((3/4)^r\) on \(r\) triples. Taking fourth roots gives the bound.

The group assignments and old-input masks cost at most \(6^n\) choices. Under \(ai+(3w+3)k\le n\), their remaining fields cost at most \(2^n\) choices for each of at most \(n+1\) choices of \(i\). Including the two controllers, sign, and roster gives the displayed probability, since \(12(3/4)^{12}=1594323/4194304\).

Earlier journal arguments used three banks with recoverable checkpoint configurations, or two-way cuts with bounds on incoming memory. The step here is the pairwise authentication of **absent earlier stores**, combined with a physical layout that retains discrepancy for every solver-chosen three-way division. This is a manuscript argument. Historical priority for the combination is unverified. [Earlier three-bank checkpoints](three-bank-solver-phases.md) · [Earlier distributional two-way cut](sparse-reply-sat-cuts.md)

## Actual elapsed time and the failed amplification

On **every positive file**, replacing any one non-anchor clause word by the padded clause \((1,2,3)\) makes the file unsatisfiable. The seven unchanged anchors force all three literals false. Thus every correct solver must load each of the \(D-9\) non-anchor clause words before overwriting it.

The \(I\) later original reads and \(K\) store-sourced reads are disjoint events, and neither can be one of those compulsory first loads. The \(K\) addresses also require \(K\) distinct store instructions. Hence on a good positive file, for every roster member,
\[
 \#\mathrm{LOAD}\ge D-9+I+K,\qquad T\ge D-9+I+2K.
\]
In particular, once \(3w+3\ge2a\),
\[
 T>\frac Nw-9+\frac{2(N/w-10)}{b(3w+3)}.
\]
The additive term counts instructions on the genuine run. The triple partitions serve only to choose the distribution.

**The revisit charge is attainable in order.** A globally correct solver can validate the private clauses in physical order, extract each \(s_v\), and pack the symbols consecutively into fresh scratch words. It keeps the unfinished word in a register. After the last private load it can reconstruct every private clause from \(O(1+an/w)\) packed words. All occurrence lists and propagation queues can be built in interval three. Verify the seven anchors, set them false, and run unit propagation. On this family it fixes every selected symbol, then every gate. Each remaining flag implication is satisfied or forces its unselected flag false. On unrecognized or unresolved files the program uses a complete solver.

On the family this gives \(I=0\) and \(K=O(1+an/w)\). Parsing constant-word records in constant time each can use tables on chunks of at most \(\tfrac12\log_2 N\) raw bits. Their \(O(\sqrt N\,\mathrm{polylog}\,N)\) setup and cells are respectively \(o(D)\) and \(o(n/w)\) at fixed \(a\). Queue-based propagation takes linear time in the clause count. The resulting \(O(D)=O(N/w)\) clock pays the entire revisit charge on both verdicts. This is the obstruction to obtaining even the linear-in-bits exclusion from the argument.

For a finite roster with **different aligned logarithmic widths**, the revisit proof also works after a layout adjustment. Use a public row slot of \(Ch\) bits wider than three times the largest native width, and spell each flag with a vertex-specific decimal prefix and a fixed-length decimal suffix for \(s\). Put other identifiers in a disjoint range. Within the middle third of each private slot, shift the suffix by public whitespace before the flag. Each roster member has only \(O_{\mathcal R}(1)\) word boundaries in the slot, and each boundary forbids only constantly many byte starts. Eventually one placement puts the entire varying suffix in one native word for every member. Different vertices have different carrier words. The same probability proof uses each program’s own \(w\); the exact \(D-9\) compulsory-load formula above uses the one-word-per-row layout.

## A ceiling on the discrepancy proof

For any fixed partition in which whole private clauses are supplied by individual parties, the positive side has a cover by at most \(2^{v_*+O(\log N)}\) cylinder intersections, where \(v_*\) is the maximum number of distinct occurring names on such files. Indeed the public family of assignments hitting every positive file takes \(v_*+O(\log N)\) bits to index. For each fixed assignment the test that all clauses pass is the intersection of the parties' own local tests. Under any distribution with positive mass \(\mu_+\), some monochromatic cylinder intersection has mass at least \(\mu_+2^{-v_*-O(\log N)}\). The same conclusion holds if a constant number of parties supplies whole literal tokens in known clause slots, with an additional \(\lceil\log_2 3\rceil\) certificate bits per split clause naming one true literal.

On the aligned one-clause-per-word layout, \(v_*=O(N/w)\) even if the alphabet in a private row grows. Consequently when the positive mass is bounded away from zero a discrepancy bound for one fixed division can charge only \(O(N/w)\) certificate bits. With \(w\)-bit stored addresses and values in the transcript above, this scale corresponds to \(O(N/w^2)\) cross-interval directory entries. The explicit upper algorithm shows this order is attainable on the constructed family. A stronger runtime conclusion would need information about executions beyond the existence of a large monochromatic cylinder. [Assignment cover and its literature](the-static-ceiling-for-equality-encoded-as-sat.md)

## Checks

- Generic DPLL and the packed-symbol propagation calculation agreed on **264 serialized proper DIMACS files**, including 74 positives. All **296** tested single-clause replacements on positives produced UNSAT. These physical fixtures use one to three lanes. The full \(2^{4096}\)-flag catalog was not materialized.
- At the proof’s **4,096 lanes**, a seeded nine-vertex wiring had **3,801 to 4,088** triples meeting all three groups over all **1,680** ordered balanced divisions. The asymptotic existence proof is independent of this sample.
- A writable-memory fixture checked **16,740** header/input pairs, including overwritten input, zero stores, and forged writer reports. With the pairwise disjointness checks, every passing header gave the true verdict. Removing those checks admitted **30 false verdicts**. A separate adaptive execution replayed all 4,096 inputs across 19 discovery partitions, including halts before the first cut.
- On the local **16-selector-bit census**, the nine-step upper program agreed with assignment enumeration on all 65,536 files and took nine steps on 20,720. I also replayed the four existing eight-step programs covering all 64 selected targets. Thus the known 28-of-64 slow cohort for **one** program cannot by itself yield a common nine-step target for that roster. Those clocks use four-bit words and 16 selector bits. [Finite roster construction](four-programs-cover-the-eight-step-native-cohort.md) · [Round 4 cohort bound](which-four-word-sat-targets-finish-in-seven-steps.md)

Reproduce the new checks with `python3 -B three_phase_revisit_audit.py`. [Revisit audit](../audits/three_phase_revisit_audit.py)
