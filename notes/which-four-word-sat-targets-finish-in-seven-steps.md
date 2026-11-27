# Exactly which four-word SAT inputs finish in seven steps

On the 64 complementary positive inputs defined below, **every correct program accepts by step seven either no inputs or exactly one row of eight**. The row has a fixed even first word \(p\in\{4,6,8,10\}\). Each of the four rows is attainable. Moreover, every seven-step success uses the same computed address, \(q\mathbin{\&}n\), to read the first word.

Consequently, 32 of the targets have pointwise optimum seven and the other 32 have pointwise optimum eight. For a **single** correct program, at least **28 of the 64 targets take nine or more steps**. Under the uniform distribution on these targets, the mean clock is at least \(534/64=8.34375\) instructions. These bounds allow arbitrary program size, writable inputs, indirect addressing, and unlimited time on rejecting executions.

The previous census established the exact global optimum of nine. The row classification and the quantitative bounds on how many executions reach nine are this round’s results. The unrestricted linear, quadratic and cubic questions for ordinary explicit SAT remain open. [Previous nine-step theorem and census dependencies](exact-nine-step-clock-for-four-sat-words.md)

## The seven-step programs

Write the four nibbles in address order as \((p,q,m,n)\). They specify positive and negative units on eight variables, together with a fixed positive disjunction. The file is SAT precisely when
\[
(p\mathbin{\&}m)=(q\mathbin{\&}n)=0,\qquad (m,n)\ne(15,15).
\]
The target set is
\[
S=\{(p,q,15-p,15-q):4\le p,q\le11\}.
\]
Every word of every target is pivotal. Replacing it by 15 conflicts with its nonzero mate. A correct accepting run must therefore read all four original cells before their first overwrite.

Fix an even \(a\in\{4,6,8,10\}\). Load \(q,m,n\), compute \(j=q\mathbin{\&}n\), and load \(x=\mathrm{mem}[j]\). These are five instructions. Accept if the next two comparisons give \(m=15-a\) and \(x=a\). A failed comparison transfers to a complete solver.

If \(j=1\) or \(3\), the indirect load returns an odd word. At \(j=2\) it returns \(m\), and at \(j\ge4\) it returns zero. Hence acceptance forces \(j=0\) and \(p=a\). The path accepts 81 of the 65,536 files, all satisfiable, including precisely the eight targets in row \(a\). This is the journal’s even-word shortcut. Its failure for odd words has a concrete witness: at hexadecimal `05A1`, the load returns 5 and \(m=10\), yet \(q\mathbin{\&}n=1\). The lower bound below excludes every alternative seven-step path on the odd rows. [Earlier shortcut and the separate `5488` pointwise result](eight-steps-on-one-four-word-sat-input.md)

There is also a single **eight-step accepting path covering 16 targets**. After the same five instructions, compute \(h=m\ll(m\bmod4)\) in one native modulo-count shift, truncated to four bits. Test \(m<h\) in unsigned order and \(x=h\). The only passing \((m,h)\) for the first comparison are \((1,2),(5,10),(7,8)\). In each case \(h\) is even, nonzero and disjoint from \(m\), so the indirect-load proof applies again. Full assignment enumeration verified all **486** accepted files. The path covers the two entire target rows \(p=8,10\).

## Why every seven-step success has this form

Unfold one accepting execution. Its comparisons may be evaluated on their saved operands at the end of this fixed path. Any negative file giving the same comparison outcomes would follow the original path and be accepted. Four fresh reads leave room for at most three comparisons.

**Raw comparisons and writes.** On the subdomain with all four words in \(4,\ldots,11\), a raw word used as an address points into scratch. The audit tested all 64 targets and all 3,772 high-word negatives. There are 195 raw comparison-outcome tables meeting a target and 14,620 distinct target-hitting intersections of two. Every target-hitting conjunction of three raw comparisons also passes a negative.

This excludes paths with no arithmetic, including writes. With four loads, each is fresh on the target. A raw-address store points high, and a literal-address store cannot hit a later fresh cell. The only case with both a store and a surplus load has just one final comparison. A load whose value depends on whether it saw the store splits the high files by equality of two raw or literal addresses. If that selection is nonconstant, the load is surplus on the target. On each resulting part all later fresh reads again select fixed original columns. The final test and the address equality are covered by the raw comparison check.

**One comparison.** A read-only path has room for at most two arithmetic operations. The audit reruns the read-only enumeration with the required support reduced from 37 targets to **one**. Its 22,064 negative examples have the property that loading through any raw input word returns zero. For an arithmetic result \(r\), repeated loads can supply only \(r,L(r),L^2(r),L^3(r)\), since \(L^4(r)=L^2(r)\) on this domain. Granting both operations these extra values covers even arbitrarily many read-only loads. The run examined 1,182 first-result tables and 3,014,206 second-stage quick tables. No comparison separated even one target. [Read-only enumeration used for this replay](../audits/two_arithmetic_results_with_unlimited_native_reads.cpp)

With one arithmetic operation and one store, all four loads must be fresh. If the computed word \(r\) supplies a load address, restrict to \(r\) equal to the omitted direct address. On that slice the reads are fixed, the write misses future fresh cells, and the final comparison sees raw words or literals. If the loads are direct, a store addressed by \(r\) can matter only where \(r\) hits a later load address. The audit permits any subset of the four addresses for those later loads. Every negative passing the erased comparison must hit that subset, while an accepted target must miss it. All **954** arithmetic tables on the high suite failed these necessary tests.

**Two comparisons.** This leaves exactly four loads, one arithmetic operation and two comparisons. On a high target the only possible fresh indirect address is the arithmetic result. There are five layouts: all four reads direct, or one of the four cells omitted from the direct reads. The audit enumerates all 20 native operations, all available operand pairs, both signed and unsigned comparisons, and both branch outcomes. The five layouts yielded \(1330+4(952)=5138\) distinct first-result tables.

| Negative suite | Initial negatives | Guard pairs surviving initially | Counterexamples added | Guard pairs surviving refinement |
|---|---:|---:|---:|---:|
| Seed 27504 | 3,287 | 119 | 58 | 16 |
| Seed 50427 | 3,295 | 1,621 | 63 | 16 |

Every surviving representative was replayed on all 65,536 physical files. In both runs, all 16 survivors omitted the direct read of \(p\). The only native operand choices agreeing with their address table on the suite were `AND(q,n)` and `AND(n,q)`. Each surviving target mask was one entire even row. Equality of tables was used only on the suite where it was checked. Any globally sound path must survive that finite test.

There is one further constraint for a shared program. The audit retains the possible **first** comparison outcomes on the entire suite, including files on which the later read would fail freshness. The 16 pairs gave 20 distinct first-outcome signatures. **No two were complements.** Two fast paths taking opposite outcomes at the first comparison would require complementary signatures. Two fast accepting paths taking the same first outcome and opposite second outcomes would make that first outcome sufficient for acceptance, yielding a one-comparison path. Both possibilities are excluded. Thus a program reaching any target by seven reaches exactly one entire even row. Four literal loads and four equality tests give the pointwise upper bound of eight on every other row. [New enumeration](../audits/seven_step_cohort_guard_pairs.cpp) · [Scalar replay and checks](../audits/seven_step_cohort_audit.py)

## How many executions reach nine

The existing eight-step census bounds a single accepting leaf with \(1,2,3,4\) comparisons by \(36,18,8,1\) targets respectively. The extra constraint is elapsed time **before** branches separate.

At a prefix containing a negative file, let \(B(d,c)\) bound the number of targets that can still finish by eight after \(d\) noncomparison instructions and \(c\) comparisons. A successor containing only positive files could accept immediately. Pad that accepting path with constant comparisons to step eight. Its support is then bounded by
\[
A_0=A_1=A_2=A_3=0,\qquad
(A_4,A_5,A_6,A_7)=(1,8,18,36),
\]
since the padded path has \(8-d\) comparisons. A data instruction preserves the set of files at the current control location. A comparison sends a negative to at least one child. Consequently, with boundary zero at \(d+c=8\), we may take
\[
B(d,c)=\max\!\left\{B(d+1,c),\;2B(d,c+1),\;A_d+B(d,c+1)\right\}.
\]
The root bound is **36**, leaving at least **28** targets at step nine or later.

If a seven-step row occurs, its last comparison is instruction seven. The sibling at that comparison contains a negative, since otherwise the program could accept the row by six. That sibling contributes at most \(B(5,2)=8\) fast targets. The sibling at the first comparison contributes at most 18. Including the row itself, at most \(8+8+18=34\) targets finish by eight in this case. Relative to nine steps on each target, the total saving is at most \(34+8=42\) instructions. Without a seven-step row the saving is at most 36. Hence the sum of the 64 clocks is at least \(9\cdot64-42=534\).

The exact maximum number that one program can finish by eight remains between **16 and 36**. The audit replays the `4488` control, the 1,914,264-candidate two-ALU exclusion at `5488`, and the nine-step program on all 65,536 files. For the older eight-step leaf capacities the worker verified the archived interval coverage and source fingerprints. The larger kernels have a separate complete replay. [Archived theorem and replay procedure](exact-nine-step-clock-for-four-sat-words.md)

## Encoded length and the failed direct-sum step

The finite clock uses **16 selector bits** and word width four. For comparison, serialize a target as ordinary ASCII CNF with header `p cnf 8 9`, the eight-literal clause, and eight unit rows. Including newlines, the header costs 10 bytes, the long clause 18, and the units \(32+r\), where \(r\) is the number of negative units. The physical length is exactly **\(8(60+r)\) bits**, ranging from 496 to 528 on this suite. The audit checked all 64 serializations. The four-bit instruction bound applies to the selector representation.

Concatenating independent selector records also defeats an additive clock induction. Pack records as hexadecimal `pqmn`. For a word \(X\) holding complete 16-bit records, put \(U=\sum_j2^{16j}\), one low bit per record, and \(C=X\mathbin{\&}(255U)\). A conflicting unit is present iff \(C\mathbin{\&}(X\gg8)\ne0\). Some record has both negative masks full iff
\[
(C+U)\mathbin{\&}(U\ll8)\ne0.
\]
Each lane adds at most \(255+1\), so no carry crosses a record boundary. For example, take power-of-two widths \(w\ge16\) and physical lengths \(N=2^w-w\). Then \(w=\lceil\log_2N\rceil\) and each word holds whole records. Constructing the masks and testing the conjunction takes \(O(w+N/w)\) executed instructions. The scan passed 6,000 packed-product checks. Independent semantic constraints therefore do not supply nine disjoint execution steps per record as the word width grows.

Reproduce the new finite results from the clone with `OPENBLAS_NUM_THREADS=1 python3 -B seven_step_cohort_audit.py`. The native path reductions are manuscript arguments, and the stated finite exclusions are executable enumerations.

The tree recurrence for mixed prefixes and both numerical entries used above are kernel-checked in Lean. The transfer from native paths to the finite tables and the native case splits are manuscript arguments with executable enumerations. [Lean recurrence](../lean/MixedPrefixDeadlineCapacity.lean)
