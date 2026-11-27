# Clock crossings for efficiently computable laws on rate digits

**Research journal, 24 November 2026.** Assume deterministic linear-time SAT on the unrestricted logarithmic-word RAM and fix an efficient optimal native prefix machine V. The [constant-width clock crossing](continuum-saving-rates.md) holds almost surely for every law on binary rate digits satisfying the computation bound below. The width H and polynomial-clock exponent a₀ are common to all these laws. This covers singular distributions and gives the crossing at **every atom** of each such law, including each rate with polynomial-time computable binary digits.

A law μ is a Borel probability measure on binary streams. For a finite bit string σ write [σ] for its cylinder. Require a deterministic algorithm returning an O(h+1)-bit dyadic estimate of μ([σ]) within 2^(−h). Let F(j) bound its worst-case running time over |σ|,h≤j. It suffices that log₂(F(j)+2)=o(j2ʲ). In particular both F(j)=2^o(2ʲ) and F(j)=2^O(2ʲ) suffice. The hidden constants can depend on μ.

Map each stream ω to x=3+Σᵢ ωᵢ2^(−i) for i starting at 1. A cylinder with left endpoint v and depth b maps into the **closed** real interval [v,v+2^(−b)]. Both binary encodings of a dyadic produce its actual real rate, and the all-ones stream produces 4. With Tₓ(m)=2^⌊xm⌋ and tₓ(m)=max(1,⌊Tₓ(m)/mᵃ⌋), for μ-almost every ω and **every** integer D≥1 there exists one d∈{D+1,…,D+H−1} with infinitely many witnesses satisfying

    m−D−H < K(y) ≤ K_Tₓ(y) = m−d < m−D ≤ K_tₓ(y),    m=|y|=2ʳ.

The witnesses work for all a≥a₀. At each D at least one fixed d has repeated witnesses on a set of μ-measure at least 1/(H−1).

## Assigning rate tickets

Fix an arbitrary positive-mass parent cylinder I=[σ] of depth s. Encode D, σ and the code of the approximation algorithm together as z. Read a shortest ordinary prefix name q of z with length k, followed by a conditional halt-time record p of length n on (z,k), using the fixed construction with m=2ʳ that encodes both names and their runtimes. The decoder merely runs these programs. The record argument gives Σ_{|y|=m}2^(−K(y))≤C₁2^(−k−n) with a constant independent of z. [Output-length mass proof](continuum-saving-rates.md)

Use b=r−⌈log₂(C₀(r+1))⌉ for a sufficiently large fixed C₀. Eventually b≥s. The M=2^(b−s) depth-b cylinders J extending I partition it, and m2^(−b) lies between C₀(r+1) and 4C₀(r+1). Set N=32M. Find a positive dyadic β≤μ(I) by increasing the precision until a certified lower bound is positive. For the current run approximate μ(I) and μ(J) within β/(8N), compute their ratio and clip it to [0,1]. The resulting estimate qⱼ differs from pⱼ=μ(J)/μ(I) by at most 1/N: the numerator and denominator errors contribute at most 2·(β/(8N))/(μ(I)−β/(8N)). Assign

    nⱼ=max(0,⌊Nqⱼ⌋−1)

tickets to J. Since Npⱼ−3≤nⱼ≤Npⱼ, at least 29N/32 and at most N tickets are assigned, and every ticket leads to a positive-mass cell. Use consecutive disjoint ticket ranges in cylinder order. Unassigned tickets diverge.

After q,p read log₂N bits for the ticket, then ℓ=m−D−c−k−n−log₂N raw bits of rank, where the fixed c pays the native header and ℓ≥0 at late records. If the ticket has zero-based index t among the nⱼ tickets of its cell and its raw rank is u, select missing-word rank t2^ℓ+u. These ranks are distinct within J, even when it receives every ticket. The maximum is below nⱼ2^ℓ≤N2^ℓ=2^(m−D−c−k−n). At least 2ᵐ−2^(m−D−1) words are missing from the early table for names shorter than m−D, so all the allocated ranks fit.

The early cutoff in J with lower endpoint v is ⌊Tᵥ(m)/mᴬ⌋. The linear-SAT missing-word count and unranking fit by Tᵥ for one fixed sufficiently large A. The choice of C₀ and a₀ from the [deadline calculation](continuum-saving-rates.md) makes different cells' internal time intervals disjoint and ensures tₓ(m)≤⌊Tᵥ(m)/mᴬ⌋ and Tᵥ(m)≤Tₓ(m) throughout the **closed** image of J. Hence a word can be paid in only one cell. Endpoint atoms need no special simulation.

At each fixed positive-mass I the search for β takes a fixed time. The required absolute precision for the remaining calls is at most b+O_{μ,I}(1). With j=b+O_{μ,I}(1) we have j2ʲ=O_{μ,I}(m). Thus the full table of at most m+1 calls costs 2^o(m), including polynomial factors in m for arithmetic and universal simulation of the supplied algorithm. It eventually fits within 2ᵐ for every fixed μ,I. This leaves a common exponential margin before every lower-endpoint deadline Tᵥ≥2^(3m); the fixed a₀ and H need no adjustment for the law. [Native model and fixed-block elimination](near-clock-credits.md)

## From local funding to almost-sure witnesses

Put Q=2^(−c−k−n). On a path in a paid cell give each of its paid words charge 2^(D−m)/pⱼ. Total charge on this path is (nⱼ/N)Q/pⱼ≤Q. Other paths have zero charge. Against μ conditioned on I, each paid word has integrated charge exactly 2^(D−m), and the integrated total is QΣⱼnⱼ/N≥29Q/32. The record estimate bounds the integrated charge of words with K(y)≤m−D−H by C₁2^(−H−k−n). Choose H independently of the law so this is ≤Q/8. Every remaining paid word meets the displayed witness condition for some d at each rate path in its cell. Therefore at least 25/32 of the normalized μ-mass of I has a witness on each sufficiently late record.

Taking a limsup over records and then pigeonholing among the H−1 savings gives the same lower fraction of I with one saving recurring at unbounded lengths. The measurable set G of paths with such a recurrence depends on D and V alone. The signed measure E↦μ(E∩G)−(25/32)μ(E) is nonnegative on all cylinders, including the null ones. It is therefore nonnegative on finite unions of disjoint cylinders and, by the monotone class theorem, on all Borel sets. Take E to be the complement of G to obtain μ(G)=1. Countable intersection over D proves the claim. For an atom positive mass forces the individual conclusion. A positive-mass collection of violating paths under one qualifying law would exclude linear SAT. No such law is exhibited here.

Lean verifies the ticket-rank bound, separation of different rank blocks, and summation of the per-cell rounding loss. The clock and measure arguments are manuscript proofs. [Finite ticket lemmas](../lean/RateCylinderLaws.lean)
