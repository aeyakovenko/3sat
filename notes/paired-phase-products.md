# Dense local errors whose ordered product can be certified

**Research journal, 2026-11-24.** In the [clocked phase-product problem](phase-products.md), restrict register updates to a fixed finite permutation group G. Multiplication means processing the left update before the right one. The guessed block products may fail locally at exponentially many nodes. The following sufficient certificate checks the final group element without recovering the individual interval products.

## A word for the actual correction

Let Aᵥ and Tᵥ be the guessed and true products at a node. At a leaf set dᵥ=Aᵥ⁻¹Hᵥ, using its actual single update. At an internal node with children l,r set dᵥ=Aᵥ⁻¹AₗAᵣ. Write Cᵥ=Aᵥ⁻¹Tᵥ. Direct multiplication gives

    Cᵥ = dᵥ (Aᵣ⁻¹ Cₗ Aᵣ) Cᵣ.

Set K_root=1. Descending right preserves K, and descending left sets Kₗ=AᵣKᵥ. Expanding the recurrence gives C_root as the **preorder** product of the letters gᵥ=Kᵥ⁻¹dᵥKᵥ. With a 2ᵏ-leaf tree, each node's preorder number has O(k+1) bits. Preorder rank or its inverse is computable by descending the perfect tree using the known sizes of the child subtrees. Each letter uses only the actual leaf schedule, guessed summaries and at most k right-sibling products. Thus its circuit size is polynomial in k and the description size of the supplied circuits, even when the true products are hard. Omitting the conjugations for general G would give an incorrect discrepancy word. [Lean check of the recurrence](../lean/PhaseProducts.lean)

To certify a proposed final group element e, append the single letter (A_root⁻¹e)⁻¹. The augmented word has product 1 exactly when T_root=e. To certify a final register value it suffices to supply such an e with the required action on the given initial register.

## Pairing inverses

A circuit π on word positions is required, on every nonidentity letter, to name a distinct position with the inverse letter and to satisfy π(π(i))=i. Ignore identity letters. Call i an opening when i<π(i). Two pairs cross when their openings and closings interleave in the order i<j<π(i)<π(j). If the opening letters commute on **every** crossing, the entire word multiplies to 1. Choose a pair having no whole pair strictly inside it. Every intervening active position crosses this pair, so its letter commutes with the chosen opening. Delete the opening and its inverse. Induction finishes, since deletion preserves the crossing pattern of the remaining pairs. The pairing and crossing conditions are universal predicates on at most two O(k)-bit positions. A single ordinary SAT query asks for any violation. If k=O(log T) and the combined schedule, summaries and pairing circuits have S gates, the violation circuit has size S·poly(k+1) up to ordinary encoding factors: it uses constantly many evaluations of π and at most O(k+1) summary evaluations per requested letter. Under cubic SAT, guessing the descriptions and testing all violations gives a nondeterministic verifier of time Õ(S³ poly(k+1)) plus uniform setup. This price is independent of the number of local defects.

A sharper calculation holds when all commutators of G are central. With [a,b]=aba⁻¹b⁻¹, the product of the paired word is exactly

    ∏_{i<j<π(i)<π(j)} [gᵢ,gⱼ],                           i,j openings.

Take the leftmost active opening a and write the remaining word as V a⁻¹ W after it. Its removal contributes [a,V]. Centrality makes this the product of [a,v] over letters of V. Pairs entirely in V cancel in this product, and all other letters there are openings crossing the chosen pair. Iterate on the shortened word. The resulting central factors commute, so their ordering is immaterial. One can certify a proposed central product by a second succinct inverse pairing on the nonidentity crossing contributions augmented by the inverse of that proposal. Each crossing label and each second-level partner uses only O(k) index bits. This is a sufficient certificate and need not exist in short form.

Centrality alone does not compute the remaining product. In the order-eight dihedral group take rotation r and reflection s, so [r,s]=r² has order two. For an arbitrary Boolean circuit h, output r,s,r⁻¹,s⁻¹ in block t if h(t)=1 and four identities otherwise. Pair within each active block in crossing order. The product is (r²) raised to the number of satisfying inputs of h. Verifying just the inverse pairs in this explicit example leaves exactly the parity-of-count question.

## A cheap endpoint with a PSPACE-hard midpoint

Take the polynomially described sequence x of five-state permutations from the quantified-formula construction in the preceding note. Its product on a designated start decides that formula. Replace each instruction g by a,a⁻¹,g,1 for one fixed nonidentity permutation a. The resulting sequence u has the same product and at least half its letters are nonidentity. Use the full schedule u followed by u⁻¹, reversing the letters and inverting each. The total length is a power of two and its succinct circuit grows by only the cost of address manipulation and constant-group operations. [Width-five construction and primary sources](phase-products.md)

Set every Aᵥ to the identity. All internal discrepancy letters are identity. Pair each active leaf at phase j with the leaf at phase 2|u|−1−j. Preorder preserves the left-to-right order of leaves, so every pair is nested or disjoint. This provides a polynomial-size certificate of the final identity although at least half the leaves are defects. Recovering the actual midpoint for this family, even just its action on the designated start, would decide the PSPACE-complete quantified-formula problem. The example shows why certifying one endpoint can be easier than constructing accurate summaries for every interval. Its terminal answer is known for every instance and supplies no hard decision to encode as SAT. A transfer to the target still requires a short pairing certificate for the *appropriate claimed output* of a genuine hierarchy computation. No novelty claim is made for the group identities.
