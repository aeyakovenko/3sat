# Two fast scans with large communication costs on every balanced tree

There are proper SAT files with \(n=2^d\) data-bearing native words and encoded length \(N=\Theta(n\log n)\) bits with the following properties.

* A fixed, globally correct SAT program takes \(O(n)\) native steps on every member. It can evaluate all payloads by two ordered scans.
* Split the \(n\) items by **any** full binary tree that divides each node into two equal halves. At each split, fix the true data outside the node and let its children privately hold their respective items. The sum of the exact deterministic communication complexities of deciding SAT in these separate two-party experiments is \(\Theta(n\log^2 n)\) bits for every outside fixing from one file.
* There is also a common-input statement about protocol executions. Fix in advance one correct deterministic protocol for each pair of disjoint equal-sized children and each public outside setting. With probability \(1-o(1)\) on a uniformly chosen *rejecting* payload, **every** balanced tree incurs \(\Omega(n\log^2 n)\) communicated bits when those protocols are run on that payload. The tree may be chosen after seeing the file. The protocols may depend on the split and the outside data. Giving a protocol extra free information about the private child inputs, for example through the rest of a tree chosen using those inputs, changes the experiment.

Dividing by the native word width gives \(\Theta(n\log n)\) word equivalents for the optimal isolated protocols, a factor \(\Theta(\log n)\) above the total running time of an actual solver. The code-membership example in the earlier journal had an exact linear telescoping bound for the sum of the sibling problems. The present SAT verdict has large sibling costs on every balanced tree. Adding those costs still overestimates elapsed RAM time. [Earlier sibling-cut calculation](balanced-cuts-of-one-sat-run.md)

## Finding two orders

Put the natural order \(\pi_1\) and a second order \(\pi_2\) on the \(n\) labeled items. At a node with children \(A,B\), restrict an order to \(A\cup B\) and record whether each item lies in the left or right child. Let \(r_i(A,B)\) count transitions between consecutive unequal symbols in this string for order \(\pi_i\). There is a choice of \(\pi_2\) for which **every** balanced tree satisfies

\[
          \sum_{\mathrm{internal}\ v} \bigl(r_1(A_v,B_v)+r_2(A_v,B_v)\bigr)
          > nd/32
\]

for all sufficiently large \(d\). In fact a uniform \(\pi_2\) works with probability \(1-2^{-\Omega(nd)}\).

Use an abstract complete ordered tree of depth \(d\), initially leaving its leaves unnamed. At all its internal nodes store the two binary interleaving strings just defined. Their lengths are known and sum to \(2nd\). For each of the two orders, recursively merge the leaf lists according to its strings to obtain an ordering of the abstract leaves. Label the leaves in the first merged ordering with the numbers \(1,\ldots,n\). The second merged ordering now specifies \(\pi_2\). In particular **no description of the labeled tree is needed**. Even if it was chosen to minimize transitions for \(\pi_2\), these strings encode the permutation. The first bits of the strings cost at most \(2(n-1)\) bits. Their transition locations are a subset of at most \(2nd\) positions. The number of permutations admitting a total of at most \(nd/32\) transitions is bounded by

\[
       2^{2(n-1)}\sum_{j\le nd/32}\binom{2nd}{j}
       \le 2^{2(n-1)+2nd\,H_2(1/64)}.
\]

Here \(H_2\) is binary entropy, \(2H_2(1/64)<1/4\), and \(\log_2(n!)=nd-O(n)\). This is a probabilistic existence proof. The lexicographically first permutation passing the finite test gives a computable choice. The fast SAT algorithm below handles any supplied permutation. Recursive interleaving strings are classical wavelet-tree representations. Alternations of this kind have also been used to lower-bound access sequences on binary search trees, a model with different costs. [Grossi, Vitter and Xu on wavelet-tree bit arrays](https://www.ittc.ku.edu/~jsv/Papers/GVX11.WaveletTreeCCP.pdf) · [Wilber on alternation bounds](https://doi.org/10.1137/0218004)

## The verdict and the rank of one split

Each item \(i\) supplies four independent \(h\)-bit masks \(x_{i,1},y_{i,1},x_{i,2},y_{i,2}\), where \(h=\Theta(\log n)\). For each bit position, or lane, compute over \(\mathbb F_2\)

\[
                   Q=\sum_{j=1}^2\sum_{u\le_{\pi_j}v}x_{u,j}y_{v,j}.
\]

The verdict is SAT if at least one lane gives \(Q=1\). A RAM can compute all lanes in parallel. For each order maintain the word \(U\) of prefix XORs of its \(x\)'s and a word \(V\), initially zero. At an item set \(U\gets U\mathbin{\mathrm{XOR}}x\), then \(V\gets V\mathbin{\mathrm{XOR}}(U\mathbin{\mathrm{AND}}y)\). XOR the two final \(V\)'s and test for nonzero.

For one lane and one order, the binary coefficient matrix of terms crossing \(A,B\), with Alice's \(x,y\) variables as rows and Bob's as columns, has off-diagonal blocks \(U_{AB}, U_{BA}^{\mathsf T}\). Here \(U_{AB}(a,b)=[a<_{\pi}b]\). In the restricted order, each \(A\)-run gives one row type consisting of a suffix of the \(B\) positions. Each \(A\)-run except a trailing run has a nonzero such suffix. Distinct nonzero suffix vectors are linearly independent, by their distinct first nonzero positions. The analogous statement holds for the \(B\)-runs. Exactly one run trails, so the cross rank is exactly the number of transitions. The two orders use independent variable banks, and their ranks add. Thus the rank for the lane is exactly

\[
                           r=r_1(A,B)+r_2(A,B).
\]

Fixing the entire outside contributes only local functions and a constant. For Alice's lane variables \(a\) and Bob's \(b\), write the local verdict polynomial as \(g(a)+g'(b)+a^{\mathsf T}Mb\), with \(\operatorname{rank}_{\mathbb F_2}M=r\). Its sign matrix has real rank \(2^r\): after row and column sign changes the distinct rows are the orthogonal binary characters indexed by the row space of \(M\). Its zero-indicator matrix has rank at least \(2^r-1\) by subtracting the all-one matrix from twice the indicator. The UNSAT matrix on all lanes is the tensor product of the zero-indicator matrices. The deterministic log-rank bound therefore gives at least \(h\log_2(2^r-1)\ge h(r-1)\) bits for \(r\ge1\). Conversely a rank factorization allows Alice to send the \(r\) inner-product coordinates and one local bit per lane, after which Bob evaluates the verdict. Thus the cost is between \(h(r-1)\) and \(h(r+1)+1\) for \(r\ge1\), with the same upper bound at \(r=0\). Summing, the additive errors are \(O(hn)\). This proves the claimed worst-case sum independently of all outside values.

## One rejecting file for all splits

Take all payload bits independently fair. On the full file the polynomial of each lane is homogeneous bilinear between all \(x\)'s and all \(y\)'s. Conditional on all \(x\)'s its value is either zero or fair. Thus the probability of UNSAT on all \(h\) independent lanes is at least \(2^{-h}\).

For any one split and outside fixing, a rejecting transcript rectangle factors into a row set and a column set. Project each of these sets onto a single lane. The resulting Cartesian product consists entirely of zeros for that lane: choose any full row and any full column realizing the two projections and use that their combination belongs to the original rectangle. Let \(U,V\) be the spans of differences of projected rows and columns. Taking the XOR of the four polynomial values at any two rows and two columns gives \(U^{\mathsf T} M V=0\), by bilinearity. Consequently \(\operatorname{codim} U+\operatorname{codim} V\ge r\); indeed \(\dim M^{\mathsf T}U\ge r-\operatorname{codim}U\) and its image annihilates \(V\). Projected rows and columns each lie in one coset of their difference spans. The projected rectangle has density at most \(2^{-r}\). The full sets lie inside the products of their lane projections, so a full rejecting rectangle has density at most \(2^{-hr}\).

Any correct binary deterministic protocol has at most \(2^{hr/2}\) terminal transcripts of length less than \(hr/2\), by prefix-freeness. Use public terminal verdicts, adding one bit if necessary. For the fixed protocol the probability of a cheap rejection is at most \(2^{-hr/2}\) on uniform free inputs, independently of outside values. Average over the outside coordinates, then condition globally on UNSAT. The probability bound on that distribution is \(2^{h-hr/2}\).

Set \(\eta=1/32\) and choose \(h\ge512d\). For each split with \(|A|=|B|=t\ge256\) and \(r\ge\eta t\), this failure probability is at most \(2^{-h\eta t/4}\). There are at most \(n^{2t}\) such ordered splits. Summing over \(t\) gives \(o(1)\). On the complementary event every one of these isolated protocols uses at least \(hr/2\) bits on the same rejecting file. For every balanced tree the sum of its \(t\)'s equals \(nd/2\). Nodes with \(r<\eta t\) therefore contribute at most \(nd/64\) to its total rank; levels with \(t<256\) cost only \(O(n)\), since \(r\le4t\). The remaining nodes must supply \(\Omega(nd)\) rank. This proves the common-input communication claim, allowing the decomposition tree to depend on all the input bits.

## Ordinary SAT files and the native clock

Use a shared existential choice of lane. Let \(h_0\) be a power of two between \(d/16\) and \(d/8\) for sufficiently large \(d\), take \(g=8192\) groups, and set \(h=gh_0\). Public one-hot selectors for the group and offset specify one of the \(h\) lanes. For each \(h_0\)-bit mask \(\mu\), define a shared library wire \(S_\mu=\mu[\text{offset}]\) by one guarded bit constraint per offset. Give the library names a common nonzero decimal prefix followed by the actual \(h_0\) digits, each 0 or 1. On each item, each of its four private scalar wires \(Z\), and each group \(j\), write the two proper clauses

\[
       (\neg G_j\lor\neg Z\lor S_\mu),\qquad
       (\neg G_j\lor Z\lor\neg S_\mu).
\]

They impose \(Z=S_\mu\) in the active group. The digits of a logical mask bit appear twice, always in the same item word. Conditional communication is measured on the independently chosen logical masks, keeping the two physical copies together. The \(8g\) clauses form one aligned word by choosing a sufficiently large **fixed** word-width coefficient. Use separate designated scalar names for the four channels of each item.

Fixed clauses implement both scan recurrences on the selected lane with deterministic XOR and AND gate equivalents, and assert that the resulting bit is one. Decode the one-hot selectors with true roots and deterministic binary trees, pad short clauses with distinct false anchors fixed by seven proper triples, and pin the unused identifiers in the mask-name range to constants. For each chosen lane every declared variable then has a unique value before the output assertion, so the model count is the number of lanes giving one. The fixed scan circuit has \(O(n)\) Boolean gates, even though the two raw scans evaluate \(h\) lanes at once. A public DIMACS comment list gives \(\pi_2\) in fixed-width fields, and the fixed scan clauses use that same permutation. For the lower bound all these positions are held fixed. The additional decoder and filler sizes are \(O(g+h_0 2^{h_0}+10^{h_0})\) clauses. All fields have \(O(\log n)\) bits. Use a public power-of-two total bit length \(N=\Theta(n\log n)\) with fixed whitespace padding and aligned words of \(8\lceil C\log_2(N+2)\rceil\) bits. Choose \(C\) and then the fixed multiplicative padding constant large enough for one entire item word and all remaining records. [Earlier shared offset mask construction](three-lookups-and-the-multilinear-sat-verdict.md)

For a global SAT algorithm the validation cost matters. Use blank-padded fields with a constant number of fixed field positions per clause, so every formatted clause fits a constant number of native words. Read dimension and layout parameters from a bounded public comment and check them against the input length before indexing. Tabulate the packed, canonically padded decimal spellings of the \(O(n)\) identifier numbers and ordinal labels. Increment the decimal digit string in one pass through the numbers, updating its packed word at the changed digit positions. The total number of digit changes is \(O(n)\) by summing the carries over powers of ten. Store a reverse dictionary for the permutation's packed labels by direct addressing with zero default. Each label uses \(O(\log n)\) bits within the chosen word width, leaving room for a fixed tag and the other work banks. Range and canonical-format checks precede lookup on arbitrary files. Directly listing all possible small masks, their compact binary words, and all fixed auxiliary clauses outside the scans costs \(O((h_0 2^{h_0}+10^{h_0}+g)\operatorname{polylog} n)=o(n)\).

Check the public permutation is a bijection with a seen array, and generate and compare the fixed scan clauses for that order via the table of packed spellings. Check every item word's IDs, fixed punctuation, duplicate mask names, and all padding. Use the mask dictionary to assemble its four \(h\)-bit payloads, in a constant number of operations per group and \(O(1)\) groups. Validate the header and exact end of file; the trailing fixed bytes can be compared a packed word at a time. This costs \(O(n)\) steps. Store the payload words and do the two scans. If validation fails, use a complete SAT procedure. This yields a single \(O(n)\)-step solver on these files, including when the chosen second order was found by an expensive finite search. A file requiring \(\Omega(n)\) steps also exists: on the all-zero file the \(n\) disjoint edits setting \(x_{i,1}=y_{i,1}=1\) in a common lane, one item at a time, are each satisfiable. Every correct solver must load every item word there.

Hence the worst-case native time on this promise is exactly \(\Theta(n)=\Theta(N/\log N)\) for the best globally correct solver. The sum of the isolated communication lower bounds, after division by word width, is \(\Theta(n\log n)=\Theta(N)\). Even a common rejecting file and an input-dependent choice of balanced tree do not supply a disjoint assignment of these communication costs to that file's native steps. The two scans reuse the same prefix state across many of the proposed local experiments. Priority for the combination on proper SAT files is unestablished. Lean checks the scalar scan recurrence and the four-corner cancellation with arbitrary one-party functions. The permutation counting, probability, encoding and native clock are manuscript proofs. The finite audit checked 131,072 packed scans and 240 proper-DIMACS lane choices. [Lean scan and four-corner identities](../lean/PrefixScanCorners.lean) · [Exhaustive small-case and packed-verdict audit](../audits/all_tree_prefix_scans_audit.py)
