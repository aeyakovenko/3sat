# A shared dividend across every quotient and remainder address

For a bank of independent bits \(X_0,\ldots,X_{v-1}\), let \(v=2^k\) and let one unknown \(k\)-bit scalar \(s\) be the **dividend** at every positive lane. All \(X_{\lfloor s/i\rfloor}\) have a deterministic bounded-fanin Boolean circuit of size **\(\Theta(v)\)**. All \(X_{s\bmod i}\) have size \(O(v\log(k+2)+C_{\rm shift}(v))\), where \(C_{\rm shift}(v)\) computes one unknown cyclic subtraction shift of a bank. The reverse remainder itself contains a cyclic subtraction shift on \(v/4\) independent positions by a projection. Using the November formal convolution upper bound therefore gives \(O_\epsilon(vk^{1/2+\epsilon})\) deterministic gates for the reverse remainder. [Formal convolution theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-logarithmic-exponent-of-finite-Fourier-transforms-November-24-2026/build/intro.tex) · [Arithmetic bank transformations](affine-and-arithmetic-subscripts-in-a-packed-bank.md)

For **locally indexed ordinary proper DIMACS**, the quotient relation takes \(O(v(k+1))\) encoded bits with \(O(v)\) packed printing work. For each fixed \(0<\epsilon<1/2\), the remainder relation has a construction with
\[
 O_\epsilon\!\left(\frac{v k^2}{(\log\log k)^{1/2-\epsilon}}\right)
\]
bits at all sufficiently large \(k\). A native RAM prints it in the displayed size divided by \(k\), plus \(\operatorname{poly}(k)\) steps. In both cases the individual raw bit indexer takes \(\operatorname{poly}(k)\) time and has degree \(O(\log(k+2))\) on each of \(\operatorname{poly}(k)\) public consecutive address intervals. The remainder's stronger deterministic gate count above does not presume local constructibility of the upstream full-length multiplication circuit. We use just its size by exhausting much smaller kernels in the local construction. These are encodings of the stated shared-dividend relations.

Choose the ISA's convention at divisor zero separately throughout. If the numerical answer there is zero, connect \(Y_0=X_0\). A saturating quotient uses \(X_{v-1}\); returning the dividend as the remainder uses \(X_s\), one further lookup. Any fixed default address with a poly\((k)\)-size uniform scalar circuit can be included in the sparse batch. A trapping convention can instead disable the zero lane or connect its dedicated trap bit, according to the declared relation.

## The quotient circuit and its physical verifier

For large \(k\) choose a dyadic \(K\) between \((k+1)^4\) and \(2(k+1)^4\), and put \(m=v/K\). Finite smaller widths can use a direct lookup. Compute \(s\div i\) on the \(1\le i<m\) lanes by binary restoring division, with \(O(k^2)\) gates per lane. A simultaneous lookup of \(m\) arbitrary requested bits of \(X\) costs \(O(v+m k^3)=O(v)\) deterministic gates by Holmgren and Rothblum. For physical verification one instead uses the sparse read certificate with \(O(v+mk^2)\) gates and the local addressing described there. All arithmetic in a small-lane record can use that lane's public binary divisor bits as constant pins. [Holmgren and Rothblum, *Linear-Size Boolean Circuits for Multiselection*](https://doi.org/10.4230/LIPIcs.CCC.2024.11) · [Physical sparse reader](sparse-batch-lookup-with-position-certificates.md)

Put \(e_q=\lfloor s/q\rfloor\) for \(1\le q<K\). These \(\operatorname{poly}(k)\) scalar divisions have polynomial total cost. At every \(i\ge m\), \(\lfloor s/i\rfloor<K\), and
\[
 X_{\lfloor s/i\rfloor}
 =X_0\mathbin\oplus\bigoplus_{q=1}^{K-1}(X_q\oplus X_{q-1})[i\le e_q].
\]
Indeed \(i\le e_q\) is equivalent to \(q\le\lfloor s/i\rfloor\), and the consecutive differences telescope. Scatter the weights \(X_q\oplus X_{q-1}\) by XOR to their endpoints \(e_q\), including collisions, then take all suffix XORs of the resulting length-\(v\) bit vector.

For deterministic size the weighted scatter is the transpose of sparse multiselection with the addresses held fixed. This uses the actual construction of Holmgren and Rothblum, not a formal differentiation claim about arbitrary Boolean circuits. Their controls and paths in §5.2 depend only on the indices. The ordering, deduplication, valid-record flags and joins in §6.2 can sort entirely by address and request tags; identical addresses already carry identical data. Keep a separate validity bit for the missing symbol. The selectors in §7 then only multiplex payload bits according to address-derived controls. Replace a controlled two-input selector by its binary-field linear formula with those fixed controls, and run its adjoint routing from outputs to inputs, XORing incoming contributions at a fanout. This costs a constant factor in the number of wires and keeps the control computation. The resulting scatter takes \(O(v+Kk^3)=O(v)\) gates. Lane one of the requested function is \(X_s\), which depends on all \(v\) independent table wires. The fanin-two cone of one output depending on \(v\) source wires already contains at least \(v-1\) gates.

For the local existential verifier, merge the \(\operatorname{poly}(k)\) events at the same endpoint, retaining exactly one representative when the merged parity is one. Pairwise equality and direct XOR accumulation on this small list suffice. Guess a dense binary scatter vector. Check all retained positions read one by a sparse gather, and require that its population count equals the number of retained positions. This forces the entire claimed vector. A balanced binary tree sums \(v\) bits with \(O(v)\) gates: a height-\(h\) node adds \(O(h)\)-bit numbers while there are \(O(v/2^h)\) such nodes. Dense suffix XOR costs \(O(v)\). These layer and adjacency references have affine coordinates after partitioning by trailing carry positions in the ordinary way. The method covers the case where all event weights cancel.

## The direct remainder circuit

Use the same sparse reader for \(i<m\), now supplying \(s\bmod i\). Decode a unary threshold table \(B_t=[t\le s]\) on \(0\le t<v\) in \(O(v)\) gates (binary one-hot decoding followed by suffix OR), and set \(B_t=0\) for \(t\ge v\). Compute \(Z_t=X_{(s-t)\bmod v}\) once. In each dyadic band \(I\le i<2I\) with \(I\ge m\), try the public candidate quotients \(0\le q<v/I\). Exactly one satisfies \(B_{qi}\land\neg B_{(q+1)i}\), and for that candidate \(Z_{qi\bmod v}=X_{s\bmod i}\). There are exactly \(v\) tests per band and \(\log_2 K=O(\log k)\) bands. This proves the claimed gate count. Indexing a public wire by \(qi\) is easy arithmetically; its high binary digits can involve long carries. The low-degree physical construction below uses a different layout.

Conversely let \(L=2^b\), use \(v=4L\), and set \(s=3L+h\), \(i=2L+j\), with \(0\le h,j<L\). Then \(i\le s<2i\) and \(s\bmod i=L+h-j\). Set the low two bank blocks to copies of an arbitrary \(L\)-bit table \(A\). These lanes return \(A_{(h-j)\bmod L}\) at every \(j\). Only copies, fixed scalar prefixes and output selections are used.

## Checking the shorter interval for each quotient

Take any \(1\le q<K\). Use \(r_q=s\bmod q\) and enumerate offset \(j=e_q-i\) from the upper endpoint. The valid large lanes of quotient \(q\) have
\[
   0\le j<g_q=\max(0,e_q-\max(m-1,e_{q+1})),\qquad
   Y_{e_q-j}=X_{qj+r_q}.
\]
Here \(e_K\) is also computed. The number of offsets is at most \(1+\lfloor(v-1)/(q(q+1))\rfloor\), since the difference of the two real quotients is \(s/(q(q+1))\). Round this bound up to a power of two \(M_q\). Then
\[
 \sum_{q<K}M_q=O(v+K),\qquad
 \sum_{q<K}qM_q=O(v\log(K+1)+K^2).
\]
These two budgets pay for different types of work. Generate all flags \([j<g_q]\) by a small interval decoder with \(O(M_q+k)\) gates. Quotient zero at a positive large lane means \(i>s\), so those lanes simply require \(Y_i=X_s\).

For fixed \(q\) write \(M=M_q\), \(e_q=HM+a\). Select from \(Y\) the two adjacent \(M\)-bit blocks numbered \(H-1,H\), with zero padding outside the bank. There are \(O(1+v/(qM))\) candidate blocks, so this wide selection costs \(O(M+v/q)\) gates: decode \(H\) once and use its control on every bit of each candidate block. A cyclic subtraction shift on the resulting \(2M\) bits returns \(Y_{e_q-j}\) at every valid \(j<M\) with scalar \(M+a\). The expensive shift therefore acts on only \(O(v)\) bits across all windows. Padding before address zero is never selected on a valid offset.

For the right side put \(B\) equal to the least power of two at least \(q\), so \(B<2q\). Divide the relevant prefix of \(X\) into ordinary aligned blocks of \(B\) bits. The positions congruent to \(r_q\) modulo \(q\) in block \(p\) have offsets
\[
       u_p=(r_q-Bp)\bmod q,\qquad u_p+q\quad\hbox{if }u_p+q<B.
\]
Read these **two bits** by local selectors. The second can be zero when absent. Generate all the public residues \(p\bmod q\) in a binary tree, using the edge update \(a\mapsto(2a+c)\bmod q\) for the next public binary digit \(c\). Thus no raw wire identifier must compute the residue of all its high lane bits. Each block costs \(O(B+(\log(q+2))^{O(1)})\) gates, including small arithmetic, and there are \(O(M+q)\) blocks; padding by \(O(q)\) per \(q\) costs altogether \(\operatorname{poly}(k)\). For large \(k\) all \(q<K=\operatorname{poly}(k)\) satisfy \(M\ge B\).

Write \(j=Bh+d\). Set \(e,u\) to the quotient and remainder upon dividing \(qd+r_q\) by \(B\). Then \(e<q\), the desired block is \(p=qh+e\), and the desired member of its pair is the second exactly when \(u\ge q\). Precompute these small controls for each \(d<B\). After making the two one-bit block tables addressable as \((h,e)\), one \(q\)-way selector per offset suffices. This last cost is \(O(qM)\). The complication in ordinary binary file addresses is forming \(qh+e\); only a pair of **single-bit** tables now has to undergo this reindexing.

## Changing radix while controlling each printed bit

Fix a digit size \(b\ge1\). To reblock a contiguous binary array at \(p=qh+e\), round the number of values of \(h\) to a power of two (it is \(M/B\) for large \(k\)). Keep a digit in \([q]\), padded to the dyadic range \([B]\) when naming lanes. Move it past successive groups of at most \(b\) bits of \(h\), starting at the low end. For a group of radix \(D=2^a\), \(a\le b\), the local rule is
\[
 (d,e)\longmapsto(e',d')=
 \left(\left\lfloor\frac{qd+e}{D}\right\rfloor,
                    (qd+e)\bmod D\right).
\]
It is a bijection from \([D]\times[q]\) to \([q]\times[D]\). It preserves the integer represented by the mixed digits, and leaves every other coordinate unchanged. At the end the ordinary binary index is the concatenation of the remaining digit and the collected low bits. Use copy relations between stages; padding lanes need no asserted data. There are \(O(M)\) gates per stage, not \(O(qM)\): the mixed digit occupies the space of the original \(q\) source blocks per \(h\). The number of stages is \(O(1+k/b)\). In each public slab any reference bit from the local rule is a function of at most \(b+\lceil\log_2(q+1)\rceil\) variable lane bits.

The unknown subtraction shift on each \(2M\)-window uses the same digit size. To add one unknown digit times \(2^a\), hold the lower \(a\) bits fixed. On every group with high part \(H\), concatenate the current and next digit blocks; shift this two-block array by the digit and take its first block. At the cyclic top wrap the next group. Negative reflection of a public lane gives subtraction, or use the two preceding blocks and a reversed low lane. Nondata control digits are shared. A binary polynomial product modulo \(z^{2^t}-1\) with the one-hot vector of a \(t\)-bit scalar implements a cyclic shift. The upstream convolution bound yields a Boolean circuit of size \(O_\epsilon(2^t(1+t)^\alpha)\), \(\alpha=1/2+\epsilon<1\), also accounting for the one-hot decoder. Repeating the small \(t\le b+1\) kernels across the digit positions costs \(O_\epsilon(M(1+k/b^{1-\alpha}))\). This duplicated-block construction asks the kernel to handle only local digits. [Related local shift encoding](locally-encoding-an-unknown-xor-shift.md)

All together the remainder's verifying gate bound is
\[
  O_\epsilon\!\left(v\left(1+\log(k+2)+
                  k/b+k/b^{1-\alpha}\right) + \operatorname{poly}(k)\right).
\]
The term \(k/b\) for reblocking is paid on \(\sum M_q\). The larger \(\sum qM_q\) is paid only for local selectors and for the data spans in wide block selection. Applying a full-length multiplier separately to every candidate quotient would lose this distinction.

For the stated uniform physical compiler take \(b=\max(1,\lfloor\tfrac12\log_2\log_2(k+4)\rfloor)\). No uniform generation rate for the upstream fast circuit is required. For each \(t\le b+1\), exhaust binary circuits through the trivial \(O(2^t(1+t))\)-gate barrel-shift bound and compare their Boolean truth tables with the shift. The whole search takes \(2^{O(2^b(1+b)^2)}=k^{o(1)}\) time at large \(k\). Pick a shortest passing circuit, which inherits the upstream size estimate. If only nonuniform size and raw degree are wanted, the local argument also allows larger \(b\): with \(b=k^\delta\), \(0<\delta<1\), it gives gate exponent \(1-\delta(1-\alpha)<1\) and degree \(O(k^\delta+\log k)\) using a local kernel record. No polynomial-time raw bit index for these larger nonuniform kernels is asserted.

Use dyadic lane fields, fresh role tags and fixed-width decimal names with one digit per identifier bit, as in the sparse reader. Small arithmetic on \(q,d,r_q\) uses \(\operatorname{poly}(k)\) public gate roles. In the residue prefix tree predecessor addresses drop one bit. Initial and selected aligned blocks concatenate address fields. For adjacent high groups \(H+1\), fix the number of trailing ones of \(H\) and its next zero, with a separate wrap case. Numbering this slab by the other bits makes both addresses affine. For reflection use the corresponding least-set-bit partition. For the small uniform digit kernels there are only \(\operatorname{poly}(k)\) local gates and roles, or an entire kernel may be packed as one record template depending on \(O(b+\log k)\) low bits. The mixed-radix digit step's port function depends on \(O(b+\log k)\) lane bits; arbitrary functions on that many bits have extensions of at most that degree. Offset indicators within padded \(O(k+1)\)-byte clause records add \(O(\log k)\) degree. With aligned slabs in nonincreasing size order these statements hold on \(\operatorname{poly}(k)\) consecutive physical intervals. Distinct copy operands and fresh padding make every emitted clause proper. A shared name-to-ASCII chunk table and one word calculation per lane reference, or prefix traversal of a fixed coordinate permutation, emit the file in time proportional to its gate count plus polynomial setup. The size and addressing conventions count the actual text of the output, excluding any external pinning files.

The audit checks all linear inputs symbolically for 8,192 small configurations, all 87,380 tested cyclic-shift projections, and exact candidate counts at 44 dyadic cuts. Independent DPLL checks 216 pinned proper DIMACS files with correct outputs or a single bad quotient or remainder bit. A separate enumeration checks 264,196 live short-window sites in 4,096 cases and 56,700 mixed-radix normalizations. An additional 144 proper files check that short-window verifier directly on honest and one-bit-corrupted claims, using explicit finite digit kernels. Lean verifies the endpoint equivalence, unique quotient region, XOR telescope, unwrapped shift window, short-window remainder identity and mixed-radix swap. The upstream asymptotic convolution theorem was not reproved here. Priority for these shared-dividend conclusions is unestablished. [Executable audit](reverse_native_table_audit.py) · [Lean identities](ReverseNativeQuotient.lean)
