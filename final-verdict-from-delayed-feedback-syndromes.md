# How much of a feedback residual must a linear checksum retain to certify the verdict?

For the fixed [single-delay forecast](one-variable-delay-and-one-binary-product.md), even checking just the requested final bit can require $\Omega(W^4)$ independent binary linear checks of the recurrence errors. This is a restriction on one proposed verification method for short SAT certificates. It holds on a prefix where the correct final bit is always one.

For any proposed binary history $v_0,\ldots,v_T$ with the specified initial seeds, form its residual
$$
 r_t=v_t+\left(\bigoplus_{a\in L(W)}v_{t-a}\right)
             \left(\bigoplus_{b\in R}v_{t-b}\right).
$$
For fixed $W$ the residuals freely parametrize all histories. Given $r$, compute each $v_t$ from earlier positions and $r_t$; this is a triangular bijection. To certify the *whole* history by requiring binary linear measurements of $r$ to vanish therefore takes $T+1$ bits. The final bit poses a different question since an erroneous history can give the right verdict.

## Injecting independent products into the actual returned bit

Include a calibration mode in the fixed simulated tape controller. After the usual measurement and header decoding, return to cell 1. Set its verdict track $q=1$ and two ordinary data tracks $a=b=0$. Thereafter the head stays at that cell, applying the transition
$$
                 (q,a,b)\longmapsto(q+ab,0,0).
$$
All other cells preserve their symbols. These are fixed finite-alphabet transitions. The mode is entered well before row $H=W^4$ on every sufficiently large width with its fixed prefix.

In the scalar compiler use a dedicated output slot for the FIFO bit; it feeds the one long tap, and any other uses of the computed value within the same finite controller use the wire upstream of that slot. Thus flipping the physical output at one bit position alters exactly the corresponding bit returned by the FIFO later. This is a choice of ordinary fixed gate layout. An additive residual placed at the slot changes the emitted bit. All subsequent gates obey the original recurrence unless their own residual is specified. The slot-isolation argument remains valid by induction, since these injected ones arrive only at legal slot residues.

Choose $m=\Theta(W^4)$ consecutive home-cell emissions in calibration rows before the final transition. In row $i$ put residual $x_i$ at the output lane spelling $a$ and $y_i$ at the lane spelling $b$, and zero on all other ticks. Write the tape alphabet in data tracks so changing either lane preserves the head state and the other tracks; its timeout/acceptance rule on these symbols is exactly the displayed map. These are $2m$ distinct physical coordinates of the residual vector. The serial FIFO and one-wall simulation now reproduce the proposed rows with those two bits changed at emission. The next update reads them at the same cell, accumulates their product and clears them. Neighboring cells are unchanged by the stationary head. Induction gives
$$
          v_T = 1 + \sum_{i=1}^m x_i y_i .
$$
There are no choices of faulty transitions hidden elsewhere in the stated residual support. The genuine trajectory has $r=0$.

## A sharp count on the indistinguishable faults

Suppose the all-zero replies to $s\le m$ binary linear queries of $r$ are used to certify the final verdict. The checks may depend on $W$; even for adaptive choices their all-zero branch is fixed. On the displayed $2m$ coordinates those replies leave a subspace $K$ of codimension $h\le s$. Put $Q(x,y)=x\cdot y$. Its polar form $B((x,y),(x',y'))=x\cdot y'+x'\cdot y$ is nondegenerate. The radical of $B$ restricted to $K$ has dimension at most $h$, since it is contained in the ambient orthogonal complement of $K$. Squaring the bias and substituting a uniform difference $z$ gives
$$
  \left|\mathbb E_{u\in K}(-1)^{Q(u)}\right|^2
  =\mathbb E_{z\in K}(-1)^{Q(z)}
                    \mathbb E_{u\in K}(-1)^{B(u,z)}
  \le \frac{|\operatorname{rad}(B|_K)|}{|K|}
  \le 2^{2h-2m}.
$$
Consequently at least $(1-2^{s-m})/2$ of these undetected faults change the final answer. For $s<m$ there is always a wrong-verdict trajectory with all the same syndrome replies as the genuine history. The fraction bound is attained by the checks $x_1=\cdots=x_s=0$. At $s=m$ such checks suffice on this particular fault subspace. There is a separate exact bound for adaptive linear measurements that must return the correct bit on *every* input to this fault subspace. For $m\ge1$ it is $m+1$. Read all $m$ bits of $x$ and use one linear query on $y$ with those coefficients. For the converse, a depth-$m$ linear decision tree partitions the $2m$ bits into affine leaves of relative sizes that are multiples of $2^{-m}$. But the fraction on which $Q=1$ is $(2^m-1)/2^{m+1}$, with odd numerator. No union of its leaves has that mass.

Characteristic-two extension-field evaluations of a residual polynomial also count by their total number of binary components.

## Allowing nonlinear checks and an existential certificate

Suppose a verifier accepts the genuine trace and forbids every wrong verdict on the displayed subspace. Along its genuine accepting transcript it reads $s$ binary measurements computed with arbitrary affine operations over $\mathbb F_2$ and $g$ binary AND gates altogether, counting shared gates once. The measurements may be adaptive and the verifier may use an existential certificate. All fault-dependent information available to the verifier, including information used to select later measurements, must come from the charged replies. It may freely use the fixed program, width and its certificate. Fix one certificate that succeeds on the genuine trace. Fix adaptive choices to those on its genuine path.

Start with the whole $2m$-bit fault space. In topological order at each AND, restrict one of its two currently affine inputs to its value at zero. This costs at most one linear equation through zero. The output then becomes affine on the smaller subspace. Finally pin the $s$ affine measurement values to their genuine replies. The resulting linear subspace of codimension at most $h=g+s$ follows the same accepting transcript with the same certificate. For $h<m$, the previous count gives a fraction at least $2^{-h-1}(1-2^{h-m})$ of **all** the faults which pass and reverse the verdict. This is a population bound, as additional accepted inputs may sit outside the flat. For $s\ge1$ and $h\le m$ it is sharp: split $h$ first-bank coordinates into $s$ nonempty groups and test the OR of each group. Pairwise OR costs one AND and affine operations, giving $h-s$ AND gates; the all-zero replies pin precisely those $h$ coordinates. In particular protecting the genuine transcript alone requires $s+g\ge m$, even with auxiliary certificates.

For a deterministic procedure required to *compute the verdict on all faults*, every AND along a path can instead be simulated by one adaptive linear query of an operand, after which its value is affine for the rest of that branch. Thus the worst-case budget satisfies $s+g\ge m+1$ by the leaf-count argument. For $1\le s\le m+1$ this is exact: read $s-1$ first-bank bits, spend $m-s+1$ AND gates on the remaining products, and ask one affine-combined output query. These counts charge access to residuals in this specified interface, with no restriction on the time taken to choose a certificate.

This excludes soundness arguments that deduce the verdict solely from vanishing linear checks of an otherwise arbitrary history. One quadratic check $x\cdot y=0$ already suffices on the displayed fault subspace. A verifier can also recognize the unperturbed calibration program and prove its steady verdict without certifying a submitted history. The unresolved SAT compiler has access to these alternatives. Lean proves the normalized linear-syndrome flip bound for every list of masks, including dependent ones. An exact finite audit tested 2,898 syndrome kernels and 64 complete scalar histories with injected errors. [Lean proof](FeedbackVerdictSyndrome.lean) · [Finite subspace and fault checks](feedback_verdict_syndrome_audit.py)
