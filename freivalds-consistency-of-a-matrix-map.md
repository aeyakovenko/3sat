# Agreement along individual directions forces affine matrix multiplication

Let V be the d-dimensional binary vector space. A function g from d by d matrices to d by d matrices supplies one whole output matrix per input. Test it by choosing a uniform nonzero v, uniform B, and then independent uniform B′ subject to B′v=Bv. Reject if g(B)v≠g(B′)v. Thus input pairs are allowed to disagree on a subspace of dimension d−1. Write ε for the probability of rejection.

**Rigidity.** If d≥3 and ε≤1/100, some fixed binary matrices C,L satisfy

$$
\Pr_B[g(B)\ne C+LB]
\le (2-2^{1-d})\left(\varepsilon+
              \frac{3\varepsilon}{1-17\varepsilon}\right)<10\varepsilon
$$

when ε>0, and zero rejection gives equality on every B. The linear dependence on ε is optimal up to a constant. The theorem compares *entire matrices* on its left.

## From directions to a partial additivity test

For v≠0 and arbitrary x, let F(v,x) be a most frequent value of g(B)v over Bv=x, with fixed tie-breaking. If the probabilities on one fiber are p_j, then 1−max p_j≤1−Σp_j². Consequently the average disagreement of F(v,Bv) with g(B)v is at most ε. For distinct nonzero v,w and uniform B, the pair (Bv,Bw) is uniform on V². The same matrix g(B) is linear in its queried direction. Applying the three agreement estimates to v,w,v+w gives

$$
\Pr[F(v,x)+F(w,y)\ne F(v+w,x+y)]\le3\varepsilon,
$$

where v,w form a uniform ordered pair of distinct nonzero directions, and x,y are independent and uniform. We need a correction on the *punctured* domain S={(v,x):v≠0}. Charging all the missing directions as errors would leave an additive term even for a perfect test.

## Correcting the punctured domain

Write h=(w,y) in V² and let S_h={p:p,p+h∈S}. For p∈S_h define D_h(p)=F(p)+F(p+h). For two random p,q∈S_h conditioned on distinct first coordinates, each of (p,q) and (p+h,q+h) is a uniform distinct-direction pair further conditioned to avoid at most one of the 2^d−1 nonzero directions. The latter condition has probability at least (2^d−3)/(2^d−1)≥5/7. Except on probability ≤(42/5)ε, both additivity tests succeed with the same sum p+q. Hence D_h(p)=D_h(q).

For p,q conditioned on equal first coordinates, sample r in S_h with first coordinate different from theirs, uniformly among the options. Both (p,r) and (r,q) individually have the distinct-coordinate distribution. The disagreement in this case is at most (84/5)ε. Removing the conditioning shows that independent D_h samples disagree with probability ≤17ε, uniformly for *each* h. Their most frequent value H(h) therefore agrees with D_h(p) with probability ≥1−17ε.

For arbitrary h,h′ choose p with p,p+h,p+h+h′ all in S. The first coordinate avoids at most three of the 2^d choices, so this extra restriction has conditional probability at least 5/8 under each of the three corresponding uniform derivative samplings. With total failure probability ≤3·(8/5)·17ε<1, the three derivatives at p, p+h and p give H(h), H(h′), H(h+h′), respectively. Adding the first two derivatives gives the third, so H is additive on all of V². It has the form H(v,x)=Cv+Lx.

For uniform h∈S and uniform p∈S_h the two first coordinates are nonzero and distinct. The additivity test shows F(h)≠D_h(p) with probability ≤3ε. Wherever F(h)≠H(h), that probability conditional on h is at least 1−17ε. This bounds the disagreement between F and H on S by 3ε/(1−17ε). Together with the fiber plurality bound, it bounds Pr[g(B)v≠(C+LB)v] by ε+3ε/(1−17ε). A nonzero linear operator moves at least 2^{d−1} of the 2^d−1 nonzero directions. Averaging over B yields the claimed whole-matrix bound.

## Sharpness in order and relation to checking programs

Distinct maps B↦C+LB disagree on at least half the inputs. If the difference of the L's is nonzero, already its action on one uniform column has point probabilities at most 1/2. If only the constants differ, the distance is one. Change a structured map by adding a fixed nonzero matrix on a δ fraction of inputs, 0<δ<1/4. Its distance to this class is exactly δ. The test rejects only if at least one sampled matrix lies in the changed set, so ε≤2δ. In particular a uniform o(ε) conclusion is impossible.

The correction uses the linearity tester of Blum, Luby and Rubinfeld. Their procedure tests additivity and studies self-checking matrix multiplication. The test here only compares outputs on one common input direction, permits an arbitrary offset C, and supplies all other entries of B and B′ independently subject to that common direction. The punctured-domain calculation removes loss from the zero first coordinate. I have not established priority for this agreement theorem or optimized the constant. [Blum, Luby and Rubinfeld](https://people.csail.mit.edu/ronitt/papers/selftestcorrect.pdf) · [Rubinfeld on robust functional equations](https://ecommons.cornell.edu/entities/publication/75a2196c-403c-47b0-a847-2d79deb5ab17).

There is also a geometric description. Each B is the graph subspace {(v,Bv)} of V² and g(B) supplies a linear map on that graph. The test compares two random graphs through a common point. This is related to subspace-versus-subspace and subspace-versus-point agreement testing. Grassmann tests also study much lower agreement and other intersection distributions. [Grassmann agreement tests](https://theoryofcomputing.org/articles/v021a011/v021a011.pdf) · [Subspace-versus-subspace linearity tests](https://theoryofcomputing.org/articles/v021a010/v021a010.pdf).

## Effect on a SAT reduction

Fixing a left input A, g(B)=AB passes exactly. More generally even a perfect pass only identifies C+LB. Values g(0)=0 and g(I)=A identify the intended product in the exact case. In the noisy case prescribed values at just two points cannot do so, since two tampered matrices cost at most 4/2^{d²} in rejection probability. A Boolean verifier of a supplied C can check whether C=AB, and a rank-one challenge can be answered by computing A(Bv), without producing any g(B). To turn the rigidity statement into a fast multiplication algorithm one would need an efficient whole-matrix producer or a sufficiently shared algebraic representation for its directional responses. The SAT-to-verification reduction supplies neither construction. [SAT-to-verification reduction](verifying-matrix-products-from-sat.md) · [Cost of shared rank-one responses](rank-one-challenges-for-a-single-matrix-product.md).

**Formal and finite checks.** With zero rejection, testing each coordinate direction gives column functions f_i(x) for each output bit. Testing e_i+e_j on inputs with columns (x,y) and (x+y,0) gives f_i(x)+f_j(y)=f_i(x+y)+f_j(0). Lean proves from all these pair identities that f_i(x)=f_i(0)+ℓ(x) for one common additive ℓ, for any dimension with two distinct coordinates. Applying the theorem to each output bit gives C and L. The numerical audit independently solves all zero-error testing equations for d=2,3 and checks corruption examples. The robust estimate is a written proof. [Exact additive extraction in Lean](IndividualDirectionRigidity.lean) · [Finite audit](freivalds_consistency_audit.py).
