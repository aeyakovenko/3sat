# Every affine one-bit extension of the cyclic cover predicate

For a binary selector $x$ on a labeled cycle, let $f_n(x)=1$ when every edge has a selected endpoint. Equivalently, its cyclic bit string contains no adjacent zeros. Complementing each coordinate identifies its satisfying set with the independent sets of the cycle, the vertex set of the Lucas cube. Complementing the output gives the satisfiable-mask convention of the Gray-cycle SAT catalog. [Lucas cubes and their cardinalities](https://arxiv.org/abs/1407.4962) · [The original selector and XOR insertion](a-shared-nine-step-obstruction-and-the-next-native-width.md)

**Theorem.** For $n\ge5$, every affine map $g:\mathbb F_2^n\to\mathbb F_2^{n+1}$ satisfying $f_{n+1}(g(x))=f_n(x)$ on every input is obtained as follows. Choose one of the $n+1$ target sites to delete, identify the remaining cycle with the source by a rotation or reversal, and fill the deleted site with the XOR of its two neighbors. All $2n(n+1)$ labeled maps are distinct. Injectivity need not be assumed.

XOR insertion works because a subdivided edge with endpoint bits $u,v$ has its new bit $u\oplus v$. Both new edges are covered exactly when the old edge was covered. Its image is the even-parity hyperplane on three cyclic consecutive coordinates. The theorem proves the converse, allowing an initially arbitrary binary matrix and translation.

## Which hyperplanes contain the right number of covers?

Write $F_0=0,F_1=1$ and $L_0=2,L_1=1$ for the Fibonacci and Lucas sequences, each with the usual additive recurrence. There are $L_m$ covers at target length $m$. For a mask $S$, define the unnormalized Walsh coefficient
$$
\widehat f_m(S)=\sum_{x:f_m(x)=1}(-1)^{S\cdot x}.
$$
A hyperplane $S\cdot x=b$ contains $[L_m+(-1)^b\widehat f_m(S)]/2$ covers. Thus its intersection can be the affine image of the preceding cover set only if $|\widehat f_m(S)|=2L_{m-1}-L_m=L_{m-3}$. Injectivity is established below.

The change to independent-set indicators multiplies the coefficient by $(-1)^{|S|}$. The remaining signed sum is over independent sets, with a factor $-1$ for each occupied marked site. It is the trace of the cyclic product with an $A$ for an unmarked site and $B$ for a marked site, where
$$
 A=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
 B=\begin{pmatrix}1&-1\\1&0\end{pmatrix}.
$$
In the trace expansion the two states record occupation. A transition into an occupied state multiplies by the site's sign, and two successive occupied states have weight zero. In particular $\operatorname{tr}(A^m)=L_m$.

Here is a classification of the coefficients of the required magnitude for $m\ge9$.

* Three consecutive marks give $B^3=-I$. Delete these factors. The absolute trace of the remaining cycle is at most $L_{m-3}$ by the independent-set sum. If any mark remains, the empty set and the singleton containing it have opposite signs, giving strict inequality. A single triple attains equality.
* Suppose all marked runs have lengths one or two. For each run consume the next $A$ in cyclic order. A singleton $BA$ becomes $C=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$, while $B^2A$ becomes $D=\operatorname{diag}(-1,1)$. With $r$ single and $s$ double runs this leaves $t=m-r-3s$ factors $A,C$, together with orthogonal $D$ factors. The norm of each $A,C$ is $\phi=(1+\sqrt5)/2$. The product has determinant $\pm1$, so its singular values are $\sigma,1/\sigma$ with $1\le\sigma\le\phi^t$. Its absolute trace is at most $\phi^t+\phi^{-t}$. When $r+3s\ge4$, this is strictly below $L_{m-3}$: the expression increases for $t\ge0$, and $\phi^{m-4}+\phi^{-(m-4)}<\phi^{m-3}-\phi^{-(m-3)}\le L_{m-3}$ here.
* One double run by itself gives $|\operatorname{tr}(DA^{m-3})|=F_{m-3}$. If there are exactly three single runs, $t=m-3$ and both $A$ and $C$ occur. Rotate the product to exhibit an $AC$ boundary. Their top singular lines differ, giving $\|AC\|<\phi^2$ (in fact $\|AC\|=1+\sqrt2$). Thus the positive spectral radius $\lambda$ is strictly below $\phi^t$. The reduced matrix is nonnegative and unimodular; its other eigenvalue is $(-1)^t/\lambda$, with $\lambda\ge1$. Its trace is strictly less than $\phi^t+(-1)^t\phi^{-t}=L_t$.
* For two nonadjacent marks, let $u,v\ge1$ count the unmarked sites in the two gaps, with $u+v=m-2$. Exactly $F_{m-1}$ independent sets contain a given marked vertex, and exactly $F_uF_v$ contain both, by the independent-set counts on the remaining paths. Inclusion-exclusion gives signed sum $L_m-4F_{m-1}+4F_uF_v=-F_{m-3}+4F_uF_v$. This exceeds $-L_{m-3}$. Equality to $+L_{m-3}$ requires $2F_uF_v=F_{u+v}$, equivalently
  $$
  \frac{F_{u-1}}{F_u}+\frac{F_{v-1}}{F_v}=1.
  $$
  These ratios are $0,1,1/2$ at lengths $1,2,3$ and strictly between $1/2$ and $1$ at every larger length. Only $(1,2),(2,1),(3,3)$ solve the equation, giving target length $5$ or $8$.
* A single mark has absolute coefficient $L_m-2F_{m-1}=F_m>L_{m-3}$. An empty mask has coefficient $L_m$.

Consequently every eligible normal for $m\ge9$ is a cyclic triple. Its bias is zero in selector coordinates, since the explicit XOR image realizes the required count and the coefficient is nonzero.

## Affine symmetries of the source

At every length $k\ge5$ the singleton masks uniquely maximize $|\widehat f_k(S)|$ among nonempty masks, with maximum $F_k$. Indeed a triple costs three sites and gives at most $L_{k-3}<F_k$. Every other mask of weight at least two has $r+3s\ge2$ in the run calculation above and hence absolute coefficient at most $\phi^{k-2}+\phi^{-(k-2)}<L_{k-2}+1$. That coefficient is integral, and $F_k-L_{k-2}=F_{k-4}>0$.

A period must annihilate every nonzero Fourier frequency. All singleton coefficients are nonzero, so the cover indicator has only the zero period. The kernel of the linear part of any verdict-preserving map consists of periods of its source. Therefore the map is injective, with an affine hyperplane for its image. An affine automorphism of the source must permute the singleton frequencies under its dual linear map, hence it is a coordinate permutation followed by a translation. All singleton coefficients have the same nonzero sign. A translation changing any one of those signs is impossible. Finally, vectors with exactly two zeros test whether their positions are adjacent, so the coordinate permutation preserves the cycle and is dihedral.

## The three smaller target lengths

The direct Walsh counts for $m=6,7,8$ are below. Each listed normal stands for its cyclic rotations. At length six there are two different alternating masks, and at length eight there are four opposite pairs.

| $m$ | Normals and bias of hyperplanes with $L_{m-1}$ covers |
| --- | --- |
| 6 | $000111$ even; $010101$ odd |
| 7 | $0000111$ even |
| 8 | $00000111$ even; $00010001$ even |

For $m=6$ the bitwise XOR of all eleven source covers is zero, a noncover. On either exceptional alternating plane the XOR of all eleven target covers is $111111$, a cover. An affine map commutes with the XOR of any odd number of points, so those planes are ineligible. For $m=8$ the exceptional plane equates opposite bits. In independent-set coordinates this identifies opposite vertices and leaves two four-cycles sharing that one vertex. Exactly four of its 29 independent sets contain the shared vertex: the two vertices opposite the joint in the two four-cycles can be chosen independently. Thus a nonconstant linear functional on the plane has absolute coefficient $29-2\cdot4=21$. Every nonconstant source coefficient has magnitude at most $F_7=13$. This excludes all four exceptional planes.

The remaining planes at every length are precisely the $n+1$ XOR images. Invert the chosen insertion by deleting its middle site. Its composition with the proposed map is a verdict-preserving affine automorphism on the preceding cycle. The source result supplies exactly $2n$ choices. Distinct hyperplanes and distinct automorphisms give distinct maps. The source threshold is sharp: on a four-cycle in independent-set coordinates, replace $h_0$ by $h_0\oplus h_2$ and leave every other bit alone. If $h_2=1$, any occupied odd vertex already decides failure independently of $h_0$, and otherwise either value of $h_0$ is allowed. Thus this non-permutation shear preserves both verdicts. In selector coordinates its first component is $1\oplus x_0\oplus x_2$. Following it by XOR insertion gives a nonstandard affine successor at source length four.

## Consequence for the finite machine search

In the five-bit search the inherited suite, listed as complete five-bit masks in decimal, was $H=(9,7,19,3,25,29,5,31,14,12,23,11,18,26,13,27)$. It requires six executed steps in the three-bit native model. The 60 maps in the theorem give 60 distinct images of this suite at six bits. A depth-five program exists on each image; only its behavior on that image is required. Thus no affine map preserving the full five-bit predicate propagates this suite's six-step bound. This conclusion allows a separate program for each image. A degree-two extension does preserve six on this very suite, and the full six-bit catalog also has exact clock six. [Explicit quadratic extensions](a-strict-clock-increase-under-one-bit-cycle-subdivision.md) The classification concerns affine transformations of a particular selector predicate, whose unrestricted scan is linear in its packed word count. A superlinear SAT running-time lower bound would require a different argument.

Ramras studied square invertible binary maps of Fibonacci and Lucas cubes. Ashrafi, Azarija, Fathalikhani, Klavžar and Petkovšek studied the vertex and edge orbits under graph automorphisms. The Fourier argument above derives the affine source symmetries without assuming preservation of Hamming distance. The search did not establish historical priority for the codimension-one theorem. [Ramras, 2014, Theorem 2](https://ajc.maths.uq.edu.au/pdf/60/ajc_v60_p001.pdf) · [Ashrafi et al., 2014](https://arxiv.org/abs/1407.4962)

The finite audit independently computes Walsh coefficients by both transfer matrices and the fast Walsh transform through length 15. It enumerates every isomorphism between the source cover set and an eligible six-bit hyperplane and checks all 60 maps against the dihedral XOR construction. Core Lean verifies every exceptional hyperplane and the centroid and shared-bit counts at lengths six through eight. Lean also proves the classification of the two-positive-index Fibonacci product equation for all indices. The general spectral argument is a manuscript proof. [Fibonacci product equation](../lean/FibonacciProductPairs.lean) [Audit](../audits/affine_cycle_successor_audit.py) · [Lean](../lean/AffineCycleSignatures.lean)
