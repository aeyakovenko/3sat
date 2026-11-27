# Weighted exact-cover polynomials with a supplied one-short packing

**Theorem.** There is a polynomial-time constructible family of simple cubic two-permutation instances with a supplied packing leaving three rows uncovered for which the exact-cover generating polynomials are VNP-complete under polynomial projections over every field. Each instance also has a supplied integral solution with one negative coordinate. Every actual perfect cover differs from the supplied packing along a path in the conflict graph. The substitutions establishing hardness use only edge variables and the constant one.

Use row-to-column arrays $P,Q$ and an indeterminate $Y_j$ for each selectable column. The polynomial of an instance is

$$
 Z_{P,Q}(Y)=\sum_{S\text{ exact}}\prod_{j\in S} Y_j.
$$

The sum is over ordinary Boolean exact covers, without imposing that they extend the partial packing. Every monomial is squarefree, has degree $q/3$ on an instance with $q$ columns, and identifies its cover uniquely.

## Projection from directed Hamiltonian cycles

Fix $m\ge3$. Build one Boolean formula describing an ordered tour starting at vertex 0, visiting every other vertex exactly once, and returning to 0. For example, use variables $s_{p,j}$ indicating that at position $1\le p<m$ the tour visits vertex $1\le j<m$. A deterministic Boolean circuit checks that these bits give a permutation matrix. Give it an output $e_{ij}$ for each directed edge, computed by testing if $i,j$ appear at consecutive positions, including the prescribed start and end. Include every gate by a defining equivalence using fan-in at most two, and assert the permutation check. This yields a polynomial-size CNF of width at most three with exactly one satisfying assignment per directed Hamiltonian cycle. All the edge indicators are uniquely determined by the positions. Rooting at the distinguished vertex avoids a factor $m$, which is essential over fields whose characteristic divides $m$.

Apply the [parsimonious path and three-hole packing construction](path-augmentations-with-three-uncovered-points.md). In its variable-choice stage each branch has a private marker with a unique incoming arc. The column for that arc occurs in the exact cover precisely when the assignment chooses that branch. For each flag $e_{ij}$ assign weight $X_{ij}$ to the arc column entering its true marker. Distinct flags use different columns. Assign weight one to every other column. There is exactly one perfect cover per satisfying source assignment. Its surviving product is the product of the directed edge variables of its tour. Thus, as a formal polynomial over the integers and after base change to any field,

$$
                 Z_{P_m,Q_m}(Y)\big|_{Y\mapsto X,1}=\mathrm{HC}_m(X).
$$

The template permutations, the list of selected marker columns, the signed witness and the three-hole packing are computed from $m$ before any edge weights are specified. The number of columns is polynomial in $m$. The relevant source hardness is Valiant's directed Hamiltonian circuit polynomial, complete under polynomial projections over every field. [Valiant, *Completeness Classes in Algebra*, Theorem 3](https://doi.org/10.1145/800135.804419)

For $m=3$, an independent check encoded the two tour orientations with a Boolean selector and six uniquely determined directed-edge flags. The path compiler produced 276 physical columns. Exhaustively enumerating its exact covers gave precisely two, with marker products $X_{01}X_{12}X_{20}$ and $X_{02}X_{21}X_{10}$. This checks the selected-weight convention after the permutation normalization. [Path compiler and finite exact-cover enumerator](../audits/path_augmentation_audit.py)

## Membership and what a determinant representation would imply

For a Boolean triple $a,b,c$ let $E(a,b,c)=a(1-b)(1-c)+(1-a)b(1-c)+(1-a)(1-b)c$. This arithmetic polynomial equals the exact-one truth bit on Boolean inputs in every characteristic. Then

$$
 Z_{P,Q}(Y)=\sum_{x\in\{0,1\}^q}\left(\prod_i E(x_i,x_{P(i)},x_{Q(i)})\right)\prod_j(1-x_j+x_jY_j).
$$

The summand has polynomial degree and an arithmetic circuit of size $O(q)$. This proves VNP membership for the displayed family. A polynomial-order determinant of affine forms representing **the entire weighted polynomial** on each of these instances would, by substitution, provide such determinants for the directed Hamiltonian cycle polynomial and hence place VNP in the class of polynomial-size weakly skew circuits. Substitution also transfers any arithmetic circuit upper bound on this family to the corresponding Hamiltonian polynomial. [Mahajan and Vinay, *Determinant: Combinatorics, Algorithms, and Complexity*](https://www.csa.iisc.ac.in/~chandan/courses/arithmetic_circuits/notes/determinant.pdf)

An individual unweighted exact-cover decision returns a single bit. For these particular Hamiltonian templates that bit is always true; the symbolic weights supply the mathematical content of the projection. Distinct solutions can cancel after a numerical substitution in positive characteristic even when the generating polynomial is nonzero. The symbolic result gives no lower bound on the native time to decide an arbitrary unweighted instance.

## At most $K$ covers

For a *fixed* instance with at most $K$ covers, an affine determinant of order $O(1+Kq)$ for $Z$ always exists over every field. Given the list of covers, make a directed acyclic graph with one separate source-to-sink path per cover, multiplying its selected column weights along the path. Fresh internal nodes keep the paths disjoint; constant-one edges handle short paths. Leave the sink unreachable for zero covers. In a topological order the weighted adjacency matrix $H$ is strictly upper triangular. The bordered matrix

$$
                  \begin{pmatrix} I-H & -e_t \\ e_s^\mathsf T & 0\end{pmatrix}
$$

has determinant $e_s^\mathsf T(I-H)^{-1}e_t=Z$ because $\det(I-H)=1$ and the finite geometric sum counts the paths. Listing the covers is the unavailable information in this nonuniform bound.

In particular on the zero-or-one promise, evaluating the **true count** at all weights one gives the correct verdict even in characteristic two. A uniform deterministic polynomial-time procedure for this promised decision problem, composed with Valiant–Vazirani isolation and the parsimonious three-hole reduction, would yield an RP algorithm for unrestricted SAT. The isolation parameters and gate auxiliaries can be encoded with unique extensions when converting the hashed Boolean predicate to CNF. This is a uniform implication, independent of the short determinants that exist for individual promised inputs. [Valiant and Vazirani, *NP is as easy as detecting unique solutions*](https://doi.org/10.1016/0304-3975(86)90135-0)
