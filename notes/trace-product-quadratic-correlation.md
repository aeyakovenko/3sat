# Exact prediction of a SAT verdict by adaptive quadratic queries

Write $K=\mathbb F_q$, $q=2^m$, $m\ge1$, and $F(x)=\operatorname{Tr}_{K/\mathbb F_2}(x_1x_2x_3)$ for a uniform $x\in K^3$. A query returns one chosen quadratic Boolean polynomial on the $3m$ input bits. Its coefficients may depend on all earlier answers. Let $C_t$ be the largest absolute correlation with $(-1)^F$ of the signed output of a deterministic tree using at most $t$ queries.

The exact profile at small and intermediate depths is
$$
 C_0=\beta,\qquad C_{r+1}=2^r\beta\quad(0\le r\le\lfloor m/2\rfloor),
 \qquad \beta=\frac{2q-1}{q^2}.
$$
Accuracy under the uniform distribution is $(1+C_t)/2$ after orienting the answer. In particular the first query buys nothing over the best constant guess. Each additional query in the indicated range doubles the optimal advantage. The **minimum depth for exact decision is $m+1$**. The full intermediate profile beyond the displayed range is not determined here. A mixture of trees with independent random coins cannot exceed their maximum average accuracy.

These are bounds for an ordinary explicit 3-CNF family under a specified form of input access. The literal signs can encode the field inputs or linear functions of them. Each physical quadratic query then restricts to a quadratic on the labels. Retaining the raw label signs allows every label query in the matching strategies. See the companion note for the two physical layouts, including the $\Theta(m\log m)$-bit affine encoding. None of these access bounds gives a superlinear unrestricted RAM lower bound. [CNF construction and storage lower bound](quadratic-observations-of-a-sat-verdict.md)

## The one-query value was known

Corollary 1, p. 9 of the 2011 Kolokotronis–Limniotis preprint states a formula for the second-order nonlinearity of a Maiorana–McFarland function formed from a quadratic perfect nonlinear map. Take the vectorial map $(u,v)\mapsto uv$ on $K^2$. Its derivative in direction $(a,b)\ne(0,0)$ is $av+bu+ab$, a balanced affine map to $K$. In dual binary bases its pairing with the third field element is $F$. The formula stated there gives minimum Hamming distance $q(q-1)^2/2$ to the quadratic Boolean functions on $3m$ variables. This is exactly the displayed $\beta$. The constant zero achieves it because averaging over $x_3$ leaves the probability that $x_1x_2=0$. We independently obtained the same value by the self-bounding calculation below. The depth profile and exact-depth consequence are separate deductions. Historical priority for those deductions remains unverified. A later presentation by the authors gives a narrower parameter range for the conference theorem. This attribution is to the 2011 preprint; the field-specific proof below is independent. [Kolokotronis and Limniotis, Corollary 1](https://eprint.iacr.org/2011/212) · [Authors’ later presentation, slide 22](https://cgi.di.uoa.gr/~klimn/Presentation_CryptAAF_Limniotis.pdf#page=22)

For context, Bhrushundi, Harsha, Hatami, Kopparty and Kumar study the same multiplication tensor. Their explicit correlation lemma treats lower-degree forms respecting the block structure. The exact value above permits every binary quadratic, including terms internal to one block. Ford and Gál already derive an asymptotically linear three-party communication bound for the multiplication bit. A quadratic probe can be simulated by partitioning its monomials among players, each seeing the variables it needs. Thus an order-$m$ bound for adaptive quadratic queries follows from prior work as well. [Bhrushundi et al., §3.4 of the preprint](https://arxiv.org/pdf/1804.09124) · [Ford and Gál, Theorem 4.5](https://www.cs.utexas.edu/~panni/icalp05.pdf)

## A scalar identity on the radical of each derivative

Put $\chi(b)=(-1)^b$, $D_z f(x)=f(x+z)+f(x)$, with addition of bits modulo two. Choose a binary quadratic $Q$ maximizing $|\mathbb E_x\chi(F(x)+Q(x))|$, and call its value $\beta_{\max}$. Squaring and changing variables gives
$$
 \beta_{\max}^2=\mathbb E_z\mathbb E_x\chi(D_z(F+Q)(x)).
$$
For nonzero $z$ the inner phase is quadratic. Its polar form on directions $u,v$ is $\operatorname{Tr}(\det(z,u,v))$. Indeed the third difference of the cubic sums the six products from one coordinate of each direction; in characteristic two this is the determinant. The radical is precisely $Kz$: if $u$ is outside that line, $\det(z,u,\cdot)$ takes every field value and trace takes both binary values. The polar rank on the binary space of dimension $3m$ is $2m$.

For a binary quadratic $g$ with polar form $B$, the square of its mean sign equals $\mathbb E_y\mathbb E_x\chi(D_y g(x))$. The inner expectation vanishes for $y$ outside the radical of $B$. On the radical the exponent is the linear functional $g(y)+g(0)$, independent of $x$. Summing it over the radical gives zero unless it vanishes everywhere. Therefore the magnitude of the mean is either zero or $2^{-\operatorname{rank}(B)/2}$. Call a shift $z$ compatible if $D_z(F+Q)$ is invariant under every translation by $tz$ for $t\in K$. The zero shift qualifies. Writing $\alpha$ for the compatible fraction,
$$
 \beta_{\max}^2\ \le\ q^{-3}(1-q^{-1})+q^{-1}\alpha .
$$
Here the zero shift contributes one, and a compatible nonzero shift contributes at most $1/q$.

The compatibility test itself is a character sum. Write $B_Q$ for the polar form of $Q$. On the radical the second difference is independent of the base point, so evaluating at zero gives
$$
 D_{tz}D_z(F+Q)=\operatorname{Tr}((t^2+t)z_1z_2z_3)+B_Q(z,tz).
$$
For fixed $z$ this is binary-linear as a function of $t$. Its mean sign over $t$ is exactly the indicator of compatibility. Average over $z$ next. The scalars zero and one give sign one everywhere. For each remaining $t$, $t^2+t\ne0$, and $z\mapsto B_Q(z,tz)$ is quadratic in binary coordinates. Rescaling the first field coordinate is a binary linear bijection and reduces this correlation to a candidate in the definition of $\beta_{\max}$. Hence
$$
 \alpha\le 2/q+(1-2/q)\beta_{\max}.
$$
Combining the inequalities gives
$$
 \left(\beta_{\max}-\frac{2q-1}{q^2}\right)
 \left(\beta_{\max}+\frac{q+1}{q^2}\right)\le0 .
$$
The second factor is positive, and the constant guess attains the first factor's root. The same function also minimizes the maximum quadratic correlation over all trilinear functions on three $m$-bit blocks. Indeed every such function already has constant correlation at least $(2q-1)/q^2$ by averaging over its third block and retaining the two zero-block events.

## What the last query saves

Every signed depth-one tree outputs a constant or the sign of one quadratic, possibly negated. Its expansion as a real sum of quadratic signs has coefficient absolute values summing to one. At a higher query $Q$, multiply the two child expansions by $(1+\chi(Q))/2$ and $(1-\chi(Q))/2$ and add. Products of quadratic signs are quadratic signs. Induction yields coefficient absolute sum at most $2^{t-1}$ at any depth $t\ge1$. Thus $C_t\le 2^{t-1}\beta$. At depth $m$ this gives $C_m\le1-1/(2q)<1$. Exact computation at depth $m+1$ reads the $m$ bits of $x_1$ and then asks the quadratic $\operatorname{Tr}(x_1 x_2x_3)$ with its now fixed first argument.

## A matching strategy through half the field dimension

Choose $z=(1,1,c)$ with $c\ne0$. On the scalar line $sz$ the phase is $R(s)=\operatorname{Tr}(cs^3)$. Its polar form on $s,t$ is $\operatorname{Tr}(c(s^2t+st^2))$. By trace invariance under squaring, the radical equation is $c s^2+(cs)^{2^{m-1}}=0$. Squaring gives $cs(c s^3+1)=0$. If $m$ is even, choose a noncube $c$ in the cyclic multiplicative group. The radical then has dimension zero. If $m$ is odd, cubing is a bijection, and the radical has dimension one. In both cases the polar rank is $2\lfloor m/2\rfloor$.

For $0\le r\le\lfloor m/2\rfloor$, choose a nondegenerate binary subspace $W\subset K$ of dimension $2r$ by taking $r$ symplectic basis pairs for that polar form. As a function of $s$,
$$
 D_{sz}F(x)=R(s)+L_x(s).
$$
Here $L_x(s)$ is binary-linear in $s$ because the remaining terms involve $s$ and $s^2$. For fixed $s$ its coefficients as a function of $x$ have degree at most two. Define
$$
 g(x)=2^{-r}\sum_{s\in W}\chi(D_{sz}F(x)).
$$
In symplectic coordinates $(a,b)\in\mathbb F_2^r\times\mathbb F_2^r$ the exponent is $a\cdot b+A(x)\cdot a+B(x)\cdot b$. Each coordinate of $A,B$ is a quadratic Boolean function, including its fixed linear-phase offsets. Summing first over $a$ leaves only $b=A(x)$ and gives **$g(x)=\chi(A(x)\cdot B(x))$**. The tree reads $r$ coordinates of $A(x)$, then asks a single quadratic giving the selected combination of the $B(x)$ coordinates. Its signed correlation is exactly
$$
 \mathbb E_x\,g(x)\chi(F(x))
 =2^{-r}\sum_{s\in W}\mathbb E_x\chi(F(x+sz))
 =2^r\beta .
$$
This proves equality for the advertised depths. In particular the exponential factor from the decision-tree expansion is attainable in this range, even with all branch dependence confined to the last question. The construction depends on the trace form's scalar lines. A generic cubic need not have the same depth profile.


## A lower bound and an obstruction at larger depths

For $\lceil m/2\rceil\le r\le m$ put $s=m-r$. Choose a nondegenerate $2s$-dimensional subspace $W$ for the scalar quadratic above. Read $m-2s$ affine bits specifying the coset $x_1=u_0+W$, choosing a fixed representative $u_0$. In this branch separate off the known quadratic $\operatorname{Tr}(u_0x_2x_3)$, which can be included in the last query. The residual first input is uniform on $W$. The $s$-pair strategy uses only shifts in $Wz$, preserving this conditional distribution. Its starting bias is $2^{-2s}+(1-2^{-2s})/q$ by conditioning on the first two inputs. With $m-2s+s+1=r+1$ queries the achieved correlation is therefore
$$
 2^{r-m}+2^{-r}-2^{r-2m}.
$$
This recovers exact decision at $r=m$. It is a lower bound on the attainable correlation at the other displayed depths.

Simply enlarging the subspace in the previous signed-shift average cannot settle the larger depths. In fact every nonzero shift of the unmodulated $F$ has nonnegative autocorrelation. For a shift $(a,b,c)$ with $b\ne0$, averaging over the first coordinate enforces $x_3=(c/b)x_2+c$. What remains in the trace exponent is $(ac/b)x_2^2+acx_2$, an additive function. The autocorrelation is zero or $1/q$. Permuting coordinates deals with the other nonzero shifts, and any shift having a zero coordinate has autocorrelation $1/q$. Now if a binary shift space $U$ yielded a sign everywhere by the normalized average of $\chi(D_zF(x))$ over $z\in U$ with factor $|U|^{-1/2}$, the square of every coset sum of $\chi(F)$ would equal $|U|$. Averaging those squares forces the sum of the nonidentity autocorrelations over $U$ to be zero. Nonnegativity forces each to vanish. Projection onto the first coordinate must then be injective on $U$, so $\dim U\le m$. Other adaptive strategies remain possible.

## How many true SAT answers can certify a native verdict?

There is an application where the three field elements are themselves outputs of the hard native program. Use the [past-conditioned family](learning-from-earlier-sat-verdicts.md) at stage $j$, with its hidden $h$-bit word $a_j$. Put $m=\lfloor h/3\rfloor$ and interpret its first $3m$ bits as $u,v,w\in K$. Use the same deterministic computation base in a new ordinary 3-CNF, append gates testing $F=\operatorname{Tr}(uvw)$ and assert the desired pin. Fix the first irreducible binary polynomial of degree $m$ as modulus. Since $m=O(\log j)$, trial division even by exhaustive search fits polynomial time in $j$ for generating the compiler parameters. The formula still has $N_j=2^j(j+1)^{O(1)}$ bits and polynomial-in-$j$ word generation. Give a learner the actual full past and an oracle answering **any quadratic of the entire current hidden word**. Every such question is itself an ordinary signed 3-SAT instance sharing the computation base: append its $O(h^2)$ quadratic evaluation gates and assert the result. The oracle gives one free verdict per question. It provides no witness bits.

Consider any transcript of $t$ such questions on a trial word, fixing the learner's nondeterministic choices when appropriate. Its indicator is a product of $t$ signed quadratic equality indicators. Over the reals its expansion in quadratic signs has coefficient absolute sum at most one. Hence a leaf on which $F$ is constant has uniform mass at most $\beta$, by the correlation bound, also with unused label bits present (condition on them). Over $\mathbb F_2$ the same indicator has degree at most $2t$. A nonzero degree-$D$ Boolean polynomial on $h$ variables occupies at least $2^{h-D}$ points when $D\le h$. Indeed if a variable occurs, its derivative is nonzero of degree at most $D-1$ on the remaining variables; each nonzero derivative value gives at least one nonzero endpoint. Constants start the induction. Therefore for $t<\lceil m/2\rceil$ every nonempty transcript has mass at least $2^{-2t}\ge 2/q>\beta$. **No such transcript forces either sign of $F$.**

It follows unconditionally that at every sufficiently late stage **no fixed, uniformly sound deterministic procedure** can certify even one pin of this physical target in $N_j/(\log N_j)^C$ ordinary RAM steps with fewer than $\lceil m/2\rceil$ free quadratic SAT answers, for a sufficiently large fixed $C$. It can abstain on arbitrary inputs. The same conclusion holds for a uniformly sound nondeterministic verifier at clock $2^{\lfloor j/k\rfloor}/(j+1)^B$ under deterministic $O(N^k)$ SAT, with sufficiently large fixed $B$ and $k=1,2,3$. Indeed any such timely claim would, by the previous note's transcript theorem, force its sign on every trial word giving the same replies. Keeping the physical stage formula and all guesses fixed is essential. There is no current-stage advice. Here $m=\Theta_A(\log\log N_j)$.

The query threshold for infinitely often sound certification is exact. Test pairs of coordinates of $u$ for being simultaneously zero, using one quadratic $(1+u_i)(1+u_{i+1})$ per pair and one affine query if necessary. Certify $F=0$ if all tests pass, and otherwise abstain. This uses $\lceil m/2\rceil$ queries, costs polynomial time in $j$, and succeeds infinitely often because the actual hidden word is zero on infinitely many stages. With one further query, a nondeterministic learner can certify the actual sign at **every** stage: guess $u$, verify the guess in pairs, and ask the resulting known quadratic in $v,w$.

There is also an exact deterministic threshold for a procedure required to decide on **all** sufficiently late stages within the same sublinear clock. If it used at most $m$ free quadratic answers, enumerate all trial words and treat a timeout, excess query, abstention or incorrect sign as a failure. For every large stage there is some failing trial by the depth-$m$ lower bound. Reporting one such word would be a timely, uniformly sound exclusion after the finite startup because the actual word succeeds. The retirement argument rules this out. The $m+1$-query strategy works on every actual stage. These are lower bounds with a sublinear computational budget and a restricted source of extra true SAT answers. They leave unrestricted linear time open.

[Lean checks of the correlation argument's components](../lean/TraceProductBias.lean) · [Finite comparison of derivatives and adaptive strategies](../audits/trace_product_bias_audit.py)
