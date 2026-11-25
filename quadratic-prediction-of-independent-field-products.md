# Quadratic prediction of a sum of independent field products

Let $K=\mathbb F_q$, $q=2^h$, $h\ge1$, and let $r$ independent uniform triples $x_i=(a_i,b_i,z_i)$ range over $K^3$. Set
$$
 H_r(x)=\sum_{i=1}^r \operatorname{Tr}_{K/\mathbb F_2}(a_i b_i z_i),\qquad b=(2q-1)/q^2.
$$
For every $r\ge0$, the **exact maximum sign correlation with an arbitrary binary quadratic** on all $3rh$ bits is $b^r$. Quadratic terms may connect any two rows. This gives a family of ordinary packed 3-CNFs on which a quadratic description of every actual SAT run needs $(1/2-o(1))rh$ binary test answers on every input. A fixed adaptive strategy needs $(1-o(1))rh$ answers on almost all inputs. Both leading constants are attainable in the respective senses specified below.

The one-field correlation $b$ is known. The previous argument used the field line in the radical of a derivative to bound its bias in terms of itself. The tensorization below uses a different random field scalar in each row. For $h=1$ it also gives an elementary derivation of the disjoint-CCZ quadratic correlation, independently of the quantum fidelity proof. I have not established priority for the arbitrary-field tensorization. [One-field proof and references](trace-product-quadratic-correlation.md) · [Kolokotronis and Limniotis, Corollary 1](https://eprint.iacr.org/2011/212) · [CCZ fidelity and the corresponding native runs](quadratic-explanations-of-packed-sat-runs.md)

## A recurrence allowing arbitrary cross-row couplings

Write $\beta_j=\max_Q|\mathbb E(-1)^{H_j+Q}|$ and $\beta_0=1$. The zero quadratic gives $\beta_j\ge b^j$. Indeed, averaging over $z_i$ gives exactly the probability that $a_i b_i=0$, namely $b$.

Fix a maximizing quadratic $Q$ for $r$, and let $u=(u_1,\dots,u_r)$ be a uniform random additive shift with $u_i\in K^3$. After squaring the correlation, the inner mean is the sign bias of the quadratic $D_u(H_r+Q)$, where $D_uP(x)=P(x+u)+P(x)$. Its polar bilinear form at $v,w$ is $\sum_i\operatorname{Tr}(\det(u_i,v_i,w_i))$. The shifts preserve the block diagonal polar form because $D_uQ$ has degree at most one. For $u_i\ne0$ the radical of its $i$th block is precisely $K u_i$: for $v_i\notin K u_i$ the determinant in the remaining argument is surjective onto $K$, and the trace itself is surjective. Thus the total binary rank is $2h$ times the number of nonzero $u_i$.

A binary quadratic has sign bias of magnitude zero or two to the negative half of its polar rank. In the nonzero-bias case its derivative is zero on every direction in that radical. Both conclusions follow by squaring the mean and averaging over shifts. In particular, nonzero bias requires this vanishing for all directions $tu=(t_i u_i)_i$ with independently chosen $t_i\in K$. On these directions the second difference is independent of the base point. At zero it is
$$
   D_{tu}D_u(H_r+Q)=
        \sum_i \operatorname{Tr}((t_i^2+t_i)u_{i1}u_{i2}u_{i3})+B_Q(u,tu),
$$
where $B_Q$ is the binary polar form of $Q$. For fixed $u$ this is binary-linear in the vector $t$, so averaging its sign over $t$ gives the indicator that all the tested derivatives vanish. Testing only these directions when some $u_i=0$ gives a valid upper bound. We obtain
$$
 \beta_r^2\le \mathbb E_{u,t}
 \prod_i \left(q^{-1}+(1-q^{-1})[u_i=0]\right)
 (-1)^{D_{tu}D_u(H_r+Q)}.
$$

Expand the product. In each row forced to $u_i=0$ the coefficient including its probability is $(1-q^{-1})q^{-3}$. Every other row has coefficient $q^{-1}$ before averaging $t_i$. Of its $q$ scalars, two give $t_i^2+t_i=0$ and the other $q-2$ give a nonzero coefficient. For fixed scalars and any $j$ rows of the last type, condition on all shifts outside those rows. On the $j$ active independent rows $B_Q(u,tu)$ is an arbitrary binary quadratic. Multiplying the first field coordinate in each active row by its nonzero coefficient is a binary-linear bijection, so the resulting absolute mean is at most $\beta_j$. With
$$
 A=(1-q^{-1})q^{-3}+2q^{-2},\qquad B=q^{-1}(1-2/q)
$$
this proves
$$
                \beta_r^2\le\sum_{j=0}^r {r\choose j} A^{r-j} B^j\beta_j.
$$
The positive number $b$ satisfies $b^2=A+Bb$ and $b>B$. Applying the inductive upper bound to all $j<r$ yields
$$
        \beta_r^2-B^r\beta_r\le b^{2r}-B^r b^r.
$$
If $\beta_r>b^r$, the left side would exceed the right side by $(\beta_r-b^r)(\beta_r+b^r-B^r)>0$. Thus $\beta_r=b^r$. When $q=2$, $B=0$ and $A=9/16$, giving $(3/4)^r$ immediately. The same proof permits different field sizes in different rows, by induction over proper subsets, replacing $b^r$ and $B^r$ by the products of the individual values.

## Attaining the native certificate bounds at encoded-bit scale

Take $r=2^{3h}$, $D=rh$. In the dictionary-and-parity 3-CNF keep the same table names and query rows, pinning each public table bit to the trace of its three field factors. All input bits are affine functions of the $3D$ source bits. The ordinary binary-identifier encoding has length $\Theta(D)$. [Explicit clause layout](spanning-trees-for-a-packed-sat-verdict.md)

Set $\lambda=-\log_2(b^r)=r(h-1-\log_2(1-2^{-h-1}))$. For any nonempty fiber $S$ defined by $t$ binary quadratic test answers on which the verdict is quadratic, expansion of its indicator into quadratic phases gives $\Pr[S]\le2^{-\lambda}$. The nonzero indicator itself has binary algebraic degree at most $2t$, giving $\Pr[S]\ge 2^{-2t}$. Thus every such certificate requires $t\ge\lambda/2$. Adaptively chosen tests on a single execution form such a certificate even if selected with free knowledge of the particular input. For a single fixed strategy used on the uniform input, the chance that an exact terminal fiber is reached by depth $t$ is at most $2^{t-\lambda}$. A convenient threshold is $t=\lfloor\lambda-r\rfloor$, with exceptional probability at most $2^{-r}$. As $h$ grows the per-input lower bound is $(1/2-o(1))D$ and the fixed-strategy threshold is $(1-o(1))D$. These estimates apply to every correct solver using the quadratic register, fixed-address memory and common instruction path convention. [Run and indicator proofs](quadratic-explanations-of-packed-sat-runs.md)

For a single row there is an exact integer statement at every input. Since $h-1<-\log_2 b<h$ for $h\ge1$ (both inequalities are strict), $\lceil-\tfrac12\log_2 b\rceil=\lceil h/2\rceil$. Guess the $h$ input bits of $a$ and check them in pairs by quadratic equality tests. On this fiber the verdict is quadratic in the two remaining factors. Thus the minimum number of input-specific quadratic tests permitting a quadratic residual is exactly $\lceil h/2\rceil$ at each point. This convention leaves the residual to be evaluated.

One globally correct solver copies the pinned Boolean table to an aligned work array and checks the entire template structure, allowing either Boolean value at every table position. Then it gathers the addressed pin for each query and XORs the results, with a fallback for other formulas. The scanner takes $O(r)$ word operations. On this particular family the table is public, so fixing all $D$ bits of the first source block makes each gathered value and the accumulated answer quadratic in the remaining bits. Query identifiers formed by concatenation are affine, and indexing an aligned bank uses a fixed tag and those varying bits. Thus $D+1$ tests explain its execution for a fixed testing strategy, including the optional terminal branch. Choosing tests with knowledge of the input lets one fix these same $D$ bits two at a time, at cost $\lceil D/2\rceil+1$. These upper bounds match the preceding lower bounds to leading order. Comparisons in template checks can use XOR to compare repeated fields whose equality holds throughout the family, as in the original scanner.

There is also a $\Theta(r)$-time solver on the family whose only input-dependent memory addresses use the first two blocks. Precompute a table indexed by $a,b$, storing the $h$ binary coefficients of $z\mapsto\operatorname{Tr}(abz)$ in the coordinate basis of the input $z$. This costs $O(2^{2h}\operatorname{poly}(h))=O(r)$ uniformly: choose a canonical irreducible polynomial of degree $h$ by enumeration with polynomial-time irreducibility tests, and perform field arithmetic by elementary polynomial arithmetic. Validate every prescribed public dictionary pin in $O(r)$ total operations, using a public parity table of size $2^h$ on public loop indices. In a query, look up the coefficient word at the address $(a,b)$, AND it with $z$, and XOR into a word accumulator. Compute parity once using fixed shifts at the end. All writes and all remaining reads on the family use public addresses. After fixing the first block this solver also has quadratic state bits (the lookup coefficients are then linear in the second block). The lower bound survives this algorithm, which forms no address involving all three blocks and achieves the optimal $\Theta(L/\log L)$ time on these inputs. The unrestricted superlinear SAT target remains open. [Finite field audit](independent_field_trace_audit.py)

## A sublinear-time scanner with fully public addresses

Even the remaining two-block lookup addresses can be removed while keeping the running time $o(L)$ on this family. Choose the polynomial basis $1,\alpha,\ldots,\alpha^{h-1}$ for all three inputs. For their coordinate polynomials $P_a,P_b,P_z$ of degrees less than $h$,
$$
 \operatorname{Tr}(abz)=\sum_{j=0}^{3h-3}[X^j](P_a P_b P_z)\operatorname{Tr}(\alpha^j).
$$
The unreduced polynomial product is sufficient. Two levels of polynomial multiplication here mean two complete multiplications; each has a fixed Boolean circuit of $O(h^{\log_2 3})$ AND/XOR gates by the usual recursive three-product split. The final contraction with the public coefficients costs $O(h)$ gates. The circuit depends only on $h$.

Use $\ell$ parallel lanes, with $\ell$ the largest power of two no greater than both $h$ and the machine word width. Here $\ell=\Theta(h)$. Collect the fields of $\ell$ consecutive rows, and transpose their bit arrays so that one word holds the $\ell$ values of a given bit position. For an $\ell$-square block this costs $O(\ell\log\ell)$ word operations: at stage $j$ exchange the off-diagonal subblocks indexed by bit $j$ of the row and column, using shifts and the periodic column mask for that bit on each pair of rows. The stages exchange all row and column index bits. A bounded number of padded blocks handles $h$ columns. All indices and masks depend only on the public dimensions. Now evaluate each circuit gate by one word operation, XOR the resulting lane-word into an accumulator, and take its parity once at the end. Padding the final batch affects only unused lanes. Public table pins can be validated by the public-index loop above. The total cost including packing is
$$
        O\big(r\log(h+1)+r h^{\log_2(3)-1}\big)=o(rh)=o(L).
$$
A template mismatch still invokes a complete SAT solver. On the promised family all input and work-memory addresses of this implementation are independent of $a,b,z$. The nearly $D/2$ quadratic-test lower bound on every individual explanation therefore coexists with a sublinear native clock even when the address pattern is fixed. [Independent transposition and field-product checks](public_address_field_products_audit.py)
