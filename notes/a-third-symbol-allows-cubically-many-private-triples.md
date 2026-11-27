# A third symbol allows cubically many pivotal triples

A complete CSP here has one constraint per unordered triple of distinct names. Each constraint forbids exactly one ordered assignment to its three names. A constraint is pivotal if removing it makes the unsatisfiable instance satisfiable.

**Theorem.** For alphabet $\{0,1,2\}$ there are complete instances on $n$ names with $\Omega(n^3)$ pivotal constraints. For the Boolean alphabet the universal upper bound is $4(1+n+\binom n2)$. [Boolean upper bound and its Lean proof](private-clauses-in-complete-signed-triple-families.md)

## Restricting names to the Boolean alphabet

Use twelve guard names at the positions $(r,c)\in\{0,1,2\}\times\mathbb Z/4\mathbb Z$. Assign each unordered pair a forbidden equal-symbol pair. In a common row forbid $00$, in a common column forbid $11$, and on a common diagonal $c-r\bmod4$ forbid $22$. Two distinct sites share at most one of these features. For remaining pairs choose $00$. Any assignment satisfying the resulting binary constraints would have at most three zeros, four ones and four twos, one per row, column and diagonal respectively. This accounts for at most eleven guard sites, so every guard assignment violates some pair.

For each ordinary name $x$ and each pair of guard names $g,h$, add the ternary constraint forbidding $(2,\sigma,\sigma)$ on $(x,g,h)$, where $\sigma\sigma$ is the pair's forbidden value. An assignment with $x=2$ violates one such triple for every choice of its guard values. When $x$ is Boolean all these triples are satisfied. The same twelve guards serve every ordinary name.

## The private witnesses

In each of three groups introduce $t\ge3$ Boolean choice names $x_1,\ldots,x_t$. Enforce that at least one equals one by an OR chain of proper 3-clauses. For $t=3$ take one clause. For $t\ge4$ use $t-3$ fresh carry names. Start with $x_1\vee x_2\vee y_1$, then for $j=1,\ldots,t-4$ use $\neg y_j\vee x_{j+2}\vee y_{j+1}$, and end with $\neg y_{t-3}\vee x_{t-1}\vee x_t$. A clause is represented by its single Boolean falsifying pattern. All choice and carry names receive the guard constraints above. The chains have pairwise distinct supports.

For every transversal of the three choice groups forbid $111$. Fill every other unoccupied triple, including triples that involve only guards, by forbidding $222$. There are no support collisions. All ordinary names are forced to be Boolean. Each chain then contains a true choice, and selecting one in each group gives a violated transversal. Thus the instance is unsatisfiable.

If the transversal $(i,j,k)$ is deleted, set exactly its three choices to one. In each group set $y_l$ to one exactly when the first $l+1$ choices are all zero. Set the guards to zero. Each chain and every filler is satisfied, while the only violated transversal in the original instance is $(i,j,k)$. This gives $t^3$ pivotal constraints on $n=3(2t-3)+12=6t+3$ names. Extra names can be assigned zero with every newly introduced constraint forbidding $222$, if intermediate lengths are desired.

Anand, Lee and Sharma already used a dummy symbol with $222$ fillers to prove hardness of the complete $(3,3)$-CSP decision problem. Their Theorem 1.5 uses copies of each Boolean variable and recovers a most frequent symbol from a satisfying assignment. This construction uses the same filler idea, a shared deterministic twelve-site guard, and one explicit private witness for every individual transversal. Lee's ordinary Boolean cubic minimal-unsatisfiability result is related to the sparse core before its support table is completed. [Anand, Lee and Sharma, §8.3 and Theorem 1.5](https://arxiv.org/pdf/2410.19066) · [Lee, *On the size of minimal unsatisfiable formulas*](https://arxiv.org/abs/0811.0427)

## Fixed arity and alphabet

The construction works for every fixed arity $k\ge3$ and alphabet size $q\ge3$. For a guard family take $p^2$ sites in an affine plane over a prime field, where $p>q(k-2)$. Choose $q$ distinct parallel classes of lines and associate one symbol $c$ to each class. On each $(k-1)$-set lying on a line of class $c$ forbid the tuple constantly $c$. Any two sites determine a line, so the constraints are compatible with one tuple per support. Use arbitrary forbidden tuples on remaining supports. A legal guard assignment could place at most $k-2$ copies of symbol $c$ on each of its $p$ lines. All $q$ symbol classes together would account for at most $q(k-2)p<p^2$ sites.

Use a separate constant-size guard pool for each unwanted label $d=2,\ldots,q-1$. Lift its $(k-1)$-constraints to $k$-constraints with $x=d$ as the extra entry, for every ordinary $x$. Make $k$ disjoint Boolean choice groups. The OR chain starts and ends with $k-1$ ordinary choices and one carry; every intermediate link has $k-2$ choices between two carries. This supplies arbitrarily large groups of equal size $t$ with $O_k(t)$ ordinary names. Forbid all ones on each choice transversal and use all-twos fillers on remaining supports. Setting only the selected choices to one, with the corresponding Boolean carries, produces $t^k=\Omega_{k,q}(n^k)$ private constraints. The bounded Boolean exponent and cubic or higher growth with a third symbol concern the same one-forbidden-tuple convention.

Run the standalone checker with Python 3. It exhausts all $3^{12}$ guard assignments, enumerates the Boolean cores for the two smallest group sizes, and checks each private witness against every constraint on four full instances. [Executable ternary audit](../audits/ternary_complete_pivots_audit.py)
