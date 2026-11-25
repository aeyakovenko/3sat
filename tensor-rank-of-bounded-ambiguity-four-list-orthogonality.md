# Tensor rank of four-list orthogonality under a witness bound

Each of four labeled lists contains $m\ge1$ Boolean vectors on $h$ coordinates. Write $B$ for the integer number of index tuples whose four selected vectors have no common one. The **four tensor factors** are the entire input lists. A rank-one term over a field $F$ is a product of four scalar functions, one of each list, with unrestricted local computation. For a promise $B\le K$, minimize the rank over all total $F$-valued tensors agreeing with the verdict on the promised inputs. Repeated records occupy distinct list positions.

**Results.** Set $R=2^h$. The unrestricted count tensor $B$ reduced into $F$ has exact rank $R$ when $m$ is nonzero in $F$, and $R-1$ when $m$ is zero in $F$. For the positive decision bit under $B\le K$, a characteristic-zero field or characteristic greater than $K$ gives rank at most $\binom{R+K}{K}$. An upper bound over every field is $16^K\binom{R+K}{K}$.

For a lower bound over every field choose any $1\le k\le\min(K,m)$ and let $\ell$ be the least nonnegative integer with $\binom\ell{\lfloor\ell/2\rfloor}\ge k$. If $r=h-\ell-4\ge0$, every completion of the positive decision bit has rank at least

$$
                    1+(2^r-1)^k.
$$

The corresponding negative verdict has rank at least $(2^r-1)^k$. These are the exact matrix ranks on the two-list restriction used below. In particular, if $a=\min(K,m)\ge1$ and $h\ge(1+\epsilon)\log_2 a$ for fixed $\epsilon>0$, then as $h$ grows the logarithm of the optimum positive tensor rank is $\Theta_\epsilon(ah)$. Indeed $\ell\le\log_2 a+O(\log\log(a+2))$. For $K\le m$ use the displayed upper bound, and for $K>m$ expand any tensor in the coordinate bases of its first three list factors for rank at most $2^{3mh}$. Thus even a bounded number of possible witnesses can significantly increase the rank of the decision predicate.

## Counting and interpolation

For $T\subseteq[h]$, let $n_i(T)$ count the records of list $i$ containing $T$. Inclusion-exclusion gives an integer separated expansion

$$
                 B=\sum_{T\subseteq[h]}(-1)^{|T|}\prod_{i=1}^4 n_i(T).
$$

This gives the count upper bound, with its empty-subset term vanishing in characteristics dividing $m$. For the matching lower bound let $D_h(x,y)=[x\cap y=\varnothing]$. Its matrix is the $h$-fold Kronecker power of $\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$, so it has rank $2^h$ over any field. If $m$ is nonzero in $F$, take each of the first two lists to consist of $m$ copies of one variable record and take every record of the other lists to be all ones. The count matrix is $m^4D_h$. If $m$ is zero in $F$, give each list one distinguished record and $m-1$ empty records. Vary the distinguished records of the first two lists and set the other two distinguished records to all ones. The nonempty-subset terms now give $D_h-J$, where $J$ is the all-ones matrix. Its rank is at least $2^h-1$ by subtracting a rank-one matrix, and at most $2^h-1$ because its empty-set row vanishes.

For the decision upper bound in characteristic zero or greater than $K$, the polynomial $1-\prod_{j=1}^K(1-B/j)$ has the correct values at $B=0,\ldots,K$. Its expansion in the $R$ separated terms has at most $\binom{R+K}{K}$ monomials. Each monomial still factors across the four lists.

There is an integral completion $P(B)=\sum_{t=1}^K(-1)^{t+1}\binom Bt$. It agrees with the decision bit on the promise. Every matrix flattening of this particular completion has rank at most $\binom{R+K}{K}$ even after reduction into a field of positive characteristic, because the larger minors vanish as integers. For a four-factor rank bound use the integral expansion of $(1+z)^B$ as the product of $(1+z)^{\pm N_T}$ with $N_T=\prod_i n_i(T)$. A degree-$v>0$ coefficient from one positive factor counts $v$-element subsets of a Cartesian product. From a negative factor it counts, up to $(-1)^v$, multisets of cardinality $v$ in that product. Group by the number $a_i\in[1,v]$ of distinct elements used in each projection. Each group is a fixed integer times $\prod_i\binom{n_i(T)}{a_i}$, by choosing its four projected subsets and then counting patterns on these fixed sets. The coefficient therefore uses at most $v^4$ separated terms with integer values. The degree-zero coefficient is one. Across a multidegree $(v_T)_T$ of sum at most $K$, the product of these ranks is at most $16^K$, using $v^4\le16^v$. There are at most $\binom{R+K}{K}$ multidegrees. The resulting integral decomposition is valid over every field without division there.

## A Cartesian restriction inside the promise

Use four blocker coordinates, $\ell$ tag coordinates, and $r$ payload coordinates. In blocker $j$, every record of the three other lists contains a one. A record of list $j$ has a zero at its own blocker if active and a one if inactive. A tuple containing any inactive record therefore has a common one. In each of the first two lists activate records $1,\ldots,k$. In each of the other lists activate only record 1. The active records of these last two lists have all tag and payload bits set to one. All unspecified bits of inactive records may be fixed to zero outside the blockers.

Choose $k$ distinct subsets $S_i$ of size $\lfloor\ell/2\rfloor$ in $[\ell]$. The active first-list record $i$ has tag $S_i$ and payload $x_i\in\{0,1\}^r$. The active second-list record $j$ has tag $[\ell]\setminus S_j$ and payload $y_j\in\{0,1\}^r$. These tags have empty intersection precisely when $i=j$, by equal cardinality. Consequently every choice of the two payload lists satisfies

$$
                        B=\sum_{i=1}^k D_r(x_i,y_i)\le k.
$$

All entries of the resulting $2^{rk}$-by-$2^{rk}$ matrix lie inside the promise, including mixtures of different payload lists. Write $N_r=J-D_r$. The negative decision matrix is the Kronecker power $X=N_r^{\otimes k}$. It has rank $(2^r-1)^k$ by the calculation above. The positive decision matrix $J-X$ has rank exactly $1+\operatorname{rank}X$. Indeed $X$ has both a zero row and a zero column. Subtract the corresponding all-ones row of $J-X$ from the other rows. The differences span the row space of $X$, up to sign, and their entries in the zero column vanish. The retained all-ones row is independent of them. Restriction and matrix flattening cannot increase four-factor tensor rank.

A finite check used $m=3$, $k=2$, $r=2$ and $\ell=2$. Exhausting all $256$ mixtures of payload lists and all $81$ tuples per mixture gave the stated count. The positive and negative matrices had ranks 10 and 9 respectively over each of $\mathbb F_2$, $\mathbb F_3$ and $\mathbb F_5$.

## Scope on encoded SAT inputs

The [compact four-list projection](compact-four-list-orthogonality-in-dimacs.md) gives a proper DIMACS template with exactly $B$ satisfying assignments in $\Theta(mh)$ bits when $h\le m^{O(1)}$. Partition its varying data positions by their originating list. Fixing the public positions and inactive records transfers the displayed rank lower bounds to this grouping, including for representations allowed arbitrary values on other strings. On the tagged family itself a globally correct SAT solver can check the public layout and the tag/blocker restrictions in $O(mh)$ operations, then scan the $k$ paired payloads for an empty intersection in $O(kr)$ more; use a complete fallback outside the matching layout. For a uniform template one can generate the first $k$ equal-weight tags in lexicographic order by enumerating successive fixed-weight subsets in $O(\ell+1)$ work per tag. Dimension and active-count markers can be fixed in the template or read by scanning the blockers. Hence these large ranks already occur on a linearly decidable family. The grouping charges communication across whole lists; it supplies no unrestricted RAM running-time or Boolean gate lower bound.
