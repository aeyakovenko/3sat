# Connected lifts and exact witness counts in the two-layer construction

In the two-layer 3-SAT reduction, let the two sides have $s$ sheets each. Fix any satisfying assignment of the public bits at the exceptional setting of the two designated file bits. Let $D$ count second-layer negative matching edges whose two physical endpoint bits differ. The number of full satisfying assignments extending these particular public bits is exactly
$$
                              2^{D-2}.
$$
This formula gives a size induction on connected inputs. One extra sheet on each side can double every witness multiplicity while preserving the entire projected decision problem. Two extra sheets on each side can instead preserve the multiplicity exactly. [The two-layer family and its linear-size reduction from proper 3-SAT](two-missing-guards-in-a-sheeted-sat-formula.md)

## Counting a single fiber

Write $x$ for a center bit and $a,b$ for its positive and negative partner bits. At a regular second-layer center the allowed guard rows are $000,111,001,100$. Enumerating the two private bits in the two port clauses gives local counts
$$
                 M(0,a,b)=1+a,\qquad M(1,a,b)=a+(1-b).
$$
On a viable row the count is two precisely when $a=1$ and $(x,b)\ne(1,1)$. All other viable rows have one completion. The two intact positive-self anchors each have $x=a=1,b=0$ and one completion. The first-layer private bits are uniquely fixed at every center.

The positive port map permutes the physical vertices, including the two fixed points. Thus the sum of the positive partner bits counts all center ones. On every viable row $x=b=1$ implies $a=1$. Each negative matching edge with both endpoint bits one therefore removes two potential free bits. The two intact anchors remove one more each. If $E_{11}$ counts negative edges with both ends one, the remaining number of free private bits is
$$
     (\text{number of center ones})-2E_{11}-2 = D-2.
$$
All private pairs are disjoint, proving the formula. In particular $D\ge2$. Lean verifies the local counts from the guard and port clauses and the product identity on an arbitrary finite list of negative edges, given viability, two anchors and conservation of the positive-partner sum. [Formal product proof](../lean/SheetLiftMultiplicity.lean)

## A connected lift by one pair

Choose any regular center $u$ on either side in layer two. Add a sheet $v$ on its side and a sheet $w$ on the other side. Pair $v,w$ in the first positive matching. In the first negative matching, replace $u$–$t$ by $u$–$w$ and $v$–$t$. This inserts two vertices into the same alternating first-layer cycle, forcing the physical values $v=u$, $w=1-u$. Every old first-layer solution has a unique public extension, and every new one restricts to an old one.

Move both former second-layer ports of $u$, including their reciprocal endpoints, to $v$. Then pair $u,w$ on both second ports, with both centers regular. The old working clauses at $u$ now occur at $v$, with the same triple of physical values. The private pairs there identify with the old pairs at $u$. The new paired centers are antipodal, so their local counts are two and one in either orientation. Equivalently the negative matching has gained exactly one bichromatic edge. Each full old witness has exactly two extensions under this identification. The two anchors stay in place. The matching graph has the same number of connected components because the first-layer cycle still joins $u$ to $v$ and all transferred edges can use that path. For every $s\ge2$ there is a regular center on each side, including in presentations with no solution.

The same operation can be iterated at any eligible centers. Contract first-layer cycles and discard tautological $P(x,t,t)$ jobs. Each lift adds only those tautologies and carries each preexisting projected constraint to itself under the cycle identification. An unrestricted RAM can perform the contraction and the projection in one linear pass over the named matching representation, with linear-time cycle traversal. For descendants of a fixed seed, enumeration of the bounded number of remaining logical bits then takes constant time beyond the scan up to a seed-dependent constant factor. Arbitrary relabeling and a hidden lift history preserve this bound. Thus even connected doubling of *all* witness multiplicities at every size leaves a linear-time algorithm on every such descendant family.

## An extension with one private completion

The two positive-self anchors have physical value one. The left anchor's first-layer logical bit is one and the right anchor's logical bit is zero. Insert one new pair into each anchor's first-layer cycle by the same subdivision, leaving all old second-layer ports in place. In both second-layer matchings pair the new left occurrence of the first anchor's name with the new right occurrence of the second name, and pair the other two new occurrences. The first pair has physical bits $1,1$ and the second $0,0$. Their four local counts are all one. The new shared values and their private witnesses are forced. Every old full solution has exactly one extension. Projection shows that an unsatisfiable input also remains unsatisfiable. The construction preserves connectedness of a connected input.

Together the two lifts determine the strongest power of two dividing **every** model count at each size. The first-layer positive matching has opposite bits on each edge, hence there are $s$ physical ones. The number $D$ has parity $s$ because $D+2E_{11}=s$. For odd $s$ every satisfying fiber therefore has even size. At $s=1$ the unique presentation is unsatisfiable because its negative edge joins the two anchors. At $s=2$, take the first positive, first negative and second negative matchings to be identity between sides; use the transposition for the second positive matching before cutting its edge at left zero. Its unique satisfying physical values, interleaving left and right, are $1,0,0,1$, with $D=2$ and one full witness. The one-pair lift gives exactly two at $s=3$. Repeated two-pair lifts give one full witness at every even $s\ge2$, and exactly two at every odd $s\ge3$. In fact the complete spectrum of nonempty fiber sizes at size $s\ge2$ is
$$
            \{2^k: 0\le k\le s-2,\; k\equiv s\pmod 2\}.
$$
The count formula gives the upper bound and parity. Starting from the unique-model seed, take $k$ one-pair lifts and $(s-2-k)/2$ two-pair lifts. Each example is connected with exactly one satisfying public assignment, so the indicated fiber size is also its total number of full models. Thus odd size always makes parity uninformative about the SAT verdict, even on arbitrarily large connected presentations.

The audit enumerates all 225 normalized presentations through $s=3$, with no contraction when computing fibers. It checks all 880 available one-pair lifts on both sides of those inputs, and the two-pair extension of each presentation. The three input sizes have respectively $0,1,64$ full witnesses across all presentations. A growth argument for running time still needs instances on which the projected decision work itself increases. [Executable checks](../audits/sheet_lift_multiplicity_audit.py)
