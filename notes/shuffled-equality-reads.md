# Extra memory accesses in disjoint parts of a shuffled equality instance

On a single unsatisfiable Horn 2-CNF, every deterministic SAT solver must perform additional memory accesses beyond its first reads of all private records. The placement of the records can depend on the solver. For an arbitrarily large integer $s$ there are $h=s$ consecutive pairs of discovery intervals. In each pair, the first interval introduces $s$ distinct records. The solver must either change many memory cells during that interval or later return to many of those very records. These obligations hold on the same input. Each charged store or return can be assigned to only one interval.

## The formula and the actual accesses

Put $N=hs$ and $q=s^2$. For each logical position $1\le t\le N$ there are two records, the equalities
$$
       U_{t-1}=V_{t,a_t},\qquad V_{t,b_t}=U_t
$$
with $a_t,b_t\in[q]$ and distinct names for different $(t,v)$. Each equality is two binary Horn clauses. Pin $U_0$ true and $U_N$ false. On the promised format these pins conflict exactly when $a_t=b_t$ for all $t$. At a mismatch the two halves of that link end at distinct private vertices. The component of $U_0$ can be set true and every other component false. On any equal input, changing one record's symbol alone thus changes the SAT verdict. In particular every correct solver must touch all $2N$ private records.

Use $2N$ interchangeable physical slots with common record width. Pad with fixed tautologies as needed so an aligned input word intersects the varying fields of at most one slot. Call a read a *touch* when its word meets one of these fields. This definition includes a read of the index or orientation alone. The public pins, spacing and header make no reference to the eventual ordering. An explicit binary literal serialization takes $\Theta(N\log N)$ bits. At most $O(1)$ physical words contain varying fields per slot, at fixed machine word-width constants. If literal names are sparse, their binary lengths are still $O(\log N)$.

Number the private slots in their order of first touch on the actual execution. Group these discoveries into $h$ consecutive groups of $2s$. Write $A_j$ for the first $s$ slots in group $j$. Its first interval runs from just after the first $2s(j-1)$ discoveries (the initial state for $j=1$) through the $s$-th discovery of group $j$. Split instructions with several accesses into a constant number of substeps, carrying their temporary registers in the controller. Define

- $D_j$ as the number of work addresses whose contents at the end of this first interval differ from their contents at the beginning. This includes writes of zero that clear nonzero words.
- $R_j$ as the number of distinct slots in $A_j$ touched at least once *after* the end of that interval.

For every fixed correct deterministic SAT solver, there is one equal input and placement on which
$$
                D_j+R_j=\Omega(s) \qquad(1\le j\le h).
$$
Workspace and computation between successive accesses are unrestricted. For each changed address choose one of its genuine stores in its interval. For each returning slot choose its first later touch. The first intervals are disjoint; the sets $A_j$ are disjoint; and returns cannot be first touches. The complete execution therefore contains all $2N$ first touches and another $\Omega(N)$ actual memory accesses. Returns for different groups may take place much later and interleave. On a multiword record its later touch may read a different constituent word. The bound counts actual additional word accesses beyond the first touch of each record. A single compound instruction may both read and store.

## A deferred placement that still gives ordinary static inputs

For each string of left and right symbols, simulate the solver with empty private slots. In group $j$ assign its next $s$ left records, in logical index order, to the next $s$ previously untouched physical slots as they are first requested, then assign its $s$ right records in the same way. Repeated touches always give the original physical contents. If the solver halts early, fill any unclaimed slots with the remaining records in arbitrary order. Its entire execution is the execution on this one completed, immutable formula. On equal inputs early halting is impossible by the sensitivity of every record. The procedure defines a family of static inputs indexed by the two symbol strings. It gives the same execution whichever group is later examined.

Fix group $j$ and all symbols outside it to any equal private lists. Alice knows its left list $x\in[q]^s$, Bob its right list $y\in[q]^s$. The resulting SAT decision computes whether $x=y$, with the equality case unsatisfiable. Both parties can reconstruct the entire execution through group $j$'s starting point without messages. Alice now simulates its first interval. Before all its left records are assigned the computation cannot halt: the given prefix can still be completed to both outcomes by choosing the remaining symbols of this group. Alice sends the following information.

1. The subset of remaining physical positions used for $A_j$, using a public subset index of at most $\lceil\log_2\binom{2hs}{s}\rceil$ bits. She keeps the correspondence between those positions and their contents.
2. The controller and the $D_j$ changed address/value pairs relative to the beginning of the first interval. Its entire baseline is already known to Bob. With a fixed number of banks and $w=\Theta(\log N)$-bit addresses this costs $O((1+D_j)w)$ bits, including the count.

Bob can now simulate the rest. Previous groups' assigned slots are public. On the first return to any slot of $A_j$ he requests that slot's contents from Alice and retains the reply. Every other previously unassigned slot receives the next record of his own list or a later public group, in the prescribed order. All later work loads and writes are local, including visits to cells modified before this group. Publishing the verdict gives a deterministic protocol with transcript length at most
$$
       \left\lceil\log_2 {2hs\choose s}\right\rceil
                       +O\big((1+D_j+R_j)w\big).
$$
A halting run before reaching this particular group's starting point can simply publish its public verdict. The fixed equal outside lists also permit completion to an all-equal input, excluding such a halt.

Each equality transcript contains at most one pair $(x,x)$ by the rectangle property of a deterministic protocol: two distinct such pairs at the same leaf would place a mismatched pair there too. For $h=s$ the subset cost is at most $s\log_2 s+O(s)$, while the diagonal contains $q^s=2^{2s\log_2 s}$ entries. Hence for a sufficiently small solver-dependent $c>0$, at most a $2^{-\Omega(s\log s)}$ fraction of equal group lists can have $D_j+R_j<cs$, uniformly over the fixed other lists. Draw all diagonal symbols independently uniformly and apply the union bound over $h$ groups. Almost every such choice produces a single real execution meeting every inequality.

There is a complementary suffix guarantee on the same inputs. Let $K_j$ be the number of distinct work addresses read after the cut before their first post-cut overwrite there. Alice can send only $D_j$ initially. Bob obtains old work words on demand and retains all post-cut stores. If he has made $D_j$ such requests, Alice sends the full delta list, after which her help with work memory ends. The work-data cost is $O((1+\min(D_j,K_j))w)$ bits. The same diagonal count therefore forces $R_j+\min(D_j,K_j)=\Omega(s)$ simultaneously for every $j$. When $R_j$ is small this yields both genuine stores during the first interval and genuine loads after it. Some suffix loads may be shared across groups, so the disjoint sum above charges their interval stores.

The communication saving comes from naming a *set* of occupied physical slots. Sending the table mapping each slot to its symbol would already exhaust the diagonal entropy. The earlier genuine-transfer argument handles arbitrary time cuts while charging foreign values and information encoded by writers' addresses. Here the freedom to order clauses lets the proof count a net change in work memory or an actual return to an already discovered clause group, with disjoint costs across groups. [Earlier cut theorem and address-channel example](simultaneous-cuts-on-a-sat-execution.md)

## What preprocessing buys on the cycle

In the earlier single-cycle Horn lift with labels $A=(1,0,0)$ and $B=(0,1,0)$, the central bit counts pairs in which an $A$ appears before a $B$, modulo two. If $k$ of the $n$ labels are $A$ and their zero-based positions are $p_1,\ldots,p_k$, this count is
$$
       k(n-1)-\sum_i p_i-\binom{k}{2}.
$$
For even $k$ and even $n-k$ the product is central and the position parity sum is rotation invariant. Preprocessing a fixed successor cycle into its bipartition therefore supports *every* later choice of the $k$ red vertices by a parity query on their names. The index is one bit per vertex. In the layout with a public source slot, one can validate each row while traversing the cycle from its public start, returning the verdict on a first return at exactly $n$ steps. On the single-cycle promise this needs no return to a previously visited row. [Cycle verdict and equality lift](almost-every-row-of-a-horn-formula.md)

The shuffled equality path also has a linear-word-time solver. Validate its fixed format, collect the two indexed records of each link in arrays, and test all symbol equalities. A general solver can take over on malformed layouts. This costs $O(N)$ native operations on the family. The extra accesses above enforce a second additive cost at the scale of the packed scan. They do not establish a superlinear lower bound in encoded bits. [Finite simulation and exhaustive cut audit](../audits/shuffled_equality_reads_audit.py)
