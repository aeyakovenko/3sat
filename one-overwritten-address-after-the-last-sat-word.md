# One overwritten address after the last SAT word

Let a deterministic program receive its last previously unread physical input word in the aligned, single-memory RAM of the butterfly construction. Treat the cut registers, including that reply, as known. Every later `LOAD` marks its destination, copies preserve the mark, and numerical instructions produce unmarked values. For one suffix define

* $c$ as the number of noncopy numerical instructions and comparison branches consuming a marked operand,
* $m$ as the number of stores with a marked address or a marked payload,
* $D$ as the set of **distinct numerical word values** appearing as addresses or payloads of all other stores.

For a solver whose prefixes on the butterfly files take $O(N\log^K N)$ time for fixed $K$, there are arbitrarily long proper DIMACS files differing in one bit, with opposite verdicts, such that **each suffix** satisfies
$$
                     c+m+|D|=\Omega_K(\log N/\log\log N).
$$
The constant may also depend on the program. It suffices to assume this near-linear bound on prefix storage in words. The claim uses the butterfly construction's word width $w=1024\lceil\log_2(N+2)\rceil$, fixed terminal verdicts, and separate operations. A store repeated a million times with the same two unmarked values contributes at most two to $|D|$. In particular, if a suffix performs few marked operations, its unmarked stores must involve many different numerical words. [Static simulation and physical butterfly files](processing-butterfly-queries-after-the-last-physical-word.md)

## Saving probes by caching labels

Write $f$ for the cut memory with the unknown last input cell temporarily cleared. Start the query simulation by installing the actual word in its slot as a known correction. The sparse functional-graph index gives an orbit label for any word and supports retrieving $f^j(u)$ in constant probes. The labels of $u,v$ suffice to test $f^j(u)=v$ without another probe, including the default zero outside the finite support and its image. Retain every retrieved label in free local query storage.

For each marked operand, record its known origin and the times of successive loads producing the current value. A copy only forwards this history. To resolve an operand, obtain its origin label and replay the load times locally. At each load, test the current old-memory orbit point against earlier store addresses using their cached labels. Use the latest matching store before that load if one exists, restarting the orbit at the stored payload with its already cached label. Otherwise advance the orbit exponent. One final old-orbit lookup obtains the numerical result. This costs $O(1)$ probes per resolved operand regardless of the number of earlier stores.

At an unmarked store both numerical endpoints are already available. Obtaining and caching the missing endpoint labels costs $O(|D|)$ probes over all such stores. A marked store resolves at most two operands and inserts at most two new labels, costing $O(1)$ per store. A counted numerical instruction or branch resolves at most two operands. All other operations can be emulated without probes. Thus the suffix costs $O_P(1+c+m+|D|)$ static probes, including the initial correction and controller. The index takes $O_P((S+1)\log(S+2))$ words when $S$ cut cells are nonzero. Simulating the two complementary tags one probe at a time lets the first returning program decide reachability. The butterfly lower bound forces the smaller of the two suffix charges to be $\Omega_K(\log N/\log\log N)$ for some database and source/sink query. [Pătraşcu, section 5](https://arxiv.org/pdf/1010.3783)

## Both kinds of endpoint are necessary

There are two globally correct SAT programs taking $O(N)$ time on these same explicit files. Both use just one marked comparison and zero marked stores in the interesting case where the withheld word is the query. Their unmarked stores pay the bound in different ways.

Scan the slots in address order and hold the final word. The final slot has no fixed public rows. Check the preceding canonical packets, build the indicated data structure, and retain the small amount of metadata in cut registers. If the query already appeared, the sole missing edge key is known, so compute both possible answers and canonical final words before the cut. Compare the actual last word with those two known words and return its answer on a match. If the query is last, the prefix contains all graph data. Decode and validate its two endpoints and tag directly from the delivered register with shifts, integer arithmetic, and counters. On a family member this takes $O(\mathrm{polylog}\,N)$ steps without reading old memory. The source and sink determine the $d$ edge addresses of their path, including edges that were deleted. These addresses can be generated in registers from the endpoints and public counters. They are all distinct. Reserve addresses $0,1$ for the techniques below and represent graph edges at distinct addresses above 1. Cache the originals for fallback or use an offset to avoid overlap with the working array. On an invalid layout invoke a complete SAT solver.

**One store address, $d$ payloads.** Keep the presence bit of edge $i$ at its public address $a_i>1$, and initialize $M[0]=0$ before the cut. Start $r=1$. For each edge address $a_i$ on the query path execute
```
STORE M[1] ← a_i
LOAD  r ← M[r]
LOAD  r ← M[r]
```
A zero remains zero. Starting at one, the two loads yield the presence bit at $a_i$. Thus after all $d$ stages, $r$ is the reachability bit. Compare it with the supplied tag to return the SAT verdict. The sole store address is 1 and all $d$ payloads are different. The two pointer loads at a stage and the final comparison are its only native uses of the marked data; the loads carry no charge in this measure.

**One store payload, $d$ addresses.** In preprocessing make the deleted edges into one linked list in the cells at their public addresses. End it at the self-loop 1. Set $M[0]=0$ and save the head, or 1 if the list is empty. After the last query word, write 0 to the $d$ path-edge addresses. Follow the list from the saved head for $E+1$ loads, where $E$ is the number of possible edges. If the path contains a missing edge, the traversal reaches the first one in list order and then stays at zero. Otherwise it stays at one after the list ends. Compare this single resulting marked register with the tag. All payloads equal zero. Only the destination addresses vary. The $O(E)$ post-cut loads still fit within the $O(N)$ total time on the family.

These two programs exclude a bound using only marked computations and marked stores. Omitting either endpoint type from $D$ also fails. The first implementation spends only $O(d)$ steps for the actual path queries after decoding the final word. The second obtains its constant payload alphabet by spending up to $E+1$ pointer loads. The lower bound counts the changing words in the updates while allowing both implementations. It adds one suffix charge to a physical scan. The audit checks 75,000 simulated step prefixes against the cached-label charge and runs both endpoint constructions on 231,872 signed butterfly queries. [Finite marked-execution audit](one_overwritten_address_audit.py)
