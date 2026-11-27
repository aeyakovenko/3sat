# How many data/query boundaries does a short SAT encoding of equality need?

Suppose a proper explicit DIMACS encoding $F(a,x)$ of equality has at most $N$ physical bits. After a database header of $b$ bits is supplied, its body is a concatenation of $k+1$ pieces, each produced by the database or the query, in a publicly specified order. Lengths and exact cut positions may be included in the header, or lengths of database pieces may be sent with their summaries. Pieces can split a literal, a long decimal name, a clause, or a run of whitespace. Assume the usual comment-free clause body with canonical positive decimal names and a public or separately delimited DIMACS header, and that every cross-completion is a valid file with the promised semantics.

With unlimited preprocessing and local calculation the equality decision has a worst-case deterministic query algorithm using
$$
 O\!\left(1+\frac{b+N/\log(N+2)+(k+1)\log(N+2)}{W}\right)
$$
probes to $W$-bit cells. In particular one contiguous data half followed by one contiguous query half has the same order of static upper bound as separated clauses, **even when an arbitrarily long variable name crosses the cut**. The two-word mixed-name construction attains the other endpoint at $\Theta(N/\log N)$ boundaries. [Separated-clause result](the-static-ceiling-for-equality-encoded-as-sat.md) · [Mixed-name construction](a-common-sat-pair-with-a-name-across-each-word-boundary.md)

## An assignment that composes across a boundary

Let $v=O(1+N/\log(N+2))$ bound the number of distinct names occurring in a file; the first occurrence of each long name pays for its length. On the positive diagonal $F(a,a)$ take any actual satisfying assignment. Choose a field of prime order $p$ between $8(N+2)^3$ and $16(N+2)^3$, fixed publicly at this length. Encode a string of decimal digits as a polynomial with coefficients 1 through 10 in printed order. This leading coefficient is nonzero. Two distinct digit strings of length at most $N$ give different polynomials, and their difference has at most $N$ roots. Some evaluation point $\alpha$ separates every pair of names on this diagonal, since there are fewer than $Nv^2<p$ bad points in total. The hash of a concatenation can be recovered from the two hashes and the length of the second piece:
$$
 H(uv)=H(u)\alpha^{|v|}+H(v)\pmod p.
$$
Use canonical spellings on each valid completed file, so numeric aliases cannot give inconsistent values. [Polynomial fingerprint methods](https://didawiki.cli.di.unipi.it/lib/exe/fetch.php/bio/kr87.pdf)

Fix a length-dependent list of total assignments on the $p$ hash values realizing every prescribed pattern on any $v$ or fewer distinct values. Such a list of at most $2^v O((v+1)\log(p+2))$ assignments exists: a random assignment realizes any single pattern with probability at least $2^{-v}$, and there are at most $(2p+1)^{v+1}$ patterns. An index costs $v+O(\log(N+2))$ bits. Finite exhaustive construction and selection are permitted in the static model. An explicit polynomial-time lookup alternative from a supplied model is also available. [Universal sets](https://users.cms.caltech.edu/~schulman/Papers/splitters.pdf) · [Explicit DIMACS model seeds](succinct-evaluation-of-a-given-dimacs-model.md)

The chosen assignment index and $\alpha$ define one total truth function $\sigma$ on **every** numerical name by hashing and applying the indexed assignment. It agrees with the selected diagonal model. Other files can cause hash collisions; the resulting values still form a single legal assignment. Accepting a query after evaluating all of $F(a,x)$ under this $\sigma$ therefore proves $a=x$ exactly.

## Summarizing an arbitrarily long old piece

For a piece consisting entirely of a single uninterrupted token fragment, store its digit hash, digit length, and the locations of any lexical sign or delimiter at its ends in constant many $O(\log N)$-bit fields. Under the valid-completion assumption a minus sign, if present, can only occur at the beginning of a signed token. Retain the first digit and whether the fragment is the single digit zero, to distinguish the clause terminator. A wholly whitespace piece needs only a separator marker.

For a piece containing separators, handle its potentially unfinished first and last tokens with the same records; retain whether those edge fragments touch across the piece, and whether it starts or ends on whitespace. The intervening full tokens have already determined values under $\sigma$. Summarize their action on the two Boolean parser bits “all completed clauses passed” and “a literal of the current clause is true”. A true literal sets the second bit, a false literal preserves it, and a token 0 ANDs the second bit into the first and clears the second. This transformer has constant size. It also handles adjacent or trailing whitespace and the empty sequence. Equivalently one may summarize every whitespace-containing piece by its prefix before its first separator, its strict internal tokens, and its suffix after its last separator; empty prefix and suffix are permitted.

The query algorithm appends these summaries and the known raw query pieces in order. It keeps the unfinished token, joining consecutive fragments by the hash identity; its signed truth value is only used when an actual separator or end of body is reached. Thus the internal parser transformer is applied only between complete tokens. Starting from the initial two bits and flushing the final token yields the truth value of the whole clause body under $\sigma$. A finite audit compares the two-bit transformation with direct literal evaluation on 12,288 exhaustive split/assignment cases, 500 longer clause bodies, a 5,000-digit name crossing over a thousand pieces, and 100 queries sharing stored diagonal summaries. [Executable fragment and parser check](../audits/dimacs_piece_fingerprint_audit.py) A single physical name may span *several* pieces. Each database piece costs only $O(\log N)$ bits regardless of its byte length.

The data representation consists of the base header, diagonal assignment seed, and at most $k+1$ old-piece summaries. Read it once and evaluate the query locally. Crucially this algorithm uses the model only to *verify the diagonal*. If any cross-completion also passes, it is a satisfying assignment for that actual cross file, which by the assumed encoding property proves equality.

The same bound on bits applies to the logarithm of the number of distinct databases. Equal descriptions would have the same query-side algorithm accepting exactly the same singleton. For a diagonal domain with $D$ bits of entropy this gives the necessary inequality
$$
 D \le b + O\big(N/\log(N+2)+(k+1)\log(N+2)\big).
$$
In particular a small directory and a single huge straddling name cannot encode $\Theta(N)$ diagonal bits. Conversely packed independent comparisons in $\Theta(N/\log N)$ different straddling names do encode that much.

## Interpolation and its time interpretation

For a word-budget parameter $M$, put $\Theta(M)$ binary coordinates into separate banks of data and query clauses by pinning the same variable from both strings. Use false anchors to make each pin a proper ternary clause. These give $\Theta(M)$ diagonal bits at length $\Theta(M\log M)$. Add $s$ mixed-digit coordinates for $0\le s\le M$ using an alphabet $K=10^{\lfloor(\log_{10}M)/4\rfloor}$. A public $O(K^2)$-row dictionary forces each mixed name true exactly on equal symbols; pin the used mixed name at every added coordinate. The total physical length remains $\Theta(M\log M)$, and at most $2s+O(1)$ switches of ownership suffice. Allocate static scaffold bytes to either neighboring owner; every mixed coordinate contributes precisely one name with a data prefix and query suffix.

The combined separated and mixed formula is satisfiable exactly on equality of the entire input. It has $2^{\Theta(M)+s\log_2K}$ diagonal databases. The ordinary static transcript argument on these diagonals gives a worst-case lower bound $\Omega((M+s\log M)/\log M)$ with logarithmic words and polynomially many static cells. Therefore the scale $N/\log^2 N+s$ of the upper bound is attained throughout the range, up to constants. It concerns static equality queries; local computation between probes has unrestricted time.

There is a separate elementary restriction on summing boundary counts over one execution. Color each aligned input word by whether its original value has ever been read. For any adjacent pair, their boundary is exposed after the first one's first read and closes after the other's. It can open at most once on a run, regardless of later reads or writes. A long sequence of cuts may exhibit the same exposed boundaries repeatedly. Across disjoint intervals there are only linearly many distinct opening events in the number of input words. This observation uses the first-read definition; it does not bound the native time needed to compute with the values.
