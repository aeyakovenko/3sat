# What timely descriptions of a rate imply, and a converse counterexample

**Research journal, 24 November 2026.** Under linear SAT, absence of bounded-width clock crossings at an individual rate forces a shortage of timely program weight on its successive binary prefixes. The converse fails for actual native machines. I construct one computable rate at which the relative timely weight tends to zero at every sufficiently long prefix, and one efficient literal prefix-universal machine on which **every** positive exact-saving column has a random two-clock increment at that same rate, unconditionally. Time-bounded versus unbounded prefix weight is related to Bennett depth. The cutoff and the uniform upper and lower clocks here are specified explicitly. [Bienvenu, Delle Rose and Merkle on relativized depth](https://iris.uniroma1.it/bitstream/11573/1713789/1/relativized-depth.pdf)

## The sufficient condition, counting all timely headers

Fix an ordinary efficient optimal prefix machine P, its unbounded complexity K₀, and an efficient native prefix machine V with complexity K. Let E(D) be a fixed prefix code of length O(log(D+2)), and write m(D,σ) for the integer with binary representation 1 E(D) σ. It determines (D,σ) and, at fixed D and h=|σ|, is Θ_D(2ʰ). For fixed large c let W(D,σ) be the total weight of exact P-programs that print the canonically encoded pair (D,σ) within 2ᵐ steps using at most m−D−c bits. Negative length cutoffs give zero. This rational weight is computable.

Let ω be a binary stream, x=3+Σᵢωᵢ2^(−i) and σ=ω↾h. Let Tₓ(m)=2^⌊xm⌋ and tₓ(m)=max(1,⌊Tₓ/mᵃ⌋). Under linear SAT there is a constant C such that absence at m=m(D,σ) of **all** words satisfying

    m−D−H < K(y) ≤ K_Tₓ(y) < m−D ≤ K_tₓ(y),     |y|=m,                 (1)

implies W(D,σ)≤C2^(−H−K₀(D,σ)) for all sufficiently large h at each fixed D and all a above a fixed constant. Thus, if the ratio W(D,ω↾h)/2^(−K₀(D,ω↾h)) exceeds C2^(−H) infinitely often, some one of the H−1 possible exact savings occurs infinitely often. This test uses the displayed integer lengths, generally different from the powers of two in the [rate-law result](rate-cylinder-laws.md).

To prove it, read any contributing P-name p, obtaining the same pair z=(D,σ) and length m. In a fixed length-lexicographic order enumerate the other contributing names for z. Allocate to p a consecutive block of 2^(m−D−c−|p|) ranks after the blocks of all its predecessors. The total number of ranks is at most 2^(m−D−c) by Kraft. Enumeration, bounded simulations and arithmetic cost at most 2^(2m)poly(m). Read m−D−c−|p| raw bits and select the corresponding missing-word rank at the left endpoint v of the rate cell of σ. At most 2^(m−D−1) m-bit words have names shorter than m−D even without a clock, so all ranks fit. One fixed sufficiently large c pays the header, including a self-delimiting specification of c when needed.

The early cutoff is ⌊Tᵥ/mᴬ⌋. The sorted-list bounded-transcript verifier under linear SAT unpacks every allocated rank by Tᵥ for one fixed sufficiently large A. The unknown tail of ω changes the deadline exponent by at most m2^(−h)+1=O_D(1), eventually below log₂m. Hence a≥A+3 makes tₓ≤⌊Tᵥ/mᴬ⌋ and Tₓ≥Tᵥ throughout the closed rate cell. [Counting and native runtime](moving-saving-cutoffs.md)

The allocated words have mass 2^(−c)W(D,σ) in units 2^(D−m) per word. The total such mass of all m-bit words with K(y)≤m−D−H is at most 2^(−H)Σ_{|y|=m}2^(−K(y))≤C₁2^(−H−K₀(D,σ)). Here the length distribution is a lower semicomputable semimeasure and m identifies z. If the first mass exceeds the second, at least one word meets (1). This accounts for the full timely header weight even when no single p pays a significant fraction.

## A computable path with negligible timely header weight

The counterexample uses the same fixed reference P and c. Let M(D,h)=Σ_{|σ|=h}W(D,σ). Each reference name outputs only one pair, hence M(D,h)≤C₂2^(−K₀(D,h)) by the length-marginal argument. At level h forbid strings σ with W(D,σ)>M(D,h)/⌈log₂(h+4)⌉ for any D between 1 and ⌊log₂log₂(h+4)⌋. The finite lists are computable and have O((log(h+4))²) members per level by counting even when some M(D,h) are zero.

The union of forbidden cylinders at levels beyond N has fair-coin measure O((log(N+4))²2^(−N)). Start sufficiently late that the closed set P₀ avoiding the lists has measure greater than 3/4. There is a computable path β in P₀ with the following extra clock guarantee at endpoints hⱼ=2ʲ:

    printing β↾hⱼ takes at most 2^(2^hⱼ · poly(j)) steps.                 (2)

To construct it, at stage j extend the previous chosen string to length hⱼ. Maximize its conditional surviving proportion when lists are checked only up to Nⱼ=hⱼ+⌈8log₂(j+2)⌉+c₀, breaking ties lexicographically. For any length-hⱼ cylinder the omitted conditional probability is at most 2^hⱼ times the unconditional tail bound, which is less than 1/(16(j+1)²) for a fixed large c₀. The maximal truncated proportion is at least the previous cylinder's true surviving proportion by averaging over its children of the specified depth. The accumulated errors leave true proportion greater than 1/2 in every chosen cylinder. Closedness gives β∈P₀.

At levels u≤Nⱼ the required integers m(D,σ) are at most 2^u poly(log log(u+4)), by the small upper bound on D. Enumerating every bounded program and simulating it requires 2^O(m)poly(m) time per context. Computing the lists, finite subtree counts and the lexicographically first maximizing extension, including earlier stages, fits the bound (2). The construction promises that clock at the endpoints; computability at intermediate h follows by proceeding to the next endpoint.

For every fixed D and all sufficiently large h we have

    W(D,β↾h)/2^(−K₀(D,β↾h)) ≤ C₃/⌈log₂(h+4)⌉.                         (3)

Indeed β is computable, so K₀(D,β↾h)=K₀(D,h)+O(1), and β avoids the corresponding forbidden cylinders.

## An actual universal machine with witnesses at this rate

Put x=3+.β in binary. Use the [record construction for exact savings](programmable-clock-spectrum.md) with a fixed generic native interpreter behind a prefix of B ones. On a disjoint 0 branch read q printing d≥1, k=|q|, then a conditional name p with auxiliary information (d,k), n=|p|. Let r be a uniform injective code identifying the parameters, names and their runtimes, exceeding those lengths and runtimes. Set h=2ʳ and M=h2ʰ, a power of two. Read M−d−1−k−n raw bits and give each such suffix a distinct M-bit output, padding the front with zeroes. For this tuple the complete name has length M−d, and altogether these names have weight 2^(−1−k−n). Distinct tuples give distinct output lengths.

Compute β↾h using (2) in 2^(2ʰ poly(r))=2^o(M) time. If v=3+.β↾h, publish after a constant fraction of 2^⌊vM⌋ steps, using the bounded-frame binary-tree traversal of the cited construction and fixed delay constants. This is timely by Tₓ(M). Also (x−v)M≤h and 2ʰ/M=1/h, so even Tₓ(M)/M is eventually smaller than the publication time. All larger a preserve this crossing. The large setup time occurs on the special branch. The fixed generic prefix still simulates its underlying interpreter efficiently.

At each d choose shortest q and let p realize successive strict runtime records at its length for its auxiliary input. The record argument gives K₀(M)≥k+n−O(1) with a uniform constant. The underlying generic interpreter has total program mass at length M at most C₄2^(−K₀(M)); the prefixed generic branch scales it by 2^(−B). Choose B once so it accounts for at most half the exceptional cohort's weight. At least half that cohort's words then have no generic name of length at most M−d, at any time. The unique special name for each of them has that length. At these unbounded M the selected words have K(y)=K_Tₓ(y)=M−d<K_tₓ(y) for every fixed a≥1. Since x is a computable real, for this fixed x the deadline exponents are computable (direct rational arithmetic for rational x, sufficient precision at each nonintegral product otherwise). The exact-d increment sums have computable terms, infinitely many at least 2^(−K(y)−1). All their sums are therefore Martin-Löf random. [Computable-series term criterion](https://arxiv.org/pdf/1110.5028)

In particular the deficiency (3) alone is insufficient evidence of even one missing exact-saving column. The [literal residue interpreter](exact-saving-blocks.md) can instead make all nonmultiples of a fixed modulus vanish at the very same rate and with the same separate reference P. The timing and compiler of the native machine are additional information needed for an inverse test.
