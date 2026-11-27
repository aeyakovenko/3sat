# Counting paths in an explicit SAT reduction

The linear-time target makes a logarithmic factor in the length of a reduction decisive. Williams observed that writing one fresh variable per simulated step costs Ω(T log T) bits with conventional names. Can a compiler preserve the accepting paths while using fewer distinct variables, or cover the paths with many smaller SAT calls? This calculation allows completely different output formulas, unused declared variables, and a separate variable namespace for every call. [Williams, section 1](https://people.csail.mit.edu/rrw/qbf-lower-bd.pdf)

## A sharp test for additive splitting

Consider a machine on unary input of length g that guesses g bits, retains their OR in a running flag, and accepts iff the flag is set. It takes O(g) steps and has M=2ᵍ−1 accepting paths. Its decision language on these inputs is trivial. Use #F to denote the number of satisfying assignments over the v variables declared by a formula, including the unused ones.

Fix a constant d≥1. Allow a nonempty list of width-at-most-three CNFs of bit lengths Lᵢ with arbitrary nonnegative counts Aᵢ=#Fᵢ. Require only that Σᵢ Aᵢ be a positive integer multiple of M. An exactly parsimonious partition is a special case. Indices and headers below are explicit binary integers, and each output has its own header declaring v. The minimum possible value of Σᵢ Lᵢᵈ has the following asymptotic orders.

| Literal identifier format | Minimum charged budget |
| --- | --- |
| Self-delimiting binary index of length Θ(log(j+2)) for identifier j | Θ(g (log g)^(d−1) log log g) |
| Every identifier has length Θ(log(v+2)) fixed by its header | Θ(g (log g)^d) |

For these statements a header costs at least the binary length of v and at most O(log(v+2)+log(number of clauses+2)) bits. Each clause has constant delimiter and sign overhead in addition to its identifiers. A list is charged separately for every occurrence of each output. The quantity Σᵢ Lᵢᵈ is the advertised time budget of a degree-d SAT solver on this list. An individual solver can run faster on these particular inputs.

**One formula.** If u distinct variables occur, A=2^(v−u)B for an integer 0≤B≤2ᵘ. A positive multiple of M has odd part at least M, so representing it with one formula takes u≥g. The distinct names alone cost Ω(g log g). One g-literal OR matches this length, as does its width-three conversion using a chain of binary OR gates with unique auxiliary values and its output pinned.

**Lower bound for any number of formulas.** Write w(z) for binary popcount. Every positive multiple of 2ᵍ−1 has w(z)≥g. To see this, write it as a sum of powers of two, reduce the exponents modulo g, and replace pairs of equal powers by one power at the next exponent modulo g. Each replacement preserves the value modulo M and reduces the number of summands. At termination a nonempty set of distinct residues represents a positive integer at most M divisible by M. All g residues must be present. This is the known sturdiness property of Mersenne numbers. [Clokie et al.](https://arxiv.org/abs/2002.02731)

Set h=⌊g/2⌋, Z=Σᵢ Aᵢ, and let q be the list length. The integer ⌊Z/2ʰ⌋ has at least g−h one-bits. It equals Σᵢ⌊Aᵢ/2ʰ⌋ plus a carry between 0 and q−1. Popcount is subadditive, so

    g−h ≤ ⌈log₂(q+1)⌉ + Σ_{i: vᵢ≥h}(uᵢ+1).

Indeed Aᵢ≤2^vᵢ, and w(Aᵢ)≤uᵢ+1 from the unused-variable factorization. If q≥2^(g/8), the outputs already cost exponentially many bits. Otherwise the sum over these high-header formulas is Ω(g). Each such formula costs Ω(log g) bits for its header. Separately naming uᵢ variables costs Ω(uᵢ log(uᵢ+1)) in the first encoding. Together these charges give Lᵢ=Ω((uᵢ+1) log log g): if uᵢ≥√log g use the name charge, and for smaller uᵢ use the header charge. In the second encoding Lᵢ=Ω((uᵢ+1) log g). Multiply either bound by Lᵢ^(d−1)=Ω((log g)^(d−1)) and sum.

**Matching lists.** For the first encoding split the binary expansion of M into consecutive blocks of k=⌈log g / log log g⌉ ones, with a shorter final block when needed. A block of k′ ones beginning at exponent a is 2ᵃ(2^k′−1). Construct the k′-variable OR chain above using just the lowest O(k′) indices. Declare a additional unused variables in the header. The number of assignments is exactly the block value. Each output costs O(log g+k log(k+1))=O(log g) bits, and the number of outputs is O(g log log g / log g). For the second encoding use one block per exponent a, a single positive unit clause and a unused variables. Its 2ᵃ assignments cost O(log g) bits to describe.

Thus a uniform compiler preserving a common multiplicity in a sum of nonnegative model counts cannot guarantee linear total bit length even on this elementary g-step machine. An ordinary many-one SAT reduction only has to preserve whether there is a path. On this machine a constant satisfiable formula suffices. The obstruction concerns the stronger compiler specification.

## Retry with signed arithmetic on unambiguous queries

A pair of terms 2ᵍ−1 already escapes the preceding bound if subtraction and a binary exponent are allowed. There is a way to use such cancellation on actual hierarchy inputs without writing exponentially long integers. Suppose a uniform compiler emits SAT queries Fᵢ and a division-free straight-line integer circuit C with s gates using constants 0, 1, addition, subtraction and multiplication. Its input gates are the answer bits [Fᵢ is satisfiable]. Assume its output A equals the number of accepting guess strings of a particular machine, so 0≤A≤2ᵍ. Unambiguous query formulas also allow their model counts to serve as these bits. Repeated squaring implements explicitly named powers of two with logarithmic gate overhead in the exponent. Intermediate integers can be arbitrarily larger than A.

There exists an integer 2≤m≤2g+1 for which A mod m is nonzero whenever A>0 and g≥1. Let D=lcm(1,…,2g+1). Expanding the polynomial xᵍ(1−x)ᵍ and integrating term by term shows that D times its integral on [0,1] is a positive integer. That integral is at most 4^(−g), so D≥4ᵍ. An A between 1 and 2ᵍ cannot be divisible by every candidate. A nondeterministic recipient guesses m, evaluates C modulo m, and accepts on nonzero. Every intermediate register now needs O(log(g+2)) bits. This uses the familiar small-modulus principle for integer circuit zero testing with the stronger promise on the final value. [Allender et al. on integer straight-line programs](https://www.cs.rutgers.edu/~allender/papers/slp.pdf)

For a deterministic recipient using the hypothetical SAT solver, first obtain the query answer bits. Then construct one further ordinary SAT query asking for a valid modulus with nonzero residue. Put b=⌈log₂(2g+2)⌉. Using long division for modular reduction, the query has P=O((s+1)b² log((s+2)(b+2))) encoded bits up to fixed encoding constants, and can be built within that order of word operations once C is available. The SAT simulation costs O(R + Σᵢ Lᵢᵈ + P + Pᵈ), with R charging the uniform compiler and reading its output. The bound on A is a semantic premise about the compiler. No certificate of correctness for an arbitrary guessed C has been supplied. In particular, existence of a short numeral circuit for a single A provides almost no evidence of effective construction. Every integer up to 2ᵍ has a nonuniform circuit with O(g/log g) gates: precompute all base-2ᵏ digits by increments for k=⌊(log₂ g)/2⌋, then use Horner evaluation on the hardwired digits of A. The descriptions of those digit choices may occupy Θ(g) bits.

**Test on a compressed generating function.** For a subset-sum instance with g positive weights aᵢ, target t and B=2^(g+1), build

    Z = ∏ᵢ(1+B^(2aᵢ)) + (B−1) B^(2t).

Binary powering gives a signed arithmetic circuit of size O(g+log(g+2)+log(t+2)+Σᵢlog(aᵢ+2)) counting arithmetic gates. Before the addition, base-B digit 2j equals the number of subsets summing to j and is less than B. The odd digits vanish. The addition produces a carry into digit 2t+1 exactly when some subset sums to t. Consequently the bit at position k=(g+1)(2t+1), starting at zero, is the answer. This is a small, uniformly obtainable circuit with the decision bit embedded in a possibly enormous integer. Related encodings underlie the hardness of BitSLP. [Allender et al., Proposition 2.4](https://www.cs.rutgers.edu/~allender/papers/slp.pdf)

Can the small-modulus test recover such a bit? Consider any exact certificate procedure that accesses an otherwise unknown Z in [0,2^(k+1)) only through residues. On a successful certificate for bit k of Z=2ᵏ being one, let D be the least common multiple of all queried moduli. If D≤2ᵏ, the smaller nonnegative integer 2ᵏ mod D has the same answers and bit k equal to zero. Replaying the same certificate gives the same transcript even if the moduli are chosen adaptively. Thus D>2ᵏ, requiring the sum of their binary logarithms to exceed k. This shows exactly what breaks when the desired bounded scalar is replaced by a selected bit of a large packed table. Inspection of the straight-line program itself can reveal additional information.

The positive question is whether a hierarchy verifier admits a uniformly constructed signed counting circuit with total encoded query budget and construction time below its excluded clock. The exact bounds above invalidate one nonnegative counting route to that goal. They allow signed cancellation, unambiguous decompositions, and purely decision-preserving reductions to be investigated separately. No lower bound on the running time of unrestricted SAT follows here.
