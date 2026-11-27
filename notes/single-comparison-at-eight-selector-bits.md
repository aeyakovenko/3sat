# Six stored instructions with a single comparison at eight selector bits

On the dense eight-bit sign-plane SAT family, no program using at most five native data instructions followed by a single comparison gives the correct verdict on the 32 inputs listed below. Data instructions may use every three-bit ALU operation in the catalog, arbitrary direct or indirect LOAD and STORE, and unrestricted initially zero registers. Comparisons that write zero or one into a register count as ALU instructions. The final comparison may use either ordering of its operands, equality, signed or unsigned order, and either assignment of its successors to verdicts. [Family and full five-slot census](eight-bit-catalog-load-sites.md).

The inputs are integers $x=P+16M$ with $0\le P,M<16$. Their initial memory words are $x\bmod 8$, $\lfloor x/8\rfloor\bmod8$, and $\lfloor x/64\rfloor$ at addresses 0, 1, and 2. The SAT verdict is $(P\mathbin{\&}M)=0$ and $M\ne15$.

```
164 166 172 228  42  28  64  35
  5 194 138  33 150 220 139   3
 34 143 176  97 240 196  78  59
152  30  22 245  47  77 180 252
```

All three original words on the first input must be read. Rows 2, 3, and 4 respectively change one of those words and reverse the SAT verdict. Until the changed word is read, both executions agree. Overwriting the word first makes the two executions agree forever. The enumeration therefore discards a STORE to a still-unread original address on the first input and prunes a prefix with insufficient remaining steps to read those cells.

Each register takes the form of a vector of 32 values, one per input. A LOAD gathers one value per input from that input's current memory and a STORE updates those memory tables lane by lane. The search tries every available register and literal in both operand positions. It retains all earlier register values: arbitrary register names realize this convention, and it covers every aliasing program by renaming each write. A newly computed vector equal to an existing vector can be replaced by its earlier register or literal throughout the suffix, shortening the program on this test set. Identical ALU outputs at the same prefix therefore have one representative. A STORE leaving the memory unchanged on every test can likewise be deleted.

A shortest matching prefix must end in a register write used by its terminal comparison. A final unused register write or a final STORE could be deleted. Testing the new register against all prior registers and literals thus covers all shortest solutions. With zero through five data instructions, the respective numbers of enumerated prefixes are 1, 38, 1,850, 143,213, 1,820,811, and 6,165,596. The terminal condition is tested on 6,172,114 prefixes. Zero pass. These counts include searched prefixes at every depth after pruning.

This excludes every total six-site program with just one effective control comparison. With a single comparison site, the deterministic prefix from entry reaches that site. Each of its two successor paths then either leads to a constant verdict or returns to the same comparison. If any successor returns, at most one distinct verdict is reachable. A total program computing both verdicts therefore has a straight-line data prefix before its single control comparison. The earlier read-only bisimulation also extends from three to four fixed predicates: all multisets of four predicates among the 21 allowed types are covered by the same 427 intertwining relations. Thus six-site programs using only LOADs and branches fail even if they use four comparison sites and two LOAD sites. With five comparison sites and one LOAD site, the earlier sensitive-input argument applies at deadline eight. Six-site programs combining multiple comparison sites with ALU instructions or STOREs still require a separate analysis. [Extended bisimulation test](../audits/eight_bit_catalog_load_sites.py).

The executable exits with failure if a matching prefix is found. Compile with GCC or Clang vector extensions. [C++ checker](../audits/eight_bit_single_comparison_six_slots.cpp).

```
c++ -O3 -march=native -std=c++20 eight_bit_single_comparison_six_slots.cpp -o /tmp/eight-bit-prefix
/tmp/eight-bit-prefix
```
