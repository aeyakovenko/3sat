# Can two SAT input words be compressed before the third arrives?

In the [eight-bit selector catalog](eight-bit-executed-clock.md), consider a program that loads two distinct input words in a fixed order, applies a straight-line sequence of register ALU operations, and retains one three-bit result. It then loads the third word and decides from that word, the retained result and immediate literals. The only memory accesses in this class are the three prescribed loads. The prefix leaves no input-dependent branch state or scratch contents. The decoder can branch freely and use additional ALU operations. **No such program takes eight or fewer executed instructions on all 256 inputs.**

Fix two words to particular values and list the SAT verdicts in order of the third word's possible values. This is the residual truth table. Two different residual tables must produce different summaries because the decoder receives identical later inputs when the third word is the same.

| Last word | Number of distinct residual truth tables | Possible summaries in one word |
| --- | ---: | ---: |
| $a$ | 9 | 8 |
| $b$ | 10 | 8 |
| $c$ | 6 | 8 |

For $a$ or $b$ last, even an arbitrarily expensive one-word encoder fails. For $c$ last, the distinct accepted subsets of $\{0,1,2,3\}$ are $\varnothing$, $\{0\}$, $\{0,1\}$, $\{0,2\}$, $\{0,1,2\}$, and the whole set. The set $\{0,2\}$ requires at least two executed decoder instructions on some input. Once the summary is fixed, a single comparison on $c$, the summary and constants can express only a singleton or its complement, a prefix or suffix, or a constant. Signed and unsigned orders coincide on the four possible values of $c$. Thus a program with total clock eight, three loads and a fixed straight-line encoding prefix can spend at most three ALU operations computing the summary.

The [exhaustive C++20 check](eight_bit_residual_summary_audit.cpp) represents every candidate word by its values on all 64 ordered pairs $(a,b)$. A candidate is sufficient precisely when its value classes each lie inside a single residual-table class. Starting with both words and all eight immediates, one ALU gives 283 distinct new tables. For each such table the checker adjoins every nonredundant second result, including computations independent of the first. In a shortest three-operation expression the third operation must use the second result. The checker therefore tries that result on either side of every opcode with every available operand, including itself. It checks 53,302,080 terminal candidates counting repetitions. None are sufficient, and neither is a shorter expression. The opcode library includes saturating and modular shift counts, signed and unsigned comparisons, both rotations and all arithmetic and Boolean operations from the original census.

Run `c++ -O3 -std=c++20 eight_bit_residual_summary_audit.cpp -o /tmp/eight-bit-summary` and `/tmp/eight-bit-summary`. The checker first compares the bit-parallel implementation of every opcode against scalar evaluation on all 64 native operand pairs.

An eight-step program for the unrestricted catalog, if one exists, can keep multiple earlier words or partial results live, use input-dependent branches while reading them, or exploit indirect memory. The general executed-time bounds remain seven through nine. [Unrestricted census and the separate prefix-code obstruction](eight-bit-executed-clock.md)
