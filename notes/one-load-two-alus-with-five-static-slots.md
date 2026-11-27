# Five slots with one LOAD and two ALUs on the four-word SAT catalog

No program with one LOAD, two arithmetic or logic slots, and two fixed-target binary branch slots decides the dense 16-bit sign-plane SAT catalog. **The result allows arbitrary running time.** It applies to the four-bit instruction set in the earlier native-clock audit. There is no memory-write instruction in this allocation. The two ALUs may implement any listed arithmetic, bitwise, shift, rotation or comparison operation, overwrite the same register, or overwrite the LOAD destination. [Machine and target](exact-clocks-for-two-word-sat-inputs.md)

Use the 324 positive inputs with all four words at least four and $P_i\mathbin{\&}N_i=0$. Changing any single word to 15 creates a conflict with its nonzero partner, so every original word must be read on each execution. The sole LOAD must repeat and use a register as its address. At least one ALU must also repeat. Otherwise at most two new numeric values could be produced on the run; the set of attainable low register values lies in zero and those two results. This cannot furnish all four input addresses. In particular fixed control flow without a cycle fails.

The two branch sites, two terminal verdicts and reachability force the unique-cycle form proved in the previous note. When both ALUs are in the cycle, the continuing data schedule is a repeated permutation of the three data slots. When just one ALU is in the cycle, the other may be in a prefix with no LOAD. We grant it the ability to initialize its destination to any one of the sixteen literals. The cycle then alternates LOAD and ALU in either order. If instead the nonrepeating ALU is in a suffix, its result and any ensuing comparison are deterministic functions of the registers at exit. An arbitrary stopping rule on the register tuple includes this ability. In this case use the cycle without initialization, which is included by choosing zero. Two early constant-register branches cannot distinguish inputs. [Unique-cycle reasoning and the stopping-rule theorem](one-load-one-store-with-five-static-slots.md)

Name register 0 as the LOAD destination. Name the two ALU destinations in order, assigning new register names by first occurrence. This gives the five partitions in the table. A register never written remains zero. If the LOAD address register is never written by an ALU, then it is either fixed at zero or is the LOAD destination operated as a pointer. On the sensitive inputs the latter simply follows $0\to P_0\to0$ in immutable memory, since $P_0\ge4$. Hence every useful address register is an ALU destination.

For each destination partition the program enumerates every pair of semantic ALU tables and each eligible LOAD address register. A table on $r$ registers is determined on all $16^r$ tuples, for $1\le r\le3$. For each continuing schedule the first test requires all four reads on every sensitive input. For each survivor, consider the sequence of pairs consisting of a cyclic data phase and the **entire** current register tuple, after each data instruction. The verifier may apply an arbitrary stationary rule returning YES, NO or continue at every observation. This strictly enlarges the options of the two binary branch sites. Repeating the complete register state at the same phase certifies repetition forever because the memory is read-only. The shared stopping-rule test advances equal observations forced to continue by opposite desired answers. [Stopping-rule implementation](../audits/five_slot_stopping_rules.hpp)

| ALU destinations | Distinct tables per ALU | Schedules | Pass required reads | Fit all 16 binary verdicts | Also fit 256 low verdicts | Also fit mixed verdicts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 0, 0 | 295 | 541,030 | 0 | 0 | 0 | 0 |
| 0, 1 | 607 | 4,499,084 | 37,248 | 11 | 0 | 0 |
| 1, 0 | 607 | 4,499,084 | 37,248 | 11 | 0 | 0 |
| 1, 1 | 607 | 2,249,542 | 4,620 | 0 | 0 | 0 |
| 1, 2 | 952 | 10,997,504 | 112,608 | 982 | 24 | 0 |

The binary suite uses words in $\{0,1\}$ and the low suite uses words in $\{0,1,2,3\}$. The final suite uses 1,440 inputs in the Cartesian product of the following sets in address order:

$$
 \{0,1,2,4,5,8,9,15\}\times\{1,2,4,5,8\}
 \times\{0,1,2,4,8,9\}\times\{0,1,2,4,8,9\}.
$$

The code permits the stopping functions on the different suites to differ. Failing any suite precludes a common evaluator. For $h$ distinct eligible address-register choices and $s$ ALU tables, the number of schedules is $h(6s^2+64s)$. The second summand permits either ALU to be the initial one, either continuing order, and 16 granted initial values. All 22,786,244 schedules are covered. As a positive control, a counter scans all four cells of every sensitive input. The stopping-rule checker accepts this schedule for the first-input-bit predicate and rejects it for binary SAT. Compile and run with a C++17 compiler and optimization enabled. [Complete checker](../audits/one_load_two_alus_five_slots.cpp)

This result concerns two branch sites. Three branch sites and only two data slots can have more than one cycle; the schedule classification here does not cover that control topology.
