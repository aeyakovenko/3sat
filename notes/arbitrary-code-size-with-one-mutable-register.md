# A code-size induction that preserves a superlinear deficit with one mutable register

Use the ordinary DIMACS single-edit suites of the [five-slot analysis](five-instruction-loops-on-dimacs-sat.md), with $k=\Theta(N/\log N)$ required original reads on one common satisfiable base. Consider a RAM with one mutable data register $r$, any number of instructions, and unrestricted addressed storage. Between memory operations its instructions can compute any deterministic word function of $r$, literals and fixed length metadata, or branch on these data. It can load from $r$ or a fixed-on-input address. A STORE at any address $a$ can write $a$ itself or a program literal or fixed metadata word. In particular it may use a separate marker for each STORE and revisit any marks it made. The restriction is on what a STORE can write; a general RAM can also save $r$ at an unrelated address. Each memory probe costs at least a step. These conventions matter for accumulator machines. [Cook and Reckhow's RAM models](https://www.cs.toronto.edu/~sacook/homepage/rams.pdf)

**Proposition.** For every code-size cutoff $s$ and every time multiplier $C$, a finite suite of ordinary formulas defeats *all* programs of this class with at most $s$ slots at deadline $CN$. Here slots supply at most two numeric immediates each. There is a common length $N$ for the entire suite. For any fixed $s$ there are arbitrarily large such $N$. Every program correct throughout the suite takes $\Omega_s(N^2/\log^2 N)$ steps on its common base.

Let $h$ bound the number of original word values on the periodic bases. This is an absolute constant. Put all original values, literals and public metadata in a set $V$ of size at most $h+2s+3$. Call a load a reset if it reads an original word or returns a value in $V$. Every required first read is a reset. Its post-load state is determined, for the purpose of the next interval, by the LOAD site and the returned member of $V$. The initial program state counts as one extra start. Thus there are at most $b_s=(s+1)(h+2s+3)$ starts. A load at a fixed address that echoes its address also yields a member of $V$ when the address is a literal or metadata word. Allowing it to act deterministically as an address echo leads to the same reasoning.

After a reset, until the next one, each LOAD must return its *address*. Even though the next reset can depend on memory, a deterministic hypothetical execution in which every LOAD echoes its address determines which addresses appear at each opportunity up to and including that reset. Branches, arithmetic, memory writes and all intermediate instructions are allowed on this continuation. A halt merely truncates a path. In the first $d$ opportunities from all $b_s$ starts together, there are at most $b_s d$ distinct addresses. Set $d=\lfloor k/(2b_s)\rfloor$. For at least $k-b_s d$ required addresses, the episode ending at its first original read costs more than $d$ loads. Distinct endpoints finish disjoint episodes: each starts just after the preceding reset and ends at the next one, or starts at entry. If $k\ge4b_s$, the common base therefore costs at least $k^2/(8b_s)$ steps. [Formal packing inequality](../lean/ResetEpisodePacking.lean)

To pass from $s$ to $s+1$, compute $b_{s+1}$ and increase the repetition count until $k\ge4b_{s+1}$ and $k^2>8b_{s+1}CN$. Both tests eventually hold since $k=\Theta(N/\log N)$. Retain the new base plus one single-word edit per required address. A machine that fails to inspect one of them gives the same verdict on a satisfiable and an unsatisfiable input, or exceeds the clock. Any machine that inspects them all on the base has already exceeded the clock if it distinguishes every edit. This formula transformation works when all the code is replaced, and its length choice is independent of the actual immediate values. For the initial and subsequent suites use the same procedure with the corresponding cutoff. One may append the new suite to earlier suites if nested test sets are desired.

## What breaks with a spill cell

Allow just one more way to write a word: `STORE[-1] ← r`. The separate fixed program below can visit all the original words of the same bases in $O(N/w)$ steps. Address $-1\bmod 2^w$ is outside the physical input range. Every occupied word of the base is nonzero, including a partial final word. Unused memory is zero.

```
r ← 0
scan:
    STORE[-1] ← r
    r ← LOAD[r]
    if r = 0 then halt
    r ← LOAD[-1]
    r ← r + 1
    jump scan
```

This program establishes how quickly a spill cell lets the machine satisfy the compulsory-read condition. It does not decide general SAT. Although an original load still resets the register, the next load of the spill cell recovers an arbitrary previous index. Its value can be outside $V$ and can differ from the cell's own address. The deterministic continuation count used in the induction then fails. A general size-$s+1$ RAM can introduce such a store or an additional live register. The unrestricted induction remains open.
