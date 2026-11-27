/* Exhaustive check of the (4j+1)-instruction upper program for the word-aligned
 * sign-plane catalog F(w,j): 2j input words of w bits, P_0..P_{j-1} at addresses
 * 0..j-1 (positive-unit masks), M_0..M_{j-1} at addresses j..2j-1 (negative-unit
 * masks), variables x_1..x_{jw}, one fixed positive clause over all jw variables.
 *
 * Program U (instruction = load / AND / binary comparison branch, cost 1 each,
 * terminal verdicts free), for pair index i = 0..j-1 with "some M not all-ones"
 * still pending:
 *   load M_i ; if M_i == ones:
 *        if i == j-1: reject
 *        load P_i ; if P_i != 0 reject ; continue with pair i+1 (still pending)
 *   else load P_i ; t = P_i & M_i ; if t != 0 reject ;
 *        then for every later pair: load P, load M, t = P & M, if t != 0 reject
 *        accept
 *   (last pair, pending, M != ones: load P, AND, test: same as above)
 *
 * The interpreter counts executed instructions. We check, for every input:
 *   verdict == closed form  (all P_i & M_i == 0  and  some M_i != ones)
 *   verdict == brute-force satisfiability over all 2^(jw) assignments (when jw <= 10)
 *   steps <= 4j+1, and record the step histogram.
 * Environment: LEAN_VARIANT=1 runs the exact program of PairSelectorUpper.lean instead
 * (on the last pair with M = ones it loads P and tests P = 0 before rejecting);
 * JOURNAL_ORDER=1 with j = 2 runs the nine-step program of NineStepSelectorUpper.lean.
 * Exit status 0 iff there is no mismatch and the maximum is exactly 4j+1.
 * Written for four-instructions-per-sign-plane-pair-at-every-width.md. The source is
 * plain C that also compiles as C++; from audits/:
 *   c++ -O2 sign_plane_pairs_upper_check.cpp -o /tmp/sign-plane-pairs && /tmp/sign-plane-pairs 5 3
 * Usage: sign_plane_pairs_upper_check w j
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static int W, J;
static int LEAN_VARIANT = 0; /* env LEAN_VARIANT=1: the exact program of PairSelectorUpper.lean */
static uint32_t ONES;

/* returns verdict, writes executed instruction count */
static int run(const uint32_t *mem, int *steps) {
  int s = 0;
  for (int i = 0; i < J; ++i) {
    uint32_t m = mem[J + i]; s++;              /* load M_i */
    s++;                                        /* branch M_i == ones */
    if (m == ONES) {
      if (i == J - 1) {                         /* all M ones: reject */
        if (LEAN_VARIANT) { s++; s++; }         /* Lean program: load P, branch P==0, then reject */
        *steps = s; return 0;
      }
      uint32_t p = mem[i]; s++;                 /* load P_i */
      s++;                                      /* branch P_i == 0 */
      if (p != 0) { *steps = s; return 0; }
      continue;                                 /* pending flag still on */
    }
    uint32_t p = mem[i]; s++;                   /* load P_i */
    uint32_t t = p & m; s++;                    /* AND */
    s++;                                        /* branch t == 0 */
    if (t != 0) { *steps = s; return 0; }
    for (int r = i + 1; r < J; ++r) {
      uint32_t pp = mem[r]; s++;                /* load P_r */
      uint32_t mm = mem[J + r]; s++;            /* load M_r */
      uint32_t tt = pp & mm; s++;               /* AND */
      s++;                                      /* branch */
      if (tt != 0) { *steps = s; return 0; }
    }
    *steps = s; return 1;
  }
  *steps = s; return 0; /* unreachable: last pair handled above */
}


/* The journal's nine-step program for j=2 (NineStepSelectorUpper.lean), memory P,Q,M,N. */
static int run_journal(const uint32_t *mem, int *steps) {
  uint32_t p, q, m, n, u; int s = 0;
  m = mem[2]; s++; s++;
  if (m == ONES) {
    n = mem[3]; s++; s++;
    if (n == ONES) { *steps = s; return 0; }
    p = mem[0]; s++; s++;
    if (p != 0) { *steps = s; return 0; }
    q = mem[1]; s++; u = q & n; s++; s++;
    *steps = s; return u == 0;
  }
  p = mem[0]; s++; u = p & m; s++; s++;
  if (u != 0) { *steps = s; return 0; }
  q = mem[1]; s++; n = mem[3]; s++; u = q & n; s++; s++;
  *steps = s; return u == 0;
}

static int closed_form(const uint32_t *mem) {
  int some_not_ones = 0;
  for (int i = 0; i < J; ++i) {
    if (mem[i] & mem[J + i]) return 0;
    if (mem[J + i] != ONES) some_not_ones = 1;
  }
  return some_not_ones;
}

/* brute force: exists x in {0,1}^(jw), x != 0, with positive plane subset of x,
   x disjoint from negative plane. Planes packed as jw-bit integers. */
static int brute(const uint32_t *mem) {
  uint64_t pos = 0, neg = 0;
  for (int i = 0; i < J; ++i) {
    pos |= (uint64_t)mem[i] << (i * W);
    neg |= (uint64_t)mem[J + i] << (i * W);
  }
  int V = J * W;
  for (uint64_t x = 1; x < (1ULL << V); ++x)
    if ((pos & ~x) == 0 && (neg & x) == 0) return 1;
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s w j\n", argv[0]); return 2; }
  W = atoi(argv[1]); J = atoi(argv[2]);
  LEAN_VARIANT = getenv("LEAN_VARIANT") != NULL;
  ONES = (1u << W) - 1;
  int K = 2 * J;
  int total_bits = K * W;
  if (total_bits > 36) { fprintf(stderr, "too many inputs\n"); return 2; }
  int do_brute = (J * W <= 10);
  uint64_t N = 1ULL << total_bits;
  uint64_t hist[64] = {0}, sat = 0, bad = 0, badb = 0;
  int maxs = 0;
  uint32_t mem[16];
  uint64_t witness = 0;
  for (uint64_t x = 0; x < N; ++x) {
    for (int c = 0; c < K; ++c) mem[c] = (uint32_t)((x >> (c * W)) & ONES);
    int st, v = (getenv("JOURNAL_ORDER") && J == 2) ? run_journal(mem, &st) : run(mem, &st);
    int cf = closed_form(mem);
    if (v != cf) { if (bad < 5) fprintf(stderr, "MISMATCH closed form at %llx\n", (unsigned long long)x); bad++; }
    if (do_brute && brute(mem) != cf) { if (badb < 5) fprintf(stderr, "MISMATCH brute at %llx\n", (unsigned long long)x); badb++; }
    hist[st]++; sat += v;
    if (st > maxs) { maxs = st; witness = x; }
  }
  printf("w=%d j=%d words=%d inputs=%llu sat=%llu closed_form_mismatches=%llu brute=%s brute_mismatches=%llu\n",
         W, J, K, (unsigned long long)N, (unsigned long long)sat, (unsigned long long)bad,
         do_brute ? "yes" : "skipped", (unsigned long long)badb);
  printf("  max steps=%d (claimed 4j+1=%d) first attaining input words:", maxs, 4 * J + 1);
  for (int c = 0; c < K; ++c) printf(" %llu", (unsigned long long)((witness >> (c * W)) & ONES));
  printf("\n  histogram:");
  for (int s = 0; s < 64; ++s) if (hist[s]) printf(" %d:%llu", s, (unsigned long long)hist[s]);
  printf("\n");
  return (bad || badb || maxs != 4 * J + 1) ? 1 : 0;
}
