import Std

/-! The table invariant and lifetime accounting for one radix-trie node. -/
namespace IncrementalRadixTable

variable {V : Type}

def write (bank : Nat → V) (atIndex : Nat) (v : V) (i : Nat) : V :=
  if i = atIndex then v else bank i

def observed (cursor : Nat) (source dest : Nat → V) (i : Nat) : V :=
  if i < cursor then dest i else source i

theorem migrate_preserves (source dest : Nat → V) (q i : Nat) :
    observed (q+1) source (write dest q (source q)) i = observed q source dest i := by
  by_cases lt : i < q
  · have lt' : i < q+1 := by omega
    have ne : i ≠ q := by omega
    simp [observed, write, lt, lt', ne]
  · by_cases eq : i = q
    · subst i
      simp [observed, write]
    · have ge : ¬ i < q+1 := by omega
      simp [observed, lt, ge]

/-- A store through the currently selected bank updates exactly that
logical array entry. The new value can be data or a child's new header. -/
theorem write_active_bank (source dest : Nat → V) (q j : Nat) (v : V) :
    (if j < q then observed q source (write dest j v)
     else observed q (write source j v) dest) =
    write (observed q source dest) j v := by
  funext i
  by_cases eq : i = j
  · subst i
    by_cases side : j < q <;> simp [observed, write, side]
  · by_cases side : j < q <;> by_cases s : i < q <;> simp [observed, write, eq, side, s]

theorem rotate_preserves (old current spare : Nat → V) (B i : Nat) (h : i < B) :
    observed 0 current spare i = observed B old current i := by simp [observed, h]

/-- Offset j can serve on B-j visits as destination and j visits as
source. Each serving visit has at most two direct probes. -/
theorem lifetime_probe_cap (B j destVisits sourceVisits direct migr : Nat)
    (h : j < B) (hd : destVisits ≤ B-j) (hs : sourceVisits ≤ j)
    (hw : direct ≤ 2*(destVisits+sourceVisits)) (hm : migr ≤ 2) :
    direct + migr ≤ 2*B+2 := by omega

end IncrementalRadixTable
