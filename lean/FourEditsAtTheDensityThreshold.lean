import Std

namespace FourEditsAtTheDensityThreshold

private def tri (p q r : Bool) := p || q || r

/-- X,A',B',C' in the ASCII files represent negations of x,a,b,c. -/
def active (bonus d x y z a b c : Bool) : Bool :=
  d || ((!x) && (!y) && z && a && b && (c == bonus))

def check (bonus : Bool) (edits : Fin 16) (d x y z a b c : Bool) : Bool :=
  active bonus d x y z a b c &&
    tri x y z && tri x a c && tri y b c && tri z a b &&
    tri (if edits.val.testBit 0 then !x else d) (!y) (!z) &&
    tri (if edits.val.testBit 1 then !d else a) x (!y) &&
    tri (if edits.val.testBit 2 then !d else b) (!x) z &&
    tri (if edits.val.testBit 3 then !d else c) y (!z)

def dormant (edits : Fin 16) (x y z a b c : Bool) : Bool :=
  (!edits.val.testBit 0 && x && y && z) ||
  (!edits.val.testBit 1 && !x && y && a) ||
  (!edits.val.testBit 2 && x && !z && b) ||
  (!edits.val.testBit 3 && !y && z && c)

theorem control_fibers : ∀ (bonus : Bool) (edits : Fin 16) (d x y z a b c : Bool),
    check bonus edits d x y z a b c =
      (if d then dormant edits x y z a b c else
        !x && !y && z && a && b && (c == bonus) && (bonus || edits.val.testBit 3)) := by
  native_decide

def count (bonus d : Bool) (edits : Fin 16) :=
  ((List.range 64).filter fun v => check bonus edits d (v.testBit 0) (v.testBit 1)
    (v.testBit 2) (v.testBit 3) (v.testBit 4) (v.testBit 5)).length

theorem model_counts : ∀ (bonus : Bool) (edits : Fin 16),
    count bonus true edits = 8*((List.range 4).filter fun j => !edits.val.testBit j).length ∧
    count bonus false edits = (bonus || edits.val.testBit 3).toNat := by native_decide

private def supports : List (List Nat) :=
  [[0,1,3],[0,2,4],[1,2,5],[0,1,2],[0,3,5],[1,4,5],[2,3,4]]

private def weight (v : Nat) := ((List.range 6).filter fun j => v.testBit j).length

/-- Together with the four disjoint private completions of d, this forces
four paid variables outside the disjoint occurrence triples. -/
theorem misses_support : ∀ v : Fin 64, weight v ≤ 2 →
    supports.any (fun edge => edge.all (fun i => !v.val.testBit i)) = true := by decide +kernel

theorem physical_bytes :
    (('1'.toNat) ^^^ ('0'.toNat)) = 1 ∧
    (('3'.toNat) ^^^ ('1'.toNat)) = 2 ∧
    (('5'.toNat) ^^^ ('1'.toNat)) = 4 ∧
    (('9'.toNat) ^^^ ('1'.toNat)) = 8 := by decide +kernel

theorem normalized_mass (m : Nat) :
    32 * 7^m * 8^(m+4) * 7^4 =
      128 * 8^m * 7^(m+4) * (4*4^4) := by
  simp only [Nat.pow_add]
  calc
    _ = (7^m * 8^m) * (32*8^4*7^4) := by ac_rfl
    _ = (7^m * 8^m) * (128*7^4*(4*4^4)) := by rfl
    _ = _ := by ac_rfl

end FourEditsAtTheDensityThreshold
