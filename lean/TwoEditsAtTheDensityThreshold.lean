import Std

namespace TwoEditsAtTheDensityThreshold

def triple (x y z : Bool) := x || y || z

def padded (x y t : Bool) := triple x y t && triple x y (!t)

theorem padding : ∀ x y t : Bool, padded x y t = (x || y) := by decide +kernel

def branch (bonus edited g a b f : Bool) : Bool :=
  padded g (!f) b && triple g a b && triple g (if bonus then a else !a) (!b) &&
    triple g (if edited then b else a) f

def controls (bonus e₀ e₁ t b a₀ f₀ a₁ f₁ : Bool) : Bool :=
  branch bonus e₀ t a₀ b f₀ && branch bonus e₁ (!t) a₁ b f₁ &&
    padded (!b) (!t) a₀ && padded (!b) (!a₁) t && padded (!b) (!f₁) t

/-- With b false exactly the unedited active branch survives. With b true
the base wrapper needs edit zero; the bonus wrapper also retains this slice
before the edit. -/
theorem control_fibers : ∀ bonus e₀ e₁ t b a₀ f₀ a₁ f₁ : Bool,
    controls bonus e₀ e₁ t b a₀ f₀ a₁ f₁ =
      ((!b && (if t then !e₁ && a₁ && !f₁ else !e₀ && a₀ && !f₀)) ||
       (b && !t && (a₀ == bonus) && !f₀ && !a₁ && !f₁ && (bonus || e₀))) := by decide +kernel

private def fromMask (bonus e₀ e₁ : Bool) (v : Nat) :=
  controls bonus e₀ e₁ (v.testBit 0) (v.testBit 1) (v.testBit 2)
    (v.testBit 3) (v.testBit 4) (v.testBit 5)

def controlCount (bonus e₀ e₁ b : Bool) : Nat :=
  ((List.range 64).filter fun v => (v.testBit 1 == b) && fromMask bonus e₀ e₁ v).length

theorem all_control_counts : ∀ bonus e₀ e₁ : Bool,
    controlCount bonus e₀ e₁ false = 4 * ((!e₀).toNat + (!e₁).toNat) ∧
    controlCount bonus e₀ e₁ true = (bonus || e₀).toNat := by decide +kernel

private def left : List (Nat × Bool) := [(0,false),(1,false),(2,true),(3,false)]
private def right : List (Nat × Bool) := [(0,true),(1,false),(4,true),(5,false)]

private def compatible (a b : Nat × Bool) := a.1 != b.1 || a.2 == b.2
private def weight (u : Nat) := ((List.range 6).filter fun i => u.testBit i).length

/-- Any three chosen controls leave a compatible pair of true literals, one
from each branch, with both variable names outside that control set. -/
theorem escape_three : ∀ v : Fin 64, weight v ≤ 3 →
    left.any (fun a => right.any (fun b =>
      compatible a b && !v.val.testBit a.1 && !v.val.testBit b.1)) = true := by decide +kernel

theorem redundant_in_both_dormant_branches : ∀ t a₀ f₀ a₁ f₁ : Bool,
    (if t then a₁ && !f₁ else a₀ && !f₀) = true →
    left.all (fun l => right.all (fun r =>
      let values := #[t, false, a₀, f₀, a₁, f₁]
      !compatible l r || (values[l.1]! == l.2) || (values[r.1]! == r.2))) = true := by decide +kernel

theorem edited_bytes :
    (('3'.toNat) ^^^ ('1'.toNat)) = 2 ∧ (('5'.toNat) ^^^ ('1'.toNat)) = 4 := by decide +kernel

theorem normalized_density (m : Nat) :
    8 * 7^m * 8^(m+4) * 7^4 =
    64 * 8^m * 7^(m+4) * (2*4^4) := by
  simp only [Nat.pow_add]
  calc
    _ = (7^m * 8^m) * (8 * 8^4 * 7^4) := by ac_rfl
    _ = (7^m * 8^m) * (64 * 7^4 * (2*4^4)) := by rfl
    _ = _ := by ac_rfl

namespace Three

def sixClauses (s t a₀ a₁ a₂ : Bool) : Bool :=
  (!s || !t) && (!s || a₁) && (!t || a₂) &&
    triple s a₀ a₂ && triple t a₀ a₁ && triple a₀ a₁ a₂

def dormant (s t a₀ a₁ a₂ : Bool) : Bool :=
  (!s && !t && a₀) || (s && !t && a₁) || (!s && t && a₂)

theorem six_are_redundant : ∀ s t a₀ a₁ a₂ : Bool,
    dormant s t a₀ a₁ a₂ = true → sixClauses s t a₀ a₁ a₂ = true := by decide +kernel

theorem hard_accepts_six : ∀ a₀ : Bool, sixClauses false false a₀ true true = true := by
  decide +kernel

/-- Coordinates are s,t,a₀,a₁,a₂. Every two-variable set misses a support.
Four disjoint private completions realize each short support in width three. -/
private def supports : List (List Nat) := [[0,1],[0,3],[1,4],[0,2,4],[1,2,3],[2,3,4]]

theorem rank_three : ∀ v : Fin 32, weight v ≤ 2 →
    supports.any (fun edge => edge.all (fun i => !v.val.testBit i)) = true := by decide +kernel

def assigned (bonus e₀ e₁ e₂ b s t a₀ a₁ a₂ : Bool) : Bool :=
  (!s || !t) && (!b || (!s && !t && (a₀ == bonus) && a₁ && a₂)) &&
    triple s t (if e₀ then b else a₀) && triple (!s) t (if e₁ then b else a₁) &&
    triple s (!t) (if e₂ then b else a₂)

private def count (bonus e₀ e₁ e₂ b : Bool) : Nat :=
  ((List.range 32).filter fun v => assigned bonus e₀ e₁ e₂ b (v.testBit 0) (v.testBit 1)
     (v.testBit 2) (v.testBit 3) (v.testBit 4)).length

theorem all_cofactor_counts : ∀ bonus e₀ e₁ e₂ : Bool,
    count bonus e₀ e₁ e₂ false = 4*((!e₀).toNat+(!e₁).toNat+(!e₂).toNat) ∧
    count bonus e₀ e₁ e₂ true = (bonus || e₀).toNat := by decide +kernel

theorem third_physical_bit : (('9'.toNat) ^^^ ('1'.toNat)) = 8 := by decide +kernel

end Three
end TwoEditsAtTheDensityThreshold
