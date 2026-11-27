import Mathlib.Data.List.Basic
import Mathlib.Data.Bool.Basic

/-! Projection of a three-bit guard with the mixed patterns selectively omitted. -/

namespace SheetGuardProjection

/-- A true field removes the exclusion of that mixed pattern, in (x,y,z) order. -/
structure Omissions where
  p001 : Bool
  p010 : Bool
  p011 : Bool
  p100 : Bool
  p101 : Bool
  p110 : Bool
  deriving DecidableEq

def allowed (g : Omissions) : Bool → Bool → Bool → Bool
  | false, false, false => true
  | false, false, true  => g.p001
  | false, true,  false => g.p010
  | false, true,  true  => g.p011
  | true,  false, false => g.p100
  | true,  false, true  => g.p101
  | true,  true,  false => g.p110
  | true,  true,  true  => true

abbrev Projects (g : Omissions) (x a b : Bool) : Prop :=
  ∃ y z : Bool, allowed g x y z = true ∧
    (a || y || z) = true ∧ (!b || !y || !z) = true

inductive Sheet
  | strict
  | weak
  | unrestricted
  deriving DecidableEq

def left (g : Omissions) : Sheet :=
  if g.p001 || g.p010 then .unrestricted else if g.p011 then .weak else .strict

def right (g : Omissions) : Sheet :=
  if g.p101 || g.p110 then .unrestricted else if g.p100 then .weak else .strict

def sheetValue (s : Sheet) (strictValue a b : Bool) : Bool :=
  match s with
  | .strict => strictValue
  | .weak => a || !b
  | .unrestricted => true

def bySheets (l r : Sheet) (x a b : Bool) : Bool :=
  if x then sheetValue r (!b) a b else sheetValue l a a b

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem projection_by_sheets (g : Omissions) (x a b : Bool) :
    Projects g x a b ↔ bySheets (left g) (right g) x a b = true := by
  rcases g with ⟨c₁,c₂,c₃,c₄,c₅,c₆⟩
  decide +revert

/-- These three optional binary clauses cover all bijunctive projections. -/
def binaryFormula (l r : Sheet) (x a b : Bool) : Bool :=
  (decide (l ≠ .strict) || x || a) &&
  (decide (r ≠ .strict) || !x || !b) &&
  (decide (l = .unrestricted ∨ r = .unrestricted) || a || !b)

def ternary (l r : Sheet) : Bool :=
  decide ((l = .unrestricted ∧ r = .weak) ∨ (l = .weak ∧ r = .unrestricted))

theorem binary_representation (l r : Sheet) (h : ternary l r = false) (x a b : Bool) :
    bySheets l r x a b = binaryFormula l r x a b := by
  revert h x a b
  cases l <;> cases r <;> decide

theorem open_left_weak_right (x a b : Bool) :
    bySheets .unrestricted .weak x a b = (!x || a || !b) := by decide +revert

theorem weak_left_open_right (x a b : Bool) :
    bySheets .weak .unrestricted x a b = (x || a || !b) := by decide +revert

def maj (x y z : Bool) : Bool := (x && y) || (x && z) || (y && z)

/-- Bijunctivity on the Boolean cube is expressed by coordinatewise majority closure. -/
abbrev MajorityClosed (P : Bool → Bool → Bool → Prop) :=
  ∀ x₁ a₁ b₁ x₂ a₂ b₂ x₃ a₃ b₃ : Bool,
    P x₁ a₁ b₁ → P x₂ a₂ b₂ → P x₃ a₃ b₃ →
      P (maj x₁ x₂ x₃) (maj a₁ a₂ a₃) (maj b₁ b₂ b₃)

abbrev SheetRelation (l r : Sheet) (x a b : Bool) : Prop := bySheets l r x a b = true

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1500000 in
theorem sheet_majority_iff (l r : Sheet) :
    MajorityClosed (SheetRelation l r) ↔ ternary l r = false := by
  cases l <;> cases r <;> decide

theorem majority_iff (g : Omissions) :
    MajorityClosed (Projects g) ↔ ternary (left g) (right g) = false := by
  simpa only [MajorityClosed, SheetRelation, projection_by_sheets] using
    sheet_majority_iff (left g) (right g)

def one (b : Bool) : Nat := if b then 1 else 0

def count (g : Omissions) : Nat :=
  one g.p001 + one g.p010 + one g.p011 + one g.p100 + one g.p101 + one g.p110

abbrev ComplementSymmetric (g : Omissions) : Prop :=
  g.p001 = g.p110 ∧ g.p010 = g.p101 ∧ g.p011 = g.p100

theorem at_most_one_is_bijunctive (g : Omissions) (h : count g ≤ 1) :
    MajorityClosed (Projects g) := by
  rw [majority_iff]
  rcases g with ⟨c₁,c₂,c₃,c₄,c₅,c₆⟩
  decide +revert

theorem symmetric_is_bijunctive (g : Omissions) (h : ComplementSymmetric g) :
    MajorityClosed (Projects g) := by
  rw [majority_iff]
  rcases g with ⟨c₁,c₂,c₃,c₄,c₅,c₆⟩
  decide +revert

def intact : Omissions := ⟨false,false,false,false,false,false⟩
def omit001_100 : Omissions := {intact with p001 := true, p100 := true}
def omit001_101 : Omissions := {intact with p001 := true, p101 := true}

theorem two_omissions_clause (x a b : Bool) :
    Projects omit001_100 x a b ↔ (!x || a || !b) = true := by decide +revert

theorem two_omissions_unrestricted (x a b : Bool) : Projects omit001_101 x a b := by
  decide +revert

theorem intact_pin (x t : Bool) : Projects intact x t t ↔ x ≠ t := by decide +revert

def omit011_101 : Omissions := {intact with p011 := true, p101 := true}

abbrev I := Projects intact
abbrev P := Projects omit001_100
abbrev Q := Projects omit011_101

theorem second_ternary_port (x a b : Bool) :
    Q x a b ↔ (x || a || !b) = true := by decide +revert

/-- Each fixed positive port forces a one at its center and a zero across its
negative port. The two centers may lie on opposite sides of the bipartition. -/
theorem two_fixed_positive_ports (h r₀ r₁ h' : Bool) :
    (I h h r₀ ∧ I r₁ r₁ h') ↔
      h = true ∧ r₀ = false ∧ r₁ = true ∧ h' = false := by decide +revert

/-- A common intact crossing center can serve both relays precisely on equal bits. -/
theorem equal_relay (a b : Bool) :
    (∃ h : Bool, I h a a ∧ I h b b) ↔ a = b := by decide +revert

/-- The negation jobs use the calibrated rails L_X = x, R_Z = !z. -/
theorem complement_jobs (x z : Bool) :
    (Q x false (!z) ∧ P x (!z) true) ↔ z = !x := by decide +revert

theorem pinned_complement_jobs (h r₀ r₁ h' x z : Bool) :
    (I h h r₀ ∧ I r₁ r₁ h' ∧ Q x r₀ (!z) ∧ P x (!z) r₁) ↔
      h = true ∧ r₀ = false ∧ r₁ = true ∧ h' = false ∧ z = !x := by
  constructor
  · rintro ⟨i₁, i₂, q, p⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := (two_fixed_positive_ports _ _ _ _).mp ⟨i₁, i₂⟩
    exact ⟨rfl, rfl, rfl, rfl, (complement_jobs x z).mp ⟨q, p⟩⟩
  · rintro ⟨rfl, rfl, rfl, rfl, nz⟩
    obtain ⟨i₁, i₂⟩ := (two_fixed_positive_ports true false true false).mpr ⟨rfl,rfl,rfl,rfl⟩
    obtain ⟨q, p⟩ := (complement_jobs x z).mpr nz
    exact ⟨i₁, i₂, q, p⟩

/-- A complemented literal flips the truth value of its variable. -/
def literal (negative value : Bool) : Bool := value ^^ negative

/-- P(L_(not u), R_(not v), R_w) on physical rails with R_l = !L_l. -/
theorem signed_clause (sx sy sz x y z : Bool) :
    P (!(literal sx x)) (literal sy y) (!(literal sz z)) ↔
      (literal sx x || literal sy y || literal sz z) = true := by decide +revert

/-- The same y=z=x witnesses both proper port clauses for every guard mask,
including intact guards, when the ports are both on the opposite side. -/
theorem all_crossing_local (g : Omissions) (x : Bool) :
    allowed g x x x = true ∧ ((!x) || x || x) = true ∧
      (!(!x) || !x || !x) = true := by cases x <;> simp [allowed]

theorem all_crossing (g : Omissions) (x : Bool) : Projects g x (!x) (!x) :=
  ⟨x, x, all_crossing_local g x⟩

/-- One common side assignment satisfies all jobs; neither the sheet maps nor the
center masks need be injective or aligned across the layers for this implication. -/
theorem all_crossing_layers {Job Vertex : Type*} (side : Vertex → Bool)
    (center posPort negPort : Job → Vertex) (mask : Job → Omissions)
    (hp : ∀ j, side (posPort j) = !(side (center j)))
    (hn : ∀ j, side (negPort j) = !(side (center j))) :
    ∀ j, Projects (mask j) (side (center j)) (side (posPort j)) (side (negPort j)) := by
  intro j
  rw [hp j, hn j]
  exact all_crossing _ _

#print axioms two_fixed_positive_ports
#print axioms equal_relay
#print axioms pinned_complement_jobs
#print axioms signed_clause
#print axioms all_crossing_layers

/-- An intact center between two calibrated right copies gives the two
inequalities in the directed cycle of copies. -/
theorem intact_cycle_step (l r next : Bool) :
    I l (!r) (!next) ↔ r ≤ l ∧ l ≤ next := by decide +revert

/-- Index positions 0,...,len-1 are the distinct visits on one directed orbit.
The extra right endpoint at len is identified with the right endpoint at zero. -/
theorem intact_cycle (len : Nat) (nonempty : 0 < len) (l r : Nat → Bool)
    (jobs : ∀ i < len, I (l i) (!(r i)) (!(r (i+1))))
    (closes : r len = r 0) :
    ∃! value : Bool, ∀ i < len, r i = value ∧ l i = value := by
  have steps (i : Nat) (hi : i < len) : r i ≤ l i ∧ l i ≤ r (i+1) :=
    (intact_cycle_step _ _ _).mp (jobs i hi)
  have forwards (i d : Nat) (bound : i + d ≤ len) : r i ≤ r (i + d) := by
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
      have pair := steps (i+d) (by omega)
      exact fun h => pair.2 (pair.1 ((ih (by omega)) h))
  have upper (i : Nat) (hi : i ≤ len) : r i ≤ r 0 := by
    have sum : i + (len-i) = len := by omega
    have h := forwards i (len-i) (Nat.le_of_eq sum)
    rwa [sum, closes] at h
  refine ⟨r 0, ?_, ?_⟩
  · intro i hi
    have lower : r 0 ≤ r i := by simpa using forwards 0 i (by omega)
    have pair := steps i hi
    exact ⟨le_antisymm (upper i (by omega)) lower,
      le_antisymm (fun h => upper (i+1) hi (pair.2 h)) (fun h => pair.1 (lower h))⟩
  · intro v hv
    exact (hv 0 nonempty).1.symm

/-- Both values occur as constant solutions on every intact cycle. -/
theorem intact_constant_cycle (value : Bool) : I value (!value) (!value) :=
  (intact_cycle_step _ _ _).mpr ⟨le_rfl, le_rfl⟩

/-- Acting at the other rail of the first input and exchanging the other two
complemented ports realizes Q with the single physical guard P. -/
theorem mirrored_clause (x a b : Bool) : Q x a b ↔ P (!x) (!b) (!a) := by decide +revert

theorem mirrored_positive_pair (x z : Bool) :
    P (!x) z true ↔ (x || z) = true := by decide +revert

theorem mirrored_negation (x z : Bool) :
    (P (!x) z true ∧ P x (!z) true) ↔ z = !x := by decide +revert

/-- Completing two disjoint matchings in the four-center box. The private
sheet d=c AND b satisfies the three reciprocal P centers at once. -/
theorem fill_three (c a b : Bool) :
    P a c (c && b) ∧ P b (c && b) c ∧ P (c && b) b a := by decide +revert

theorem four_center_box (g : Omissions) (c a b : Bool) :
    (∃ d : Bool, Projects g c a b ∧ P a c d ∧ P b d c ∧ P d b a) ↔
      Projects g c a b := by
  constructor
  · rintro ⟨_, used, _⟩
    exact used
  · intro used
    exact ⟨c && b, used, fill_three c a b⟩

theorem same_partner_filler (x a : Bool) : P x a a := by decide +revert

theorem pin_box (h r₀ r₁ h' : Bool) :
    (I h h r₀ ∧ I r₁ r₁ h' ∧ P r₀ h' h ∧ P h' r₀ r₁) ↔
      h = true ∧ r₀ = false ∧ r₁ = true ∧ h' = false := by
  constructor
  · rintro ⟨i₁,i₂,_⟩
    exact (two_fixed_positive_ports _ _ _ _).mp ⟨i₁,i₂⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    decide

#print axioms intact_cycle_step
#print axioms intact_cycle
#print axioms intact_constant_cycle
#print axioms mirrored_clause
#print axioms mirrored_negation
#print axioms four_center_box
#print axioms same_partner_filler
#print axioms pin_box

def allMasks : List Omissions := do
  let bits := [false, true]
  let c₁ ← bits
  let c₂ ← bits
  let c₃ ← bits
  let c₄ ← bits
  let c₅ ← bits
  let c₆ ← bits
  return ⟨c₁,c₂,c₃,c₄,c₅,c₆⟩

theorem exhaustive (g : Omissions) : g ∈ allMasks := by
  rcases g with ⟨c₁,c₂,c₃,c₄,c₅,c₆⟩
  decide +revert

set_option maxRecDepth 8192 in
set_option maxHeartbeats 500000 in
theorem census :
    let exceptional := allMasks.filter (fun g => ternary (left g) (right g))
    allMasks.Nodup ∧ allMasks.length = 64 ∧ exceptional.length = 12 ∧
    (exceptional.filter (fun g => count g == 2)).length = 4 ∧
    (exceptional.filter (fun g => count g == 3)).length = 6 ∧
    (exceptional.filter (fun g => count g == 4)).length = 2 := by decide

#print axioms projection_by_sheets
#print axioms open_left_weak_right
#print axioms weak_left_open_right
#print axioms binary_representation
#print axioms majority_iff
#print axioms at_most_one_is_bijunctive
#print axioms symmetric_is_bijunctive
#print axioms two_omissions_clause
#print axioms two_omissions_unrestricted
#print axioms intact_pin
#print axioms census

end SheetGuardProjection
