import Std

namespace ParityRepairRows

variable {ι : Type}
abbrev Word (ι : Type) := ι → Bool

def add (a b : Word ι) : Word ι := fun i => a i ^^ b i

def supportCost (weight : ι → Nat) (a : Word ι) : List ι → Nat
  | [] => 0
  | i :: is => (if a i then weight i else 0) + supportCost weight a is

theorem cost_add_le (weight : ι → Nat) (a b : Word ι) (coords : List ι) :
    supportCost weight (add a b) coords ≤
      supportCost weight a coords + supportCost weight b coords := by
  induction coords with
  | nil => simp [supportCost]
  | cons i is ih =>
    simp only [supportCost, add] at *
    have localBound (x y : Bool) (w : Nat) :
        (if x ^^ y then w else 0) ≤ (if x then w else 0) + (if y then w else 0) := by
      cases x <;> cases y <;> simp <;> omega
    have localStep := localBound (a i) (b i) (weight i)
    omega

def sumWords : List (Word ι) → Word ι
  | [] => fun _ => false
  | a :: as => add a (sumWords as)

theorem cost_zero (weight : ι → Nat) (coords : List ι) :
    supportCost weight (fun _ => false) coords = 0 := by
  induction coords with
  | nil => rfl
  | cons i is ih => simp [supportCost, ih]

theorem repair_cost (weight : ι → Nat) (coords : List ι)
    (repairs : List (Word ι)) (per : Nat)
    (small : ∀ r ∈ repairs, supportCost weight r coords ≤ per) :
    supportCost weight (sumWords repairs) coords ≤ repairs.length * per := by
  induction repairs with
  | nil => simp [sumWords, cost_zero]
  | cons a as ih =>
    have h₁ := small a (by simp)
    have h₂ := ih (fun r hr => small r (by simp [hr]))
    have h₃ := cost_add_le weight a (sumWords as) coords
    simp only [sumWords, List.length_cons, Nat.succ_mul]
    omega

def parity (a : Word ι) : List ι → Bool
  | [] => false
  | i :: is => a i ^^ parity a is

theorem parity_congr {a b : Word ι} {rows : List ι}
    (agree : ∀ i ∈ rows, a i = b i) : parity a rows = parity b rows := by
  induction rows with
  | nil => rfl
  | cons i is ih =>
    simp only [parity]
    rw [agree i (by simp), ih (fun k hk => agree k (by simp [hk]))]

theorem refutation_sound (attainable : Word ι → Prop) (target : Word ι)
    (rows : List ι)
    (vanishes : ∀ a, attainable a → parity a rows = false)
    (oddTarget : parity target rows = true) :
    ¬ ∃ a, attainable a ∧ ∀ i ∈ rows, a i = target i := by
  rintro ⟨a, ha, agrees⟩
  have eq := parity_congr agrees
  rw [vanishes a ha, oddTarget] at eq
  contradiction

/-- Every private column in a subdivided equation requires the two
adjacent row-selection bits to agree. -/
def adjacentAgree (b : Bool) : List Bool → Prop
  | [] => True
  | x :: xs => b = x ∧ adjacentAgree x xs

theorem selected_chain (bits : List Bool) (b : Bool)
    (edges : adjacentAgree b bits) : ∀ x ∈ bits, x = b := by
  induction bits generalizing b with
  | nil => simp
  | cons x xs ih =>
    have head : b = x := edges.1
    have tail := edges.2
    intro y hy
    rcases List.mem_cons.mp hy with h | h
    · exact h.trans head.symm
    · exact (ih x tail y h).trans head.symm

end ParityRepairRows
