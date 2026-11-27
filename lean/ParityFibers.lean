import Std

namespace ParityFibers

/-- Values on the vertices of a binary cube. -/
inductive Cube : Nat → Type where
  | leaf (v : Int) : Cube 0
  | fork {n : Nat} (left right : Cube n) : Cube (n+1)

def energy : Cube n → Int
  | .leaf x => x*x
  | .fork a b => energy a + energy b

def combine (f : Int → Int → Int) : Cube n → Cube n → Cube n
  | .leaf x, .leaf y => .leaf (f x y)
  | .fork a b, .fork c d => .fork (combine f a c) (combine f b d)

private theorem pair_energy (a b : Int) :
    (a+b)*(a+b)+(a-b)*(a-b) = 2*(a*a+b*b) := by
  simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub]
  omega

private theorem combined_energy (x y : Cube n) :
    energy (combine (·+·) x y) + energy (combine (·-·) x y) =
      2 * (energy x + energy y) := by
  induction x with
  | leaf v => cases y with | leaf w => exact pair_energy v w
  | fork a b ha hb =>
    cases y with
    | fork c d =>
      have ac := ha c
      have bd := hb d
      simp only [combine, energy]
      omega

def walsh : Cube n → Cube n
  | .leaf x => .leaf x
  | .fork a b =>
    let l := walsh a
    let r := walsh b
    .fork (combine (·+·) l r) (combine (·-·) l r)

/-- Unnormalized Walsh transform: energy is multiplied by the cube size. -/
theorem walsh_energy (x : Cube n) : energy (walsh x) = (2 : Int)^n * energy x := by
  induction x with
  | leaf v => simp [walsh, energy]
  | @fork k a b ha hb =>
    simp only [walsh, energy, combined_energy, ha, hb, Int.pow_succ]
    rw [← Int.mul_add, ← Int.mul_assoc, Int.mul_comm 2 ((2 : Int)^k)]

/-- A support list toggles its positions over the binary field. -/
def dot (f : ι → Bool) : List ι → Bool
  | [] => false
  | x :: tail => xor (f x) (dot f tail)

private theorem dot_pivot (f g : ι → Bool) (p : ι) (s : List ι) :
    dot (fun x => xor (g x) (f x && g p)) s =
      xor (dot g s) (dot f s && g p) := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    simp only [dot, ih]
    cases g x <;> cases f x <;> cases g p <;> cases dot g s <;> cases dot f s <;> rfl

private theorem dot_all_false (f : ι → Bool) (no : ∀ x, f x = false) (s : List ι) :
    dot f s = false := by
  induction s with | nil => rfl | cons x s ih => simp [dot, no x, ih]

/-- Any attainable joint answer to n linear tests has a support of size ≤n.
    Repeated indices in a support cancel, so its number of nonzero bits
    is at most its list length. -/
theorem sparse_support (n : Nat) (rows : List (ι → Bool)) (budget : rows.length ≤ n)
    (s : List ι) : ∃ v : List ι, v.length ≤ n ∧ ∀ g ∈ rows, dot g v = dot g s := by
  induction n generalizing rows with
  | zero =>
    have nil : rows = [] := List.length_eq_zero_iff.mp (by omega)
    exact ⟨[], by simp, by simp [nil]⟩
  | succ n ih =>
    cases rows with
    | nil => exact ⟨[], by simp, by simp⟩
    | cons f rest =>
      have hr : rest.length ≤ n := by simpa using budget
      by_cases active : ∃ p, f p = true
      · obtain ⟨p, hp⟩ := active
        let tr := fun (g : ι → Bool) x => xor (g x) (f x && g p)
        obtain ⟨v, hv, agree⟩ := ih (rest.map tr) (by simpa using hr)
        have ht (g) (hg : g ∈ rest) :
            xor (dot g v) (dot f v && g p) = xor (dot g s) (dot f s && g p) := by
          have a := agree (tr g) (List.mem_map.mpr ⟨g, hg, rfl⟩)
          simpa [tr, dot_pivot] using a
        by_cases eq : dot f v = dot f s
        · refine ⟨v, by omega, ?_⟩
          intro g hg
          rcases List.mem_cons.mp hg with rfl | hrest
          · exact eq
          · have a := ht g hrest
            rw [eq] at a
            exact Bool.xor_left_inj.mp a
        · refine ⟨p :: v, by simpa using hv, ?_⟩
          intro g hg
          rcases List.mem_cons.mp hg with rfl | hrest
          · simp only [dot, hp]
            cases hg : dot g v <;> cases hs : dot g s <;> simp_all
          · have a := ht g hrest
            simp only [dot]
            cases hg : dot g v <;> cases hs : dot g s <;> cases hf : dot f v <;>
              cases hj : dot f s <;> cases hp' : g p <;> simp_all
      · have no (x : ι) : f x = false := by
          cases e : f x with | false => rfl | true => exact False.elim (active ⟨x,e⟩)
        obtain ⟨v, hv, agree⟩ := ih rest hr
        refine ⟨v, by omega, ?_⟩
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hrest
        · rw [dot_all_false g no, dot_all_false g no]
        · exact agree g hrest

end ParityFibers
