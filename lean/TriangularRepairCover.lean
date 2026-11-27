import Std

/-! A transversal contains an editable matrix position from every triangle.
Sites are tagged to distinguish entries in the three input tables. -/
namespace TriangularRepairCover

inductive Site where
  | ab (i k : Nat)
  | bc (k j : Nat)
  | ca (j i : Nat)
  deriving DecidableEq

def Hits (d : Nat) (sites : List Site) : Prop :=
  ∀ i < d, ∀ k < d, ∀ j < d,
    Site.ab i k ∈ sites ∨ Site.bc k j ∈ sites ∨ Site.ca j i ∈ sites

/-- On the packed Latin square use j=i+k modulo d. Its inverse operations
here use only comparisons and subtractions on in-range indices. -/
def rotate (d x y : Nat) := if x+y < d then x+y else x+y-d
def difference (d z x : Nat) := if x ≤ z then z-x else z+d-x

private theorem rotate_lt {d x y : Nat} (hx : x < d) (hy : y < d) :
    rotate d x y < d := by
  unfold rotate
  split <;> omega

private theorem unrotate {d x y : Nat} (hx : x < d) (hy : y < d) :
    difference d (rotate d x y) x = y ∧ difference d (rotate d x y) y = x := by
  unfold rotate difference
  split <;> constructor <;> split <;> omega

/-- Every site of a packed triangle gives back its row-major serial number. -/
def recover (d : Nat) : Site → Nat
  | .ab i k => k+d*i
  | .bc k j => k+d*difference d j k
  | .ca j i => difference d j i + d*i

private theorem distinct_length {α : Type} (xs ys : List α) (hx : xs.Nodup)
    (sub : xs ⊆ ys) : xs.length ≤ ys.length := by
  classical
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp hx
    have mem := sub List.mem_cons_self
    have shorter := ih (ys.erase x) tail (by
      intro y hy
      have ne : y ≠ x := by rintro rfl; exact fresh hy
      exact (List.mem_erase_of_ne ne).mpr (sub (List.mem_cons_of_mem _ hy)))
    rw [List.length_erase_of_mem mem] at shorter
    have pos := List.length_pos_of_mem mem
    simp only [List.length_cons]
    omega

theorem minimum_lower (d : Nat) (sites : List Site) (hit : Hits d sites) :
    d*d ≤ sites.length := by
  classical
  by_cases zero : d = 0
  · simp [zero]
  have pos : 0 < d := by omega
  have find (u : Fin (d*d)) : ∃ e ∈ sites, recover d e = u.val := by
    let i := u.val / d
    let k := u.val % d
    have hi : i < d := (Nat.div_lt_iff_lt_mul pos).2 u.isLt
    have hk : k < d := Nat.mod_lt _ pos
    have packed : k+d*i = u.val := Nat.mod_add_div _ _
    obtain ⟨ui, uk⟩ := unrotate hi hk
    rcases hit i hi k hk (rotate d i k) (rotate_lt hi hk) with h | h | h
    · exact ⟨.ab i k, h, packed⟩
    · exact ⟨.bc k (rotate d i k), h, by simpa [recover, uk] using packed⟩
    · exact ⟨.ca (rotate d i k) i, h, by simpa [recover, ui] using packed⟩
  let chosen := fun u => Classical.choose (find u)
  have chosen_ok (u : Fin (d*d)) : chosen u ∈ sites ∧ recover d (chosen u) = u.val :=
    Classical.choose_spec (find u)
  have nd : (List.ofFn chosen).Nodup := by
    apply List.pairwise_iff_getElem.mpr
    intro a b ha hb lt eq
    simp only [List.getElem_ofFn] at eq
    have same := congrArg (recover d) eq
    rw [(chosen_ok _).2, (chosen_ok _).2] at same
    exact (Nat.ne_of_lt lt) same
  have bound := distinct_length (List.ofFn chosen) sites nd (by
    intro e he
    obtain ⟨u, rfl⟩ := List.mem_ofFn.mp he
    exact (chosen_ok u).1)
  simpa using bound

def firstBank (d : Nat) : List Site :=
  (List.range d).flatMap fun i => (List.range d).map (Site.ab i)

theorem minimum_attained (d : Nat) :
    Hits d (firstBank d) ∧ (firstBank d).length = d*d := by
  constructor
  · intro i hi k hk j hj
    exact Or.inl (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
      List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩⟩)
  · simp [firstBank, List.length_flatMap, List.map_const']

/-- The one-hit-per-triangle equations force the rectangular differences
of each indicator array to vanish. The other two arrays cancel. -/
theorem rectangular_identity {I K J : Type} (a : I → K → Nat)
    (b : K → J → Nat) (c : J → I → Nat) (j : J)
    (h : ∀ i k z, a i k + b k z + c z i = 1) (i i' : I) (k k' : K) :
    a i k + a i' k' = a i k' + a i' k := by
  have := h i k j
  have := h i' k' j
  have := h i k' j
  have := h i' k j
  omega

/-- A binary array with all rectangular differences zero depends on at
most one of its two indices. -/
theorem binary_rigidity {I K : Type} (a : I → K → Nat)
    (binary : ∀ i k, a i k ≤ 1)
    (rect : ∀ i i' k k', a i k + a i' k' = a i k' + a i' k) :
    (∀ i i' k, a i k = a i' k) ∨ (∀ i k k', a i k = a i k') := by
  classical
  by_cases same : ∀ i i' k, a i k = a i' k
  · exact Or.inl same
  · simp only [Classical.not_forall] at same
    obtain ⟨u, v, p, diff⟩ := same
    have fixed (k : K) : a u k = a u p := by
      have := rect u v k p
      have := binary u k
      have := binary v k
      have := binary u p
      have := binary v p
      omega
    right
    intro i k k'
    have h := rect i u k k'
    rw [fixed k, fixed k'] at h
    omega

end TriangularRepairCover
