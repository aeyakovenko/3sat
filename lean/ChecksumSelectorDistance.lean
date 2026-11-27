import Std

namespace ChecksumSelectorDistance

def xorWord {I : Type} (u v : I → Bool) (i : I) : Bool := u i ^^ v i

def ham {I : Type} (coords : List I) (u v : I → Bool) : Nat :=
  coords.countP (fun i => u i != v i)

theorem ham_symmetric {I : Type} (coords : List I) (u v : I → Bool) :
    ham coords u v = ham coords v u := by
  apply List.countP_congr
  intro i _
  cases u i <;> cases v i <;> decide

theorem ham_triangle {I : Type} (coords : List I) (u v w : I → Bool) :
    ham coords u w ≤ ham coords u v + ham coords v w := by
  induction coords with
  | nil => simp [ham]
  | cons i rest ih =>
    simp only [ham, List.countP_cons] at *
    cases a : u i <;> cases b : v i <;> cases c : w i <;>
      simp [a, b, c] <;> omega

theorem ham_xor {I : Type} (coords : List I) (u v w z : I → Bool) :
    ham coords (xorWord u v) (xorWord w z) ≤ ham coords u w + ham coords v z := by
  induction coords with
  | nil => simp [ham]
  | cons i rest ih =>
    simp only [ham, List.countP_cons] at *
    cases a : u i <;> cases b : v i <;> cases c : w i <;> cases d : z i <;>
      simp [xorWord, a, b, c, d] at * <;> omega

private theorem disjoint_count {U : Type} (pts : List U) (p q : U → Bool)
    (disjoint : ∀ u ∈ pts, p u = true → q u = false) :
    pts.countP p + pts.countP q ≤ pts.length := by
  induction pts with
  | nil => simp [ham]
  | cons u us ih =>
    have tail := ih (fun x mem => disjoint x (List.mem_cons_of_mem _ mem))
    have head := disjoint u (by simp)
    cases a : p u <;> cases b : q u <;>
      simp [a, b, List.countP_cons] at * <;> omega

/-- A translate of a subset of density above one half meets that subset. -/
theorem dense_translate {U : Type} (pts : List U) (p : U → Bool) (translate : U → U)
    (perm : (pts.map translate).Perm pts) (dense : pts.length < 2 * pts.countP p) :
    ∃ u ∈ pts, p u = true ∧ p (translate u) = true := by
  apply Classical.byContradiction
  intro noPair
  have disjoint : ∀ u ∈ pts, p u = true → (p ∘ translate) u = false := by
    intro u mem good
    cases h : p (translate u)
    · exact h
    · exact False.elim (noPair ⟨u, mem, good, h⟩)
  have bound := disjoint_count pts p (p ∘ translate) disjoint
  have eq := List.Perm.countP_eq p perm
  rw [List.countP_map] at eq
  omega

/-- With a separated additive honest code, rows close on a majority of all candidate
symbols extend to one additive decoder, close on every candidate symbol. -/
theorem exists_additive_decoder {I U H : Type} (coords : List I) (pts : List U)
    (addU : U → U → U) (addH : H → H → H) (alt : U → I → Bool)
    (honest : H → I → Bool) (good : U → Bool) (tol dist : Nat)
    (perm : ∀ x, (pts.map (addU x)).Perm pts)
    (cancel : ∀ x y, addU y (addU x y) = x)
    (altAdd : ∀ x y, alt (addU x y) = xorWord (alt x) (alt y))
    (honestAdd : ∀ x y, honest (addH x y) = xorWord (honest x) (honest y))
    (sep : ∀ x y, x ≠ y → dist ≤ ham coords (honest x) (honest y))
    (room : 6 * tol < dist) (dense : pts.length < 2 * pts.countP good)
    (close : ∀ x, good x = true → ∃ a, ham coords (alt x) (honest a) ≤ tol) :
    ∃ decode : U → H,
      (∀ x, ham coords (alt x) (honest (decode x)) ≤ 2 * tol) ∧
      (∀ x y, decode (addU x y) = addH (decode x) (decode y)) := by
  classical
  have allClose (x : U) : ∃ a, ham coords (alt x) (honest a) ≤ 2 * tol := by
    obtain ⟨y, _, goodY, goodZ⟩ := dense_translate pts good (addU x) (perm x) dense
    obtain ⟨a, ha⟩ := close y goodY
    obtain ⟨b, hb⟩ := close (addU x y) goodZ
    refine ⟨addH a b, ?_⟩
    have eqAlt : alt x = xorWord (alt y) (alt (addU x y)) := by
      simpa only [cancel] using altAdd y (addU x y)
    rw [eqAlt, honestAdd]
    have sumBound := ham_xor coords (alt y) (alt (addU x y)) (honest a) (honest b)
    omega
  let decode : U → H := fun x => Classical.choose (allClose x)
  have bound (x : U) : ham coords (alt x) (honest (decode x)) ≤ 2 * tol :=
    Classical.choose_spec (allClose x)
  refine ⟨decode, bound, ?_⟩
  intro x y
  apply Classical.byContradiction
  intro different
  have apart := sep _ _ different
  have t := ham_triangle coords (honest (decode (addU x y))) (alt (addU x y))
    (honest (addH (decode x) (decode y)))
  rw [ham_symmetric coords (honest (decode (addU x y))) (alt (addU x y))] at t
  have sumBound := ham_xor coords (alt x) (alt y) (honest (decode x)) (honest (decode y))
  have middle : ham coords (alt (addU x y)) (honest (addH (decode x) (decode y))) ≤
      ham coords (alt x) (honest (decode x)) + ham coords (alt y) (honest (decode y)) := by
    simpa only [altAdd, honestAdd] using sumBound
  have hx := bound x
  have hy := bound y
  have hxy := bound (addU x y)
  omega

/-- A pair of correct endpoint decodings witnesses the transfer equality at its base. -/
theorem transfer_at_good_edge {U H : Type} (decode : U → H)
    (left : H → H) (right : U → U) (base next : H) (base' next' : U)
    (cleanBase : decode base' = base) (cleanNext : decode next' = next)
    (honestEdge : left base = next) (alternateEdge : right base' = next') :
    decode (right base') = left (decode base') := by
  rw [alternateEdge, cleanNext, cleanBase, honestEdge]

/-- A row with an incorrect decoded message uses at least the code distance
minus its decoding radius in disagreements with the correct word. -/
theorem mismatch_cost {I U H : Type} (coords : List I) (honest : H → I → Bool)
    (alt : U → I → Bool) (decode : U → H) (u : U) (truth : H) (rad gap : Nat)
    (separation : ∀ a b, a ≠ b → gap ≤ ham coords (honest a) (honest b))
    (bound : ham coords (alt u) (honest (decode u)) ≤ rad) (wrong : truth ≠ decode u) :
    gap ≤ ham coords (honest truth) (alt u) + rad := by
  have h := ham_triangle coords (honest truth) (alt u) (honest (decode u))
  have t := separation truth (decode u) wrong
  omega

/-- On the paired row sample, each failure of transfer must have at least one
bad endpoint. A strict count advantage over the cap for a proper kernel
forces the two candidate linear maps to coincide. -/
theorem transfer_from_paired_counts {I H : Type} (pts : List I) (left right : H → H)
    (bad₀ bad₁ agree : I → Bool) (cap : Nat)
    (bothGood : ∀ i ∈ pts, bad₀ i = false → bad₁ i = false → agree i = true)
    (kernelCap : left ≠ right → pts.countP agree ≤ cap)
    (room : cap + pts.countP bad₀ + pts.countP bad₁ < pts.length) : left = right := by
  have cover {xs : List I} (h : ∀ i ∈ xs,
      bad₀ i = false → bad₁ i = false → agree i = true) :
      xs.length ≤ xs.countP agree + xs.countP bad₀ + xs.countP bad₁ := by
    induction xs with
    | nil => simp
    | cons i rest ih =>
      have tail := ih (fun j mem => h j (List.mem_cons_of_mem i mem))
      have head := h i (by simp)
      cases a : bad₀ i <;> cases b : bad₁ i <;> cases c : agree i <;>
        simp [List.countP_cons, a, b, c] at * <;> omega
  apply Classical.byContradiction
  intro ne
  have k := kernelCap ne
  have bound := cover bothGood
  omega

end ChecksumSelectorDistance
