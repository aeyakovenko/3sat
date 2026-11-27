import Std

namespace Adaptive

/-- A public binary protocol. Each internal node may ask any predicate of one table. -/
inductive Protocol (A B : Type) where
  | leaf (answer : Bool)
  | left (ask : A → Bool) (next : Bool → Protocol A B)
  | right (ask : B → Bool) (next : Bool → Protocol A B)

variable {A B : Type}

/-- The final bit records the leaf's output. -/
def path (p : Protocol A B) (x : A) (y : B) : List Bool :=
  match p with
  | .leaf answer => [answer]
  | .left ask next => ask x :: path (next (ask x)) x y
  | .right ask next => ask y :: path (next (ask y)) x y

theorem splice (p : Protocol A B) (x x' : A) (y y' : B)
    (h : path p x y = path p x' y') : path p x y' = path p x y := by
  induction p with
  | leaf => rfl
  | left ask next ih =>
    simp only [path, List.cons.injEq] at h ⊢
    obtain ⟨hq, ht⟩ := h
    rw [← hq] at ht
    exact ⟨True.intro, ih _ ht⟩
  | right ask next ih =>
    simp only [path, List.cons.injEq] at h ⊢
    obtain ⟨hq, ht⟩ := h
    rw [← hq] at ht ⊢
    exact ⟨rfl, ih _ ht⟩

/-- Every exactly correct public protocol distinguishes complementary pairs.
    Inputs are characteristic functions. The last path bit indicates intersection. -/
theorem complementary_paths_injective {U : Type}
    (p : Protocol (U → Bool) (U → Bool))
    (correct : ∀ x y, (path p x y).getLast? = some true ↔
      ∃ i, x i = true ∧ y i = true)
    (x z : U → Bool)
    (same : path p x (fun i => !(x i)) = path p z (fun i => !(z i))) :
    x = z := by
  have disjoint (a : U → Bool) : ¬ (path p a (fun i => !(a i))).getLast? = some true := by
    intro h
    obtain ⟨i, hi, hn⟩ := (correct ..).mp h
    simp [hi] at hn
  have le_of_path (a b : U → Bool)
      (h : path p a (fun i => !(a i)) = path p b (fun i => !(b i))) :
      ∀ i, a i = true → b i = true := by
    intro i ha
    cases hb : b i with
    | true => rfl
    | false =>
      exfalso
      apply disjoint a
      rw [← splice p a b (fun j => !(a j)) (fun j => !(b j)) h]
      apply (correct ..).mpr
      exact ⟨i, ha, by simp [hb]⟩
  funext i
  have f := le_of_path x z same i
  have g := le_of_path z x same.symm i
  cases hx : x i <;> cases hz : z i <;> simp_all

/-- A one-sided disjointness prover chooses a protocol. Complementary inputs
    with the same accepting certificate and path have the same first table. -/
theorem disjoint_certificates_distinguish {U C : Type}
    (protocol : C → Protocol (U → Bool) (U → Bool))
    (sound : ∀ c x y, (path (protocol c) x y).getLast? = some true →
      ∀ i, x i = true → y i = false)
    (choose : (U → Bool) → C)
    (completeOnComplements : ∀ a,
      (path (protocol (choose a)) a (fun i => !(a i))).getLast? = some true)
    (x z : U → Bool) (hc : choose x = choose z)
    (hp : path (protocol (choose x)) x (fun i => !(x i)) =
          path (protocol (choose z)) z (fun i => !(z i))) : x = z := by
  rw [← hc] at hp
  let p := protocol (choose x)
  have yesX : (path p x (fun i => !(x i))).getLast? = some true :=
    completeOnComplements x
  have yesZ : (path p z (fun i => !(z i))).getLast? = some true := by
    rw [← hp]
    exact yesX
  have xz : (path p x (fun i => !(z i))).getLast? = some true := by
    rw [splice _ _ _ _ _ hp]
    exact yesX
  have zx : (path p z (fun i => !(x i))).getLast? = some true := by
    rw [splice _ _ _ _ _ hp.symm]
    exact yesZ
  funext i
  have f := sound _ _ _ xz i
  have g := sound _ _ _ zx i
  cases hx : x i <;> cases hz : z i <;> simp_all

end Adaptive
