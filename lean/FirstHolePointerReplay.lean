/- A chronology-sensitive proof for a sparse memory function with any fixed
   set of initially unknown cells. Their location is available to preprocessing;
   their numerical replies are supplied separately to each query. -/
namespace FirstHolePointerReplay

variable {W T : Type}
def orbit (f : W → W) (u : W) : Nat → W
  | 0 => u
  | n+1 => f (orbit f u n)

def clean (f : W → W) (overlay : W → Option W) (u : W) (k : Nat) :=
  ∀ j, j < k → overlay (orbit f u j) = none

def labelValid (f : W → W) (overlay : W → Option W) (u : W) :
    Option (Nat × W) → Prop
  | none => ∀ j, overlay (orbit f u j) = none
  | some (j,a) => orbit f u j = a ∧ overlay a ≠ none ∧ clean f overlay u j

def overlayFromLabel (overlay : W → Option W) (k : Nat) :
    Option (Nat × W) → Option W
  | none => none
  | some (j,a) => if j = k then overlay a else none

theorem first_hole_reply (f : W → W) (overlay : W → Option W)
    (u : W) (k : Nat) (l : Option (Nat × W)) (ok : labelValid f overlay u l)
    (clear : clean f overlay u k) :
    overlayFromLabel overlay k l = overlay (orbit f u k) := by
  cases l with
  | none => exact (ok k).symm
  | some tup =>
    obtain ⟨j,a⟩ := tup
    obtain ⟨hat, hpresent, hprior⟩ := ok
    by_cases heq : j = k
    · subst k
      simp [overlayFromLabel, hat]
    · by_cases hk : k < j
      · simp [overlayFromLabel, heq, hprior k hk]
      · have hj : j < k := by omega
        exact False.elim (hpresent (hat ▸ clear j hj))

def update (f : W → W) (overlay : W → Option W) (writes : T → W → Option W)
    (label : W → Option (Nat × W)) (state : W × Nat) (t : T) : W × Nat :=
  match writes t (orbit f state.1 state.2) with
  | some v => (v,0)
  | none =>
    match overlayFromLabel overlay state.2 (label state.1) with
    | some v => (v,0)
    | none => (state.1,state.2+1)

def readAt (f : W → W) (overlay : W → Option W)
    (writes : T → W → Option W) (x : W) (t : T) : W :=
    (writes t x).getD ((overlay x).getD (f x))

theorem step_valid (f : W → W) (ov : W → Option W) (writes : T → W → Option W)
    (label : W → Option (Nat × W)) (valid : ∀ u, labelValid f ov u (label u))
    (s : W × Nat) (t : T) (clear : clean f ov s.1 s.2) :
    let p := update f ov writes label s t
    clean f ov p.1 p.2 ∧ orbit f p.1 p.2 = readAt f ov writes (orbit f s.1 s.2) t := by
  obtain ⟨u,k⟩ := s
  have hreply := first_hole_reply f ov u k (label u) (valid u) clear
  cases hwrite : writes t (orbit f u k) with
  | some v =>
    simp [update, readAt, hwrite, clean, orbit]
  | none =>
    cases hvalue : ov (orbit f u k) with
    | some v =>
      simp [update, readAt, hwrite, hreply, hvalue, clean, orbit]
    | none =>
      simp only [update, readAt, hwrite, hreply, hvalue, Option.getD_none,
        orbit, and_true]
      intro j hj
      by_cases h : j = k
      · simpa [h] using hvalue
      · apply clear
        omega

theorem replay (f : W → W) (ov : W → Option W) (writes : T → W → Option W)
    (label : W → Option (Nat × W)) (valid : ∀ u, labelValid f ov u (label u))
    (times : List T) (s : W × Nat) (clear : clean f ov s.1 s.2) :
    let out := times.foldl (update f ov writes label) s
    orbit f out.1 out.2 = times.foldl (readAt f ov writes) (orbit f s.1 s.2) := by
  induction times generalizing s with
  | nil => rfl
  | cons t ts ih =>
    have ⟨nextClean, nextValue⟩ := step_valid f ov writes label valid s t clear
    simp only [List.foldl_cons]
    rw [ih _ nextClean, nextValue]

#print axioms first_hole_reply
#print axioms replay
end FirstHolePointerReplay
