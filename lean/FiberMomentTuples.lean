import Std

namespace FiberMomentTuples

def words (alphabet : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => alphabet.flatMap (fun a => (words alphabet n).map (a :: ·))

private theorem listed (alphabet : List Nat) (n : Nat) (w : List Nat) :
    w ∈ words alphabet n ↔ w.length = n ∧ ∀ x ∈ w, x ∈ alphabet := by
  induction n generalizing w with
  | zero => cases w <;> simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons x xs => simp [words, ih, and_left_comm]

private theorem countWords (alphabet : List Nat) (n : Nat) :
    (words alphabet n).length = alphabet.length^n := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    simp only [words, List.length_flatMap, List.length_map, ih, Nat.pow_succ]
    have constSum (ls : List Nat) (c : Nat) : (ls.map (fun _ => c)).sum = c * ls.length := by
      induction ls with
      | nil => simp
      | cons l ls il => simp [il, Nat.mul_succ, Nat.add_comm]
    exact constSum _ _

private theorem distinctWords (alphabet : List Nat) (nd : alphabet.Nodup) (n : Nat) :
    (words alphabet n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    apply List.pairwise_flatMap.2
    constructor
    · intro a _
      exact List.pairwise_map.2 (ih.imp (fun h he => h (List.cons.inj he).2))
    · apply nd.imp
      intro a b ne u hu v hv he
      obtain ⟨u',_,rfl⟩ := List.mem_map.1 hu
      obtain ⟨v',_,rfl⟩ := List.mem_map.1 hv
      exact ne (List.cons.inj he).1

private theorem includedSize {α : Type} [DecidableEq α] (xs ys : List α) (nd : xs.Nodup)
    (mem : ∀ a ∈ xs, a ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp nd
    have ha := mem a (by simp)
    have pos := List.length_pos_of_mem ha
    have tail := ih (ys.erase a) rest (by
      intro x hx
      have ne : x ≠ a := fun h => fresh (h ▸ hx)
      exact (List.mem_erase_of_ne ne).2 (mem x (by simp [hx])))
    rw [List.length_erase_of_mem ha] at tail
    simp; omega

private theorem countBudget (labels : List Nat) (nd : labels.Nodup) (w : List Nat) :
    (labels.map (fun a => w.count a)).sum ≤ w.length := by
  induction w with
  | nil =>
    induction labels with
    | nil => simp
    | cons a as ih => simpa using ih (List.nodup_cons.mp nd).2
  | cons x w iw =>
    have increment (ls : List Nat) :
        (ls.map (fun a => (x :: w).count a)).sum =
          (ls.map (fun a => w.count a)).sum + ls.count x := by
      induction ls with
      | nil => simp
      | cons a as ih =>
        by_cases hx : a = x
        · subst a
          simp only [List.map_cons, List.sum_cons, List.count_cons_self, ih]
          omega
        · simp only [List.map_cons, List.sum_cons, List.count_cons_of_ne hx,
            List.count_cons_of_ne (Ne.symm hx), ih]
          omega
    rw [increment]
    have cap : labels.count x ≤ 1 := by
      induction labels with
      | nil => simp
      | cons a as ih =>
        obtain ⟨fresh,rest⟩ := List.nodup_cons.mp nd
        by_cases eq : a = x
        · subst a; simp [List.count_eq_zero_of_not_mem fresh]
        · rw [List.count_cons_of_ne eq]
          exact ih rest (by
            have h := iw
            simp only [List.map_cons, List.sum_cons] at h
            omega)
    simp; omega

private theorem minCounts (labels w : List Nat) (heavy : ∀ x ∈ labels, 2 ≤ w.count x) :
    2 * labels.length ≤ (labels.map (fun a => w.count a)).sum := by
  induction labels with
  | nil => simp
  | cons a as ih =>
    have head := heavy a (by simp)
    have tail := ih (fun x hx => heavy x (by simp [hx]))
    simp [Nat.mul_succ]; omega

/-- Every surviving term in a centered 2h-th moment can be indexed by
    h alphabet symbols (allowing padding) and 2h choices among them. -/
theorem noSingletonCount (N h : Nat) (positive : 0 < N) :
    ((words (List.range N) (2*h)).filter
      (fun w => w.all (fun x => decide (2 ≤ w.count x)))).length ≤ N^h * h^(2*h) := by
  let source := List.range N
  let survivors := (words source (2*h)).filter (fun w => w.all (fun x => decide (2 ≤ w.count x)))
  let encodings := (words source h).flatMap (fun dict => words dict (2*h))
  have nd : survivors.Nodup := (distinctWords source List.nodup_range _).filter _
  have bound := includedSize survivors encodings nd (by
    intro w hw
    obtain ⟨hw,counts⟩ := List.mem_filter.1 hw
    obtain ⟨length,legal⟩ := (listed ..).1 hw
    let support := source.filter (fun a => decide (a ∈ w))
    have inSupport (a : Nat) (ha : a ∈ w) : a ∈ support :=
      List.mem_filter.2 ⟨legal a ha, by simpa using ha⟩
    have ss : support.Nodup := List.nodup_range.filter _
    have lo := minCounts support w (by
      intro a ha
      have hw' : a ∈ w := by simpa using (List.mem_filter.1 ha).2
      simpa using (List.all_eq_true.1 counts) a hw')
    have hi := countBudget support ss w
    have small : support.length ≤ h := by omega
    let dict := support ++ List.replicate (h-support.length) 0
    apply List.mem_flatMap.2
    refine ⟨dict,(listed ..).2 ⟨by simp [dict]; omega, ?_⟩, (listed ..).2 ⟨length,?_⟩⟩
    · intro a ha
      rcases List.mem_append.1 ha with hs | hp
      · exact (List.mem_filter.1 hs).1
      · have az := (List.mem_replicate.1 hp).2
        simpa [source, az] using positive
    · intro a ha; exact List.mem_append_left _ (inSupport a ha))
  have encSize : encodings.length = N^h * h^(2*h) := by
    simp only [encodings, List.length_flatMap, countWords]
    have sumConst (ls : List (List Nat)) (eqLen : ∀ w ∈ ls, w.length = h) :
        (ls.map (fun w => w.length^(2*h))).sum = ls.length * h^(2*h) := by
      induction ls with
      | nil => simp
      | cons w ws ih =>
        have hw := eqLen w (by simp)
        have rest := ih (fun w' hw' => eqLen w' (by simp [hw']))
        simp only [List.map_cons, List.sum_cons, hw, rest, List.length_cons]
        rw [Nat.succ_mul ws.length (h^(2*h)), Nat.add_comm]
    rw [sumConst _ (fun w hw => ((listed ..).1 hw).1), countWords]
    simp [source]
  exact encSize ▸ bound

end FiberMomentTuples
