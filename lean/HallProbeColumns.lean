import Std

namespace HallProbeColumns

private theorem count_subset {α : Type} [DecidableEq α] {xs ys : List α}
    (distinct : xs.Nodup) (inside : ∀ a ∈ xs, a ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp distinct
    have found := inside a (by simp)
    have pos := List.length_pos_of_mem found
    have shorter := ih tail (ys := ys.erase a) (by
      intro b hb
      have diff : b ≠ a := fun e => fresh (e ▸ hb)
      exact (List.mem_erase_of_ne diff).mpr (inside b (by simp [hb])))
    rw [List.length_erase_of_mem found] at shorter
    simp
    omega

variable {Code : Type}
structure HallPair (j : Nat) (edge : Nat → Code → Prop) where
  rows : List Nat
  codes : List Code
  distinct : rows.Nodup
  prefixRows : ∀ h ∈ rows, h ≤ j
  covers : ∀ h ∈ rows, ∀ c, edge h c → c ∈ codes
  deficit : codes.length < rows.length

structure EarlierMatching (j : Nat) (edge : Nat → Code → Prop) where
  pick : Nat → Code
  hits : ∀ h < j, edge h (pick h)
  unique : ∀ a < j, ∀ b < j, pick a = pick b → a = b

/-- Given the first failed index, one positive matching of the earlier rows
    suffices to read every row-independent bit. No Hall pair is supplied. -/
theorem probe_in_positive_matching {j edge} (m : EarlierMatching (Code := Code) j edge)
    (fails : ¬ Nonempty (EarlierMatching (j + 1) edge)) (c : Code) (answer : Prop)
    (independent : ∀ h ≤ j, edge h c ↔ answer) :
    (∃ h < j, m.pick h = c) ↔ answer := by
  constructor
  · rintro ⟨h, before, rfl⟩
    exact (independent h (by omega)).mp (m.hits h before)
  · intro yes
    apply Classical.byContradiction
    intro missing
    apply fails
    let extended (h : Nat) := if h = j then c else m.pick h
    refine ⟨{ pick := extended, hits := ?_, unique := ?_ }⟩
    · intro h bounded
      by_cases last : h = j
      · subst h
        simpa [extended] using (independent j (Nat.le_refl _)).mpr yes
      · simpa [extended, last] using m.hits h (by omega)
    · intro a ha b hb equal
      by_cases endA : a = j <;> by_cases endB : b = j
      · exact endA.trans endB.symm
      · have used : m.pick b = c := by simpa [extended, endA, endB] using equal.symm
        exact False.elim (missing ⟨b, by omega, used⟩)
      · have used : m.pick a = c := by simpa [extended, endA, endB] using equal
        exact False.elim (missing ⟨a, by omega, used⟩)
      · exact m.unique a (by omega) b (by omega) (by simpa [extended, endA, endB] using equal)

variable [DecidableEq Code]

/-- Any deficient pair at the first failed prefix is tight, even when the
    row set is not minimal and the column list was only claimed to cover it. -/
theorem exact_pair {j edge} (m : EarlierMatching (Code := Code) j edge)
    (w : HallPair j edge) : j ∈ w.rows ∧ w.codes.length + 1 = w.rows.length ∧
      ∀ c, c ∈ w.codes ↔ ∃ h ∈ w.rows, edge h c := by
  let prior := w.rows.erase j
  have old (h : Nat) (hh : h ∈ prior) : h < j := by
    have bounded := w.prefixRows h (List.mem_of_mem_erase hh)
    have ne : h ≠ j := fun same => w.distinct.not_mem_erase (same ▸ hh)
    omega
  have distinct : (prior.map m.pick).Nodup := by
    apply List.pairwise_map.mpr
    exact List.Pairwise.imp_of_mem (fun ha hb ne equal =>
      ne (m.unique _ (old _ ha) _ (old _ hb) equal)) (w.distinct.erase j)
  have witness (c : Code) (hc : c ∈ prior.map m.pick) : ∃ h ∈ w.rows, edge h c := by
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hc
    exact ⟨h, List.mem_of_mem_erase hh, m.hits h (old h hh)⟩
  have inside (c : Code) (hc : c ∈ prior.map m.pick) : c ∈ w.codes := by
    obtain ⟨h, hh, yes⟩ := witness c hc
    exact w.covers h hh c yes
  have enough := count_subset distinct inside
  simp only [List.length_map] at enough
  have short := w.deficit
  have last : j ∈ w.rows := by
    apply Classical.byContradiction
    intro missing
    have eq : prior = w.rows := List.erase_of_not_mem missing
    rw [eq] at enough
    omega
  have shrink : prior.length = w.rows.length - 1 := List.length_erase_of_mem last
  refine ⟨last, by omega, fun c => ⟨?_, ?_⟩⟩
  · intro member
    apply Classical.byContradiction
    intro absent
    have fresh : c ∉ prior.map m.pick := fun hc => absent (witness c hc)
    have augmented := count_subset (List.nodup_cons.mpr ⟨fresh, distinct⟩) (ys := w.codes) (by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | prev
      · exact member
      · exact inside b prev)
    simp only [List.length_cons, List.length_map] at augmented
    omega
  · rintro ⟨h, hh, yes⟩
    exact w.covers h hh c yes

/-- A row-independent probe is read from membership in any genuine pair. -/
theorem probe_membership {j edge} (m : EarlierMatching (Code := Code) j edge)
    (w : HallPair j edge) (c : Code) (answer : Prop)
    (independent : ∀ h ∈ w.rows, edge h c ↔ answer) : c ∈ w.codes ↔ answer := by
  obtain ⟨last, _, exactCode⟩ := exact_pair m w
  constructor
  · intro member
    obtain ⟨h, hh, yes⟩ := (exactCode c).mp member
    exact (independent h hh).mp yes
  · intro yes
    exact w.covers j last c ((independent j last).mpr yes)

/-- A family of probes accepting an inner prefix recovers the entire threshold. -/
theorem threshold_family {j edge} (m : EarlierMatching (Code := Code) j edge)
    (w : HallPair j edge) (probe : Nat → Code) (width cut : Nat)
    (exposes : ∀ a < width, ∀ h ∈ w.rows, edge h (probe a) ↔ a < cut) :
    ∀ a < width, probe a ∈ w.codes ↔ a < cut := by
  intro a ha
  exact probe_membership m w _ _ (exposes a ha)

/-- Counting marked copies recovers a threshold uniquely when slack and
    missing neighbors leave an uncertainty interval narrower than one block. -/
theorem replicated_threshold_unique (copies slack misses observed a b : Nat)
    (separated : slack + 2 * misses < copies)
    (fitsA : observed ≤ copies * a + slack + misses ∧ copies * a ≤ observed + misses)
    (fitsB : observed ≤ copies * b + slack + misses ∧ copies * b ≤ observed + misses) :
    a = b := by
  have ordered (x y : Nat) (lower : copies * x ≤ observed + misses)
      (upper : observed ≤ copies * y + slack + misses) : x ≤ y := by
    apply Nat.le_of_not_gt
    intro less
    have bound := Nat.mul_le_mul_left copies (show y + 1 ≤ x by omega)
    rw [Nat.mul_succ] at bound
    omega
  exact Nat.le_antisymm (ordered a b fitsA.2 fitsB.1) (ordered b a fitsB.2 fitsA.1)

/-- With the public-coin tuple already fixed, separate addresses and repetitions
    may use different responses. The visible pin is true precisely when the
    predicate has a witness, by perfect completeness on the correct advice. -/
def Approves {Addr Sample Reply : Type} (verify : Addr → Bool → Sample → Reply → Prop)
    (u : Addr) (v : Bool) : Prop := ∀ i, ∃ a, verify u v i a

def Pinned {Addr Sample Reply : Type} (verify : Addr → Bool → Sample → Reply → Prop)
    (pin : Bool) (y : Addr → Bool) : Prop := pin = true ∧ ∀ u, Approves verify u (y u)

theorem pinned_verdict {Addr Sample Reply : Type} (verify : Addr → Bool → Sample → Reply → Prop)
    (g : Addr → Bool) (correct : ∀ u, Approves verify u (g u)) (pin : Bool) :
    (∃ y, Pinned verify pin y) ↔ pin = true :=
  ⟨fun ⟨_, passes⟩ => passes.1, fun yes => ⟨g, yes, correct⟩⟩

theorem forced_bitmap {Addr Sample Reply : Type} (verify : Addr → Bool → Sample → Reply → Prop)
    (g : Addr → Bool) (good : ∀ u v, Approves verify u v → v = g u)
    (pin : Bool) (y : Addr → Bool) (passes : Pinned verify pin y) : y = g := by
  funext u
  exact good u (y u) (passes.2 u)

/-- Different outer witnesses need agree only on this particular probe slice. -/
theorem common_probe_bitmap {Addr : Type} {j edge} (g : Addr → Bool) (probe : Addr → Code)
    (m : EarlierMatching j edge) (fails : ¬ Nonempty (EarlierMatching (j + 1) edge))
    (w : HallPair j edge) (good : ∀ h ≤ j, ∀ u, edge h (probe u) ↔ g u = true) :
    ∀ u, ((∃ h < j, m.pick h = probe u) ↔ g u = true) ∧ (probe u ∈ w.codes ↔ g u = true) := by
  intro u
  exact ⟨probe_in_positive_matching m fails _ _ (fun h hh => good h hh u),
    probe_membership m w _ _ (fun h hh => good h (w.prefixRows h hh) u)⟩

end HallProbeColumns
