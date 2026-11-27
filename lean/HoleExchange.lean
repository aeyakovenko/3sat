import Std

namespace HoleExchange

variable {Row Label : Type}

/-- An edge-compatible assignment covers each label except its hole once. -/
structure Matching (edge : Row → Label → Prop) (f : Row → Label) (hole : Label) : Prop where
  injective : ∀ i j, f i = f j → i = j
  allowed : ∀ i, edge i (f i)
  covers : ∀ y, (∃ i, f i = y) ↔ y ≠ hole

def change [DecidableEq Row] (f : Row → Label) (hole : Label) (i j : Row) : Label :=
  if j = i then hole else f j

theorem exchange [DecidableEq Row] {edge : Row → Label → Prop} {f : Row → Label}
    {hole : Label} (valid : Matching edge f hole) (i : Row) (legal : edge i hole) :
    Matching edge (change f hole i) (f i) := by
  have occupied (j : Row) : f j ≠ hole := (valid.covers (f j)).1 ⟨j, rfl⟩
  constructor
  · intro j k equal
    by_cases hj : j = i <;> by_cases hk : k = i
    · exact hj.trans hk.symm
    · simp [change, hj, hk, Ne.symm (occupied k)] at equal
    · simp [change, hj, hk, occupied j] at equal
    · exact valid.injective j k (by simpa [change, hj, hk] using equal)
  · intro j
    by_cases hj : j = i
    · simpa [change, hj] using legal
    · simpa [change, hj] using valid.allowed j
  · intro y
    constructor
    · rintro ⟨j, hj⟩ same
      by_cases atRow : j = i
      · exact (occupied i).symm (by simpa [change, atRow, same] using hj)
      · exact atRow (valid.injective j i (by simpa [change, atRow, same] using hj))
    · intro different
      by_cases oldHole : y = hole
      · exact ⟨i, by simp [change, oldHole]⟩
      · obtain ⟨j,hj⟩ := (valid.covers y).2 oldHole
        have untouched : j ≠ i := by
          intro eq
          subst j
          exact different hj.symm
        exact ⟨j, by simpa [change, untouched] using hj⟩

/-- A walk in the original matching has arcs x → f(i) for each edge (i,x). -/
def Walk (edge : Row → Label → Prop) (f : Row → Label) (start : Label) :
    List Row → Label → Prop
  | [], target => start = target
  | i :: rest, target => edge i start ∧ Walk edge f (f i) rest target

private theorem suffix_walk {edge : Row → Label → Prop} {f : Row → Label}
    (before : List Row) {i : Row} {after : List Row} {start target : Label}
    (walk : Walk edge f start (before ++ i :: after) target) :
    Walk edge f (f i) after target := by
  induction before generalizing start with
  | nil => exact walk.2
  | cons j rest ih => exact ih walk.2

private theorem simplify_walk {edge : Row → Label → Prop} {f : Row → Label}
    {start target : Label} (rows : List Row) (walk : Walk edge f start rows target) :
    ∃ simple, simple.Nodup ∧ Walk edge f start simple target := by
  classical
  induction rows generalizing start with
  | nil => exact ⟨[], by simp, walk⟩
  | cons i rest ih =>
    obtain ⟨simple,distinct,tail⟩ := ih walk.2
    by_cases repeated : i ∈ simple
    · obtain ⟨before,after,eq⟩ := List.append_of_mem repeated
      subst simple
      exact ⟨i :: after, List.Nodup.sublist (List.sublist_append_right before _) distinct,
        walk.1, suffix_walk before tail⟩
    · exact ⟨i :: simple, List.nodup_cons.mpr ⟨repeated,distinct⟩, walk.1, tail⟩

private theorem follow_simple {edge : Row → Label → Prop} {f current : Row → Label}
    {hole target : Label} (valid : Matching edge current hole) (rows : List Row)
    (distinct : rows.Nodup) (unused : ∀ i ∈ rows, current i = f i)
    (walk : Walk edge f hole rows target) : ∃ g, Matching edge g target := by
  classical
  induction rows generalizing hole current with
  | nil =>
    have eq : hole = target := walk
    exact ⟨current, eq ▸ valid⟩
  | cons i rest ih =>
    have old := unused i (by simp)
    have moved := exchange valid i walk.1
    rw [old] at moved
    apply ih moved (List.nodup_cons.mp distinct).2 _ walk.2
    intro j hj
    have other : j ≠ i := fun eq => (List.nodup_cons.mp distinct).1 (eq ▸ hj)
    simpa [change, other] using unused j (by simp [hj])

theorem realize_walk {edge : Row → Label → Prop} {f : Row → Label} {hole target : Label}
    (valid : Matching edge f hole) (rows : List Row) (walk : Walk edge f hole rows target) :
    ∃ g, Matching edge g target := by
  obtain ⟨simple,distinct,path⟩ := simplify_walk rows walk
  exact follow_simple valid simple distinct (fun _ _ => rfl) path

private theorem extend_walk {edge : Row → Label → Prop} {f : Row → Label}
    (rows : List Row) {start x : Label} (path : Walk edge f start rows x)
    (i : Row) (lastEdge : edge i x) : Walk edge f start (rows ++ [i]) (f i) := by
  induction rows generalizing start with
  | nil =>
    have eq : start = x := path
    exact ⟨eq ▸ lastEdge, rfl⟩
  | cons j rest ih => exact ⟨path.1, ih path.2⟩

private theorem count_mono (rows : List Row) (p q : Row → Bool)
    (le : ∀ i, p i = true → q i = true) : rows.countP p ≤ rows.countP q := by
  induction rows with
  | nil => simp
  | cons i rest ih =>
    simp only [List.countP_cons]
    by_cases h : p i = true <;> by_cases h' : q i = true <;> simp_all <;> omega

/-- Finite converse. Each assignment with its single hole appended enumerates
    the same labels. Reachability is measured against the original assignment. -/
theorem endpoint_reachable {edge : Row → Label → Prop} (f g : Row → Label)
    (hole target : Label) (rows : List Row) (allowed : ∀ i, edge i (g i))
    (same_labels : (hole :: rows.map f).Perm (target :: rows.map g)) :
    ∃ route, Walk edge f hole route target := by
  classical
  let reachable := fun x => ∃ route, Walk edge f hole route x
  have start : reachable hole := ⟨[], rfl⟩
  have closed (i : Row) (h : reachable (g i)) : reachable (f i) := by
    obtain ⟨route,path⟩ := h
    exact ⟨route ++ [i], extend_walk route path i (allowed i)⟩
  apply Classical.byContradiction
  intro absent
  have missing : ¬reachable target := absent
  let mark := fun x => decide (reachable x)
  have count := same_labels.countP_eq mark
  have compare := count_mono rows (mark ∘ g) (mark ∘ f) (by
    intro i h
    exact decide_eq_true (closed i (of_decide_eq_true h)))
  have yes : mark hole = true := decide_eq_true start
  have no : mark target = false := decide_eq_false missing
  simp [List.countP_cons, List.countP_map, yes, no] at count
  omega

end HoleExchange
