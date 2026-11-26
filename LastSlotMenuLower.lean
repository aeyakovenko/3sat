import Std

/-! A finite menu of layouts for an adaptive reader. A reply `none` is the
distinguished query. A non-query label may occur at most once in each layout.
Full permutations of the data and the query satisfy this condition. -/
namespace LastSlotMenuLower

structure Layout (Address Label : Type) where
  read : Address → Option Label
  uniqueData : ∀ {i j a}, read i = some a → read j = some a → i = j

variable {Address Label : Type} [DecidableEq Address] [DecidableEq Label]

def fiber (menu : List (Layout Address Label)) (i : Address) (a : Label) :=
  menu.filter fun layout => decide (layout.read i = some a)

/-- The reader chooses an unqueried address, then the responder chooses a
remaining ordinary label. The responder must keep a genuine member of the
original menu consistent with all replies, ending with the query unread. -/
def KeepsLast : Nat → List Address → List Label → List (Layout Address Label) → Prop
  | 0, addresses, _, menu =>
      ∃ layout ∈ menu, ∀ i ∈ addresses, layout.read i = none
  | p + 1, addresses, labels, menu =>
      ∀ i ∈ addresses, ∃ a ∈ labels,
        KeepsLast p (addresses.erase i) (labels.erase a) (fiber menu i a)

omit [DecidableEq Address] in
private theorem shared_reply (R : Address → Label → Prop)
    (addresses : List Address) (labels : List Label)
    (fresh : addresses.Nodup) (more : labels.length < addresses.length)
    (total : ∀ i ∈ addresses, ∃ a ∈ labels, R i a) :
    ∃ i ∈ addresses, ∃ j ∈ addresses, i ≠ j ∧ ∃ a ∈ labels, R i a ∧ R j a := by
  induction addresses generalizing labels with
  | nil => simp at more
  | cons i tail ih =>
    obtain ⟨iFresh, tailFresh⟩ := List.nodup_cons.mp fresh
    obtain ⟨a, ha, hia⟩ := total i (by simp)
    by_cases other : ∃ j ∈ tail, R j a
    · obtain ⟨j, hj, hja⟩ := other
      exact ⟨i, by simp, j, by simp [hj], fun eq => iFresh (eq ▸ hj),
        a, ha, hia, hja⟩
    · have remaining : (labels.erase a).length < tail.length := by
        rw [List.length_erase_of_mem ha]
        simp only [List.length_cons] at more
        have positive := List.length_pos_iff_exists_mem.mpr ⟨a, ha⟩
        omega
      have tailTotal : ∀ j ∈ tail, ∃ b ∈ labels.erase a, R j b := by
        intro j hj
        obtain ⟨b, hb, rjb⟩ := total j (by simp [hj])
        have ne : b ≠ a := fun eq => other ⟨j, hj, eq ▸ rjb⟩
        exact ⟨b, (List.mem_erase_of_ne ne).2 hb, rjb⟩
      obtain ⟨j, hj, k, hk, ne, b, hb, rjb, rkb⟩ :=
        ih (labels.erase a) tailFresh remaining tailTotal
      exact ⟨j, by simp [hj], k, by simp [hk], ne, b,
        List.mem_of_mem_erase hb, rjb, rkb⟩

private theorem two_filters {α : Type} (f g : α → Bool) (xs : List α)
    (apart : ∀ x, f x = true → g x = true → False) :
    (xs.filter f).length + (xs.filter g).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hf : f x <;> cases hg : g x
    all_goals first | exact (apart x hf hg).elim | simp [List.filter, hf, hg] <;> omega

omit [DecidableEq Address] in
/-- The two surviving submenus for a repeated reply at different addresses
are disjoint, even when not all labels or addresses occur in every layout. -/
theorem two_fibers (menu : List (Layout Address Label)) {i j : Address}
    (ne : i ≠ j) (a : Label) :
    (fiber menu i a).length + (fiber menu j a).length ≤ menu.length := by
  apply two_filters
  intro layout hi hj
  exact ne (layout.uniqueData (of_decide_eq_true hi) (of_decide_eq_true hj))

/-- With p remaining data labels and p+1 remaining addresses, keeping the
query for last against every adaptive choice requires at least 2^p layouts.
For a menu listed without repetitions, its length is its cardinality. -/
theorem exponential_menu (p : Nat) (addresses : List Address) (labels : List Label)
    (menu : List (Layout Address Label)) (fresh : addresses.Nodup)
    (ha : addresses.length = p + 1) (hl : labels.length = p)
    (win : KeepsLast p addresses labels menu) : 2 ^ p ≤ menu.length := by
  induction p generalizing addresses labels menu with
  | zero =>
    obtain ⟨layout, hm, _⟩ := win
    have positive := List.length_pos_iff_exists_mem.mpr ⟨layout, hm⟩
    simpa using positive
  | succ p ih =>
    let R (i : Address) (a : Label) :=
      KeepsLast p (addresses.erase i) (labels.erase a) (fiber menu i a)
    obtain ⟨i, hi, j, hj, ne, a, ha', wi, wj⟩ :=
      shared_reply R addresses labels fresh (by omega) win
    have labelLen : (labels.erase a).length = p := by
      rw [List.length_erase_of_mem ha', hl]
      omega
    have step (q : Address) (hq : q ∈ addresses) (wq : R q a) :
        2 ^ p ≤ (fiber menu q a).length := by
      apply ih (addresses.erase q) (labels.erase a) (fiber menu q a)
        (fresh.erase q) _ labelLen wq
      rw [List.length_erase_of_mem hq, ha]
      omega
    have left := step i hi wi
    have right := step j hj wj
    have both := two_fibers menu ne a
    rw [Nat.pow_succ]
    omega

/-- A reader tree chooses a fresh address and can branch separately on every
legal previously unseen reply. A query or illegal reply ends the attempt. -/
inductive Reader : Nat → List Address → List Label → Type where
  | stop : Reader 0 addresses labels
  | ask {p addresses labels} (i : Address) (available : i ∈ addresses)
      (next : (a : {a // a ∈ labels}) →
        Reader p (addresses.erase i) (labels.erase a.val)) :
      Reader (p + 1) addresses labels

def passes (layout : Layout Address Label) :
    {p : Nat} → {addresses : List Address} → {labels : List Label} →
    Reader p addresses labels → Prop
  | _, addresses, _, .stop => ∀ i ∈ addresses, layout.read i = none
  | _, _, _, .ask i _ next =>
      ∃ a, layout.read i = some a.val ∧ passes layout (next a)

/-- Finite determinacy supplies the quantifier reversal: a single layout may
be chosen *after* the reader's whole adaptive strategy has been specified. -/
theorem universal_iff (p : Nat) (addresses : List Address) (labels : List Label)
    (menu : List (Layout Address Label)) :
    KeepsLast p addresses labels menu ↔
      ∀ reader : Reader p addresses labels, ∃ layout ∈ menu, passes layout reader := by
  induction p generalizing addresses labels menu with
  | zero =>
    constructor
    · intro win reader
      cases reader
      exact win
    · intro all
      exact all .stop
  | succ p ih =>
    constructor
    · intro win reader
      cases reader with
      | ask i hi next =>
        obtain ⟨a, ha, child⟩ := win i hi
        obtain ⟨layout, member, pass⟩ :=
          (ih _ _ _).mp child (next ⟨a, ha⟩)
        obtain ⟨hm, eq⟩ := List.mem_filter.mp member
        exact ⟨layout, hm, ⟨a, ha⟩, of_decide_eq_true eq, pass⟩
    · classical
      intro all i hi
      apply Classical.byContradiction
      intro noneWins
      have escape (a : {a // a ∈ labels}) :
          ∃ reader : Reader p (addresses.erase i) (labels.erase a.val),
            ¬ ∃ layout ∈ fiber menu i a.val, passes layout reader := by
        apply Classical.byContradiction
        intro noneEscape
        apply noneWins
        refine ⟨a.val, a.property, (ih _ _ _).mpr ?_⟩
        intro reader
        exact Classical.byContradiction (fun hn => noneEscape ⟨reader, hn⟩)
      let next := fun a => Classical.choose (escape a)
      obtain ⟨layout, hm, a, eq, pass⟩ := all (.ask i hi next)
      exact Classical.choose_spec (escape a) ⟨layout,
        List.mem_filter.mpr ⟨hm, decide_eq_true eq⟩, pass⟩

private theorem nodup_representatives {α : Type} (xs : List α) :
    ∃ ys : List α, ys.Nodup ∧ ∀ x, x ∈ ys ↔ x ∈ xs := by
  classical
  induction xs with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons x xs ih =>
    obtain ⟨ys, hy, repr⟩ := ih
    by_cases mem : x ∈ ys
    · refine ⟨ys, hy, ?_⟩
      intro z
      simp only [List.mem_cons]
      exact ⟨fun hz => Or.inr ((repr z).mp hz),
        fun h => h.elim (fun hz => hz ▸ mem) ((repr z).mpr)⟩
    · exact ⟨x :: ys, List.nodup_cons.mpr ⟨mem, hy⟩, by simp [repr]⟩

/-- Even a menu with repetitions contains at least 2^p *distinct* layouts
when every deterministic reader tree can be beaten by one of its members. -/
theorem distinct_layouts (p : Nat) (addresses : List Address) (labels : List Label)
    (menu : List (Layout Address Label)) (fresh : addresses.Nodup)
    (ha : addresses.length = p + 1) (hl : labels.length = p)
    (all : ∀ reader : Reader p addresses labels,
      ∃ layout ∈ menu, passes layout reader) :
    ∃ representatives : List (Layout Address Label),
      representatives.Nodup ∧
      (∀ l, l ∈ representatives ↔ l ∈ menu) ∧ 2 ^ p ≤ representatives.length := by
  obtain ⟨ys, hy, repr⟩ := nodup_representatives menu
  refine ⟨ys, hy, repr, exponential_menu p addresses labels ys fresh ha hl ?_⟩
  apply (universal_iff _ _ _ _).mpr
  intro reader
  obtain ⟨layout, hm, pass⟩ := all reader
  exact ⟨layout, (repr layout).mpr hm, pass⟩

/-- Only the active addresses matter when playing against a reader tree. -/
theorem passes_congr {p : Nat} {addresses : List Address} {labels : List Label}
    (reader : Reader p addresses labels) (left right : Layout Address Label)
    (eqRead : ∀ i ∈ addresses, left.read i = right.read i)
    (passed : passes left reader) : passes right reader := by
  induction reader with
  | stop =>
    intro i hi
    rw [← eqRead i hi]
    exact passed i hi
  | ask i hi next ih =>
    obtain ⟨a, eq, cont⟩ := passed
    exact ⟨a, (eqRead i hi).symm.trans eq,
      ih a (fun x hx => eqRead x (List.mem_of_mem_erase hx)) cont⟩

namespace Chain

private theorem passes_reindex {p : Nat} {xs ys labs labs' : List Nat}
    (hx : xs = ys) (hy : labs = labs') (reader : Reader p xs labs)
    (w : Layout Nat Nat) :
    passes w (cast (by rw [hx, hy]) reader : Reader p ys labs') ↔ passes w reader := by
  subst ys
  subst labs'
  rfl

/-- Along the selected subsequence each address carries its successor's name.
The final selected address carries the query. All other addresses name themselves. -/
def walk (head : Nat) : List Nat → Nat → Option Nat
  | [], i => if i = head then none else some i
  | a :: tail, i => if i = head then some a else walk a tail i

private theorem unmarked (head i : Nat) (tail : List Nat)
    (absent : i ∉ head :: tail) : walk head tail i = some i := by
  induction tail generalizing head with
  | nil => simpa [walk] using (show i ≠ head from by simpa using absent)
  | cons a tail ih =>
    have hi : i ≠ head := fun h => absent (by simp [h])
    have ht : i ∉ a :: tail := fun h => absent (List.mem_cons_of_mem _ h)
    simpa [walk, hi] using ih a ht

private theorem omitsHead (head : Nat) (tail : List Nat)
    (fresh : (head :: tail).Nodup) (i : Nat) : walk head tail i ≠ some head := by
  induction tail generalizing head with
  | nil => by_cases eq : i = head <;> simp [walk, eq]
  | cons a tail ih =>
    have hmiss := (List.nodup_cons.mp fresh).1
    have sep : a ≠ head := fun e => hmiss (by simp [e])
    by_cases eq : i = head
    · simp [walk, eq, sep]
    · simp only [walk, if_neg eq]
      by_cases present : i ∈ a :: tail
      · clear ih
        have range (s : Nat) (xs : List Nat) (key : Nat) (inside : key ∈ s :: xs)
            (found : walk s xs key = some head) : head ∈ xs := by
          induction xs generalizing s with
          | nil => simp_all [walk]
          | cons y ys step =>
            by_cases isHead : key = s
            · have := Option.some.inj (by simpa [walk, isHead] using found)
              simp_all
            · have inside' : key ∈ y :: ys := (List.mem_cons.mp inside).resolve_left isHead
              exact List.mem_cons_of_mem _ (step y inside' (by simpa [walk, isHead] using found))
        exact fun e => hmiss (List.mem_cons_of_mem _ (range a tail i present e))
      · simp [unmarked a i tail present, eq]

private theorem one_per_label (head : Nat) (tail : List Nat)
    (fresh : (head :: tail).Nodup) {i j a : Nat}
    (hi : walk head tail i = some a) (hj : walk head tail j = some a) : i = j := by
  induction tail generalizing head with
  | nil =>
    by_cases ei : i = head <;> by_cases ej : j = head <;> simp_all [walk]
  | cons h tail ih =>
    have inner := (List.nodup_cons.mp fresh).2
    by_cases ei : i = head <;> by_cases ej : j = head
    · exact ei.trans ej.symm
    · have eq : h = a := by simpa [walk, ei] using hi
      exact (omitsHead h tail inner j (by simpa [walk, ej, ← eq] using hj)).elim
    · have eq : h = a := by simpa [walk, ej] using hj
      exact (omitsHead h tail inner i (by simpa [walk, ei, ← eq] using hi)).elim
    · exact ih h inner (by simpa [walk, ei] using hi) (by simpa [walk, ej] using hj)

def layout (head : Nat) (tail : List Nat) : Layout Nat Nat where
  read i := if (head :: tail).Nodup then walk head tail i else none
  uniqueData := by
    intro i j a hi hj
    by_cases h : (head :: tail).Nodup
    · exact one_per_label head tail h (by simpa [h] using hi) (by simpa [h] using hj)
    · simp [h] at hi

def subsequences : List Nat → List (List Nat)
  | [] => [[]]
  | a :: xs => let prev := subsequences xs; prev ++ prev.map (a :: ·)

theorem count_subsequences (xs : List Nat) : (subsequences xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [subsequences, ih, Nat.pow_succ, Nat.mul_two]

private theorem listed {xs ys : List Nat} (sub : xs.Sublist ys) : xs ∈ subsequences ys := by
  induction sub with
  | slnil => simp [subsequences]
  | cons a _ ih => simp [subsequences, ih]
  | cons₂ a _ ih => simp [subsequences, ih]

private theorem beats (p : Nat) (h : Nat) (t : List Nat) (fresh : (h :: t).Nodup)
    (hl : t.length = p) (reader : Reader p (h :: t) t) :
    ∃ s, s.Sublist t ∧ passes (layout h s) reader := by
  induction p generalizing h t with
  | zero =>
    obtain rfl : t = [] := List.length_eq_zero_iff.mp hl
    cases reader
    exact ⟨[], .slnil, by simp [passes, layout, walk]⟩
  | succ p ih =>
    cases t with
    | nil => simp at hl
    | cons b bs =>
      cases reader with
      | ask i hi next =>
        by_cases eq : i = h
        · subst i
          let a : {x // x ∈ b :: bs} := ⟨b, by simp⟩
          let child : Reader p (b :: bs) bs := by simpa [a] using next a
          obtain ⟨s, sub, passed⟩ := ih b bs (List.nodup_cons.mp fresh).2 (by simpa using hl) child
          have hs : (b :: s).Nodup := List.Nodup.sublist (sub.cons₂ b) (List.nodup_cons.mp fresh).2
          have hfull := List.Nodup.sublist ((sub.cons₂ b).cons₂ h) fresh
          refine ⟨b :: s, sub.cons₂ b, a, by simp [layout, hfull, walk, a], ?_⟩
          have newPass := passes_congr child (layout b s) (layout h (b :: s))
            (fun j hj => by
              have ne : j ≠ h := fun e => (List.nodup_cons.mp fresh).1 (e ▸ hj)
              simp [layout, hs, hfull, walk, ne]) passed
          exact (passes_reindex (show (h :: b :: bs).erase h = b :: bs by simp)
            (show (b :: bs).erase b = bs by simp) (next a) _).mp newPass
        · have hiTail : i ∈ b :: bs := (List.mem_cons.mp hi).resolve_left eq
          let a : {x // x ∈ b :: bs} := ⟨i, hiTail⟩
          have hneq : ¬(h == i) := by simpa using Ne.symm eq
          let child : Reader p (h :: (b :: bs).erase i) ((b :: bs).erase i) := by
            simpa [a, List.erase_cons_tail hneq] using next a
          have childFresh : (h :: (b :: bs).erase i).Nodup :=
            List.Nodup.sublist (List.erase_sublist.cons₂ h) fresh
          have len : ((b :: bs).erase i).length = p := by
            rw [List.length_erase_of_mem hiTail, hl]
            omega
          obtain ⟨s, sub, passed⟩ := ih h _ childFresh len child
          have whole := sub.trans List.erase_sublist
          have hs := List.Nodup.sublist (whole.cons₂ h) fresh
          have miss : i ∉ s := fun mem => ((List.nodup_cons.mp fresh).2.not_mem_erase) (sub.subset mem)
          refine ⟨s, whole, a, ?_, ?_⟩
          · simp [layout, hs, a, unmarked h i s (by simp [eq, miss])]
          · exact (passes_reindex (List.erase_cons_tail hneq) rfl (next a) _).mp passed

/-- An explicit list of 2^p layouts beats every reader on any ordered list
of p+1 distinct addresses. Ordinary labels are the p noninitial addresses. -/
theorem matching_upper (h : Nat) (t : List Nat) (fresh : (h :: t).Nodup) :
    let menu := (subsequences t).map (layout h)
    menu.length = 2 ^ t.length ∧ KeepsLast t.length (h :: t) t menu := by
  refine ⟨by simp [count_subsequences], (universal_iff _ _ _ _).mpr ?_⟩
  intro reader
  obtain ⟨s, sub, pass⟩ := beats t.length h t fresh rfl reader
  exact ⟨layout h s, List.mem_map.mpr ⟨s, listed sub, rfl⟩, pass⟩

end Chain
end LastSlotMenuLower
