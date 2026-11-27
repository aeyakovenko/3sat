import Std

/-! Times are natural numbers. A memory edge goes between consecutive
visits to the same cell on one tape. An abstract vertex may be any pair
(v,i); its home time visits both of its designated tape cells. -/

namespace TwoTapeGratePaths

inductive Walk (edge : V → V → Prop) (safe : V → Prop) : V → Nat → V → Prop
  | stay (v : V) (valid : safe v) : Walk edge safe v 0 v
  | extend {start u v : V} {n : Nat} (earlierPath : Walk edge safe start n u)
      (link : edge u v) (valid : safe v) : Walk edge safe start (n+1) v

theorem endSafe (w : Walk edge safe x n y) : safe y := by
  cases w with
  | stay hv => exact hv
  | extend _ _ hv => exact hv

theorem concatenate (first : Walk edge safe x m y) (second : Walk edge safe y n z) :
    Walk edge safe x (m+n) z := by
  induction second with
  | stay => exact first
  | extend _ link hv ih => exact .extend ih link hv

/-- Both endpoints visit c, and no strictly intermediate time visits c. -/
def consecutive (position : Nat → Cell) (c : Cell) (t u : Nat) : Prop :=
  position t = c ∧ position u = c ∧ t < u ∧
    ∀ v, t < v → v < u → position v ≠ c

def tapeEdge (positionA : Nat → A) (positionB : Nat → B) (t u : Nat) : Prop :=
  (∃ c, consecutive positionA c t u) ∨ (∃ c, consecutive positionB c t u)

def clean (deleted : Nat → Prop) (position : Nat → Cell) (c : Cell) : Prop :=
  ∀ t, position t = c → ¬ deleted t

/-- Every intervening visit to a clean cell survives. Split at any such
visit until each remaining pair gives a genuine consecutive-visit edge. -/
theorem cleanVisits (edge : Nat → Nat → Prop) (deleted : Nat → Prop)
    (position : Nat → Cell) (c : Cell)
    (includeVisit : ∀ i j, consecutive position c i j → edge i j)
    (safeCell : clean deleted position c)
    (t u : Nat) (ht : position t = c) (hu : position u = c) (earlier : t < u) :
    ∃ length, 0 < length ∧ Walk edge (fun v => ¬ deleted v) t length u := by
  classical
  by_cases middle : ∃ v, t < v ∧ v < u ∧ position v = c
  · obtain ⟨v, htv, hvu, hv⟩ := middle
    obtain ⟨left, hl, pl⟩ := cleanVisits edge deleted position c includeVisit safeCell t v ht hv htv
    obtain ⟨right, hr, pr⟩ := cleanVisits edge deleted position c includeVisit safeCell v u hv hu hvu
    exact ⟨left+right, by omega, concatenate pl pr⟩
  · have link : consecutive position c t u :=
      ⟨ht, hu, earlier, fun v htv hvu hv => middle ⟨v, htv, hvu, hv⟩⟩
    exact ⟨1, by decide, .extend (.stay t (safeCell t ht)) (includeVisit t u link) (safeCell u hu)⟩
termination_by u-t
decreasing_by all_goals omega

/-- A home at time H(v) touches A(v) and B(v). A transfer for v→w
visits A(v) and B(w) at a time strictly between the two homes. -/
structure Layout (V A B : Type) (edge : V → V → Prop) where
  positionA : Nat → A
  positionB : Nat → B
  home : V → Nat
  cellA : V → A
  cellB : V → B
  atHomeA : ∀ v, positionA (home v) = cellA v
  atHomeB : ∀ v, positionB (home v) = cellB v
  transfer : ∀ v w, edge v w → ∃ time, home v < time ∧ time < home w ∧
    positionA time = cellA v ∧ positionB time = cellB w

def goodHome (g : Layout V A B edge) (deleted : Nat → Prop) (v : V) : Prop :=
  clean deleted g.positionA (g.cellA v) ∧ clean deleted g.positionB (g.cellB v)

/-- On a single edge only the first tape cell of its source and the second
tape cell of its destination need be clean. -/
theorem liftEdge (g : Layout V A B edge) (deleted : Nat → Prop) {v w : V}
    (link : edge v w) (source : clean deleted g.positionA (g.cellA v))
    (target : clean deleted g.positionB (g.cellB w)) :
    ∃ length, 2 ≤ length ∧ Walk (tapeEdge g.positionA g.positionB)
      (fun i => ¬ deleted i) (g.home v) length (g.home w) := by
  obtain ⟨time, before, after, atA, atB⟩ := g.transfer v w link
  obtain ⟨left, hl, pl⟩ := cleanVisits (tapeEdge g.positionA g.positionB) deleted
    g.positionA (g.cellA v) (fun _ _ h => Or.inl ⟨_, h⟩)
    source (g.home v) time (g.atHomeA v) atA before
  obtain ⟨right, hr, pr⟩ := cleanVisits (tapeEdge g.positionA g.positionB) deleted
    g.positionB (g.cellB w) (fun _ _ h => Or.inr ⟨_, h⟩)
    target time (g.home w) atB (g.atHomeB w) after
  exact ⟨left+right, by omega, concatenate pl pr⟩

theorem liftPath (g : Layout V A B edge) (deleted : Nat → Prop)
    (path : Walk edge (goodHome g deleted) v n w) :
    ∃ length, 2*n ≤ length ∧ Walk (tapeEdge g.positionA g.positionB)
      (fun i => ¬ deleted i) (g.home v) length (g.home w) := by
  induction path with
  | stay hv =>
    exact ⟨0, by decide, .stay _ (hv.1 _ (g.atHomeA _))⟩
  | extend prior link target ih =>
    obtain ⟨left, hl, pl⟩ := ih
    obtain ⟨right, hr, pr⟩ := liftEdge g deleted link (endSafe prior).1 target.2
    exact ⟨left+right, by omega, concatenate pl pr⟩

/-- Every tape edge strictly increases time, so the lifted walk has no
repeated times. The endpoint gap bounds its edge count. -/
theorem timeGap (a : Nat → A) (b : Nat → B) {safe : Nat → Prop}
    (path : Walk (tapeEdge a b) safe t n u) : t+n ≤ u := by
  induction path with
  | stay => omega
  | extend prior link _ ih =>
    rcases link with ⟨_, visit⟩ | ⟨_, visit⟩ <;> have h := visit.2.2.1 <;> omega

/-- A failed event writes zero; a surviving event ORs its injection and
the two previously stored tape bits. The same result goes to both heads. -/
def gate (failed input a b : Bool) : Bool :=
  if failed then false else input || a || b

variable {A B : Type}

def tapesBefore [DecidableEq A] [DecidableEq B] (a : Nat → A) (b : Nat → B)
    (failed inject : Nat → Bool) : Nat → (A → Bool) × (B → Bool)
  | 0 => (fun _ => false, fun _ => false)
  | t+1 =>
    let mem := tapesBefore a b failed inject t
    let out := gate (failed t) (inject t) (mem.1 (a t)) (mem.2 (b t))
    (fun x => if a t = x then out else mem.1 x,
     fun y => if b t = y then out else mem.2 y)

def written [DecidableEq A] [DecidableEq B] (a : Nat → A) (b : Nat → B)
    (failed inject : Nat → Bool) (t : Nat) : Bool :=
  let mem := tapesBefore a b failed inject t
  gate (failed t) (inject t) (mem.1 (a t)) (mem.2 (b t))

/-- On either tape, the bit read at the next visit is precisely what the
earlier visit wrote. This uses the concrete rule that unvisited cells
retain their value. -/
theorem retainedUntil [DecidableEq Cell] (pos : Nat → Cell) (mem : Nat → Cell → Bool)
    (out : Nat → Bool)
    (update : ∀ t c, mem (t+1) c = if pos t = c then out t else mem t c)
    {c : Cell} {t u : Nat} (first : pos t = c) (earlier : t < u)
    (middle : ∀ j, t < j → j < u → pos j ≠ c) : mem u c = out t := by
  induction u with
  | zero => omega
  | succ n ih =>
    rw [update]
    by_cases last : n = t
    · simp [last, first]
    · have hn : t < n := by omega
      rw [if_neg (middle n hn (by omega))]
      exact ih hn (fun j hj hjn => middle j hj (by omega))

theorem alongMemoryEdge [DecidableEq A] [DecidableEq B] (a : Nat → A) (b : Nat → B)
    (failed inject : Nat → Bool) {t u : Nat} (link : tapeEdge a b t u)
    (live : failed u = false) (prior : written a b failed inject t = true) :
    written a b failed inject u = true := by
  rcases link with ⟨c, first, last, before, middle⟩ | ⟨c, first, last, before, middle⟩
  · have same := retainedUntil a (fun j => (tapesBefore a b failed inject j).1)
      (written a b failed inject) (fun _ _ => rfl) first before middle
    rw [prior] at same
    simp [written, gate, live, last, same]
  · have same := retainedUntil b (fun j => (tapesBefore a b failed inject j).2)
      (written a b failed inject) (fun _ _ => rfl) first before middle
    rw [prior] at same
    simp [written, gate, live, last, same]

/-- Propagation uses only consecutive same-cell edges. An unrelated
chronological successor does not have to receive the preceding bit. -/
theorem signalOnPath [DecidableEq A] [DecidableEq B] (a : Nat → A) (b : Nat → B)
    (failed inject : Nat → Bool) {t n u : Nat}
    (path : Walk (tapeEdge a b) (fun j => failed j = false) t n u)
    (source : inject t = true) : written a b failed inject u = true := by
  induction path with
  | stay live => simp [written, gate, live, source]
  | extend prior link live ih => exact alongMemoryEdge a b failed inject link live ih

/-- Even if there are failures, zero initialization and zero injections
leave both tapes zero at every time. -/
theorem zeroTapes [DecidableEq A] [DecidableEq B] (a : Nat → A) (b : Nat → B)
    (failed : Nat → Bool) (t : Nat) :
    (∀ x, (tapesBefore a b failed (fun _ => false) t).1 x = false) ∧
    (∀ y, (tapesBefore a b failed (fun _ => false) t).2 y = false) := by
  induction t with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ t ih =>
    obtain ⟨ha, hb⟩ := ih
    constructor <;> intro c <;> simp [tapesBefore, gate, ha, hb]

theorem zeroSignal [DecidableEq A] [DecidableEq B] (a : Nat → A) (b : Nat → B)
    (failed : Nat → Bool) (t : Nat) : written a b failed (fun _ => false) t = false := by
  obtain ⟨ha, hb⟩ := zeroTapes a b failed t
  simp [written, gate, ha, hb]

end TwoTapeGratePaths
