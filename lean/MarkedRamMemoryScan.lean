import Std

namespace MarkedRamMemoryScan

/-- The two components of a location are the bank and the address within it. -/
abbrev Cell := Nat × Nat

structure Event where
  cell : Cell
  time : Nat
  write : Bool
  value : Nat
deriving DecidableEq, Repr

/-- The mark bit on a key is one iff that key was inserted by an actual event. -/
def PositiveEnumeration (actual guesses : List Nat) : Prop :=
  guesses.length = actual.length ∧ guesses.Pairwise (· < ·) ∧ guesses ⊆ actual

private theorem perm_of_full_subset {α : Type} [DecidableEq α] (xs ys : List α)
    (hn : xs.Nodup) (hsub : xs ⊆ ys) (hlen : xs.length = ys.length) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    have h : ys = [] := List.eq_nil_of_length_eq_zero hlen.symm
    simp [h]
  | cons a xs ih =>
    obtain ⟨ha, hn'⟩ := List.nodup_cons.mp hn
    have hmem := hsub List.mem_cons_self
    have tail : xs ⊆ ys.erase a := by
      intro b hb
      exact (List.mem_erase_of_ne (fun e : b = a => ha (e ▸ hb))).mpr
        (hsub (List.mem_cons_of_mem _ hb))
    have len : xs.length = (ys.erase a).length := by
      rw [List.length_erase_of_mem hmem]
      simp at hlen
      omega
    exact ((ih _ hn' tail len).cons _).trans (List.perm_cons_erase hmem).symm

theorem enumeration_perm {actual guesses : List Nat} (hv : PositiveEnumeration actual guesses) :
    guesses.Perm actual :=
  perm_of_full_subset guesses actual (hv.2.1.imp Nat.ne_of_lt) hv.2.2 hv.1

def sortedKeys (keys : List Nat) := keys.mergeSort (fun a b => decide (a ≤ b))

theorem sortedKeys_positive {keys : List Nat} (hn : keys.Nodup) :
    PositiveEnumeration keys (sortedKeys keys) := by
  let leq := fun a b : Nat => decide (a ≤ b)
  have hp := List.mergeSort_perm keys leq
  have ht (a b c : Nat) : leq a b → leq b c → leq a c := by
    simp only [leq, decide_eq_true_eq]
    omega
  have hall (a b : Nat) : leq a b || leq b a := by
    simp only [leq, Bool.or_eq_true, decide_eq_true_eq]
    omega
  have hs : (sortedKeys keys).Pairwise (· ≤ ·) := by
    simpa [sortedKeys, leq] using List.sorted_mergeSort ht hall keys
  exact ⟨hp.length_eq, hs.imp₂ (fun _ _ hab hne => Nat.lt_of_le_of_ne hab hne)
    (hp.symm.nodup hn), hp.subset⟩

theorem positive_iff_canonical {keys guesses : List Nat} (hn : keys.Nodup) :
    PositiveEnumeration keys guesses ↔ guesses = sortedKeys keys := by
  constructor
  · intro h
    have hcanon := sortedKeys_positive hn
    exact List.Perm.eq_of_sorted (fun _ _ _ _ h₁ h₂ => False.elim (Nat.lt_asymm h₁ h₂))
      h.2.1 hcanon.2.1 ((enumeration_perm h).trans (enumeration_perm hcanon).symm)
  · rintro rfl
    exact sortedKeys_positive hn

/-- A successful read preserves the old value, so both kinds of event leave
the cell containing the recorded payload. -/
def rowOK (prior : Nat) (e : Event) : Prop := e.write = true ∨ e.value = prior

def update (m : Cell → Nat) (e : Event) : Cell → Nat :=
  fun c => if c = e.cell then e.value else m c

def correct (m : Cell → Nat) : List Event → Prop
  | [] => True
  | e::es => rowOK (m e.cell) e ∧ correct (update m e) es

def oneCell (prior : Nat) : List Event → Prop
  | [] => True
  | e::es => rowOK prior e ∧ oneCell e.value es

def stream (c : Cell) (es : List Event) := es.filter (fun e => decide (e.cell = c))

theorem correct_iff_cell_checks {es : List Event} {m : Cell → Nat} :
    correct m es ↔ ∀ c, oneCell (m c) (stream c es) := by
  induction es generalizing m with
  | nil => simp [correct, stream, oneCell]
  | cons e es ih =>
    rw [correct, ih]
    constructor
    · rintro ⟨head,tail⟩ c
      by_cases same : e.cell = c
      · subst c
        simpa [stream, oneCell, update] using And.intro head (tail e.cell)
      · simpa [stream, same, update, Ne.symm same] using tail c
    · intro h
      constructor
      · have head : rowOK (m e.cell) e ∧ oneCell e.value (stream e.cell es) := by
          simpa [stream, oneCell] using h e.cell
        exact head.1
      · intro c
        by_cases same : e.cell = c
        · subst c
          have h' : rowOK (m e.cell) e ∧ oneCell e.value (stream e.cell es) := by
            simpa [stream, oneCell] using h e.cell
          simpa [update] using h'.2
        · simpa [stream, same, update, Ne.symm same] using h c

def timeOrder (a b : Event) := a.time < b.time

def perCellOrdered (es : List Event) : Prop := ∀ c, (stream c es).Pairwise timeOrder

theorem streams_equal {base sorted : List Event}
    (hp : sorted.Perm base) (hc : base.Pairwise timeOrder) (hs : perCellOrdered sorted) :
    ∀ c, stream c sorted = stream c base := by
  intro c
  apply List.Perm.eq_of_sorted _ (hs c) (hc.filter _) (hp.filter _)
  intro a ha b hb h₁ h₂
  exact False.elim (Nat.lt_asymm h₁ h₂)

theorem chronological_iff_sorted_check {base sorted : List Event}
    (hp : sorted.Perm base) (hc : base.Pairwise timeOrder) (hs : perCellOrdered sorted)
    (m : Cell → Nat) :
    correct m base ↔ ∀ c, oneCell (m c) (stream c sorted) := by
  rw [correct_iff_cell_checks]
  exact forall_congr' (fun c => by rw [streams_equal hp hc hs c])

/-- Unpack a positive-key certificate. The encoding is only required to
round-trip on actual events, so malformed off-support keys need no semantics. -/
theorem decoded_perm {enc : Event → Nat} {dec : Nat → Event} {base : List Event}
    (roundTrip : ∀ e ∈ base, dec (enc e) = e)
    {guesses : List Nat} (h : PositiveEnumeration (base.map enc) guesses) :
    (guesses.map dec).Perm base := by
  have hp := (enumeration_perm h).map dec
  have hr : (base.map enc).map dec = base := by
    rw [List.map_map]
    exact List.map_congr_left (fun e he => roundTrip e he) |>.trans (List.map_id _)
  exact hr ▸ hp

/-- Radices are capacities, not bit counts. Operation is the single bit
between the time and value fields. The bank may be any natural number. -/
def digit (r major minor : Nat) := r*major + minor

def packed (A T V : Nat) (e : Event) : Nat :=
  digit V (digit 2 (digit T (digit A e.cell.1 e.cell.2) e.time) e.write.toNat) e.value

def unpacked (A T V k : Nat) : Event :=
  let upper := (k/V)/2
  let c := upper/T
  ⟨(c/A, c%A), upper%T, decide ((k/V)%2 = 1), k%V⟩

def bounded (A T V : Nat) (e : Event) : Prop :=
  e.cell.2 < A ∧ e.time < T ∧ e.value < V

private theorem dig_div {r x v : Nat} (h : v < r) : digit r x v / r = x := by
  have pos : 0 < r := by omega
  simp [digit, Nat.mul_add_div pos, Nat.div_eq_of_lt h]

private theorem dig_mod {r x v : Nat} (h : v < r) : digit r x v % r = v := by
  simp [digit, Nat.mul_add_mod, Nat.mod_eq_of_lt h]

theorem round_trip {A T V : Nat} {e : Event} (h : bounded A T V e) :
    unpacked A T V (packed A T V e) = e := by
  obtain ⟨ha, ht, hv⟩ := h
  have hop : e.write.toNat < 2 := by cases e.write <;> decide
  cases e with
  | mk c t wr v =>
    cases c
    cases wr <;> simp_all [packed, unpacked, dig_div, dig_mod]

private theorem monotone_digit {r i j u v : Nat} (h : i < j) (hu : u < r) :
    digit r i u < digit r j v := by
  have le := Nat.mul_le_mul_left r (Nat.succ_le_of_lt h)
  rw [Nat.mul_succ] at le
  simp only [digit]
  omega

theorem time_increases_key {A T V : Nat} {e f : Event}
    (h : bounded A T V e) (hc : e.cell = f.cell) (ht : e.time < f.time) :
    packed A T V e < packed A T V f := by
  apply monotone_digit _ h.2.2
  apply monotone_digit _ (show e.write.toNat < 2 by cases e.write <;> decide)
  simp only [digit, hc, Nat.add_lt_add_iff_left, ht]

theorem actual_keys_distinct {A T V : Nat} {es : List Event}
    (h : ∀ e ∈ es, bounded A T V e) (ht : es.Pairwise timeOrder) :
    (es.map (packed A T V)).Nodup := by
  apply List.pairwise_map.mpr
  apply ht.imp_of_mem
  intro a b ha hb t eq
  have same : a = b := by
    simpa only [round_trip (h a ha), round_trip (h b hb)] using congrArg (unpacked A T V) eq
  exact (Nat.ne_of_lt t) (congrArg Event.time same)

/-- Once the positive probes pass, the word fields themselves enforce the correct
chronological order within each cell. No second history or coverage bit is trusted. -/
theorem packed_memory_check {A T V : Nat} {es : List Event} {g : List Nat}
    (hb : ∀ e ∈ es, bounded A T V e) (ht : es.Pairwise timeOrder)
    (hg : PositiveEnumeration (es.map (packed A T V)) g) (init : Cell → Nat) :
    correct init es ↔ ∀ c, oneCell (init c) (stream c (g.map (unpacked A T V))) := by
  let dec := unpacked A T V
  let enc := packed A T V
  let ys := g.map dec
  have hp : ys.Perm es := decoded_perm (fun e he => round_trip (hb e he)) hg
  have distinct : ys.Pairwise (fun a b => a.time ≠ b.time) :=
    (hp.pairwise_iff (fun h => Ne.symm h)).mpr (ht.imp Nat.ne_of_lt)
  have reenc : ∀ k ∈ g, enc (dec k) = k := by
    intro k hk
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp (hg.2.2 hk)
    exact congrArg enc (round_trip (hb e he))
  have ho : ys.Pairwise (fun a b => enc a < enc b) := by
    apply List.pairwise_map.mpr
    exact hg.2.1.imp_of_mem (fun {a b} ha hb h => by simpa only [reenc a ha, reenc b hb] using h)
  apply chronological_iff_sorted_check hp ht _ init
  intro c
  have both : (stream c ys).Pairwise (fun a b => enc a < enc b ∧ a.time ≠ b.time) :=
    List.Pairwise.imp₂ (fun _ _ h₁ h₂ => And.intro h₁ h₂) (ho.filter _) (distinct.filter _)
  apply both.imp_of_mem
  intro a b ha hbm hh
  obtain ⟨_, ac⟩ := List.mem_filter.mp ha
  obtain ⟨bmem, bc⟩ := List.mem_filter.mp hbm
  have hcell : b.cell = a.cell := (of_decide_eq_true bc).trans (of_decide_eq_true ac).symm
  have hnot : ¬ b.time < a.time := fun lt =>
    Nat.lt_asymm hh.1 (time_increases_key (hb b (hp.subset bmem)) hcell lt)
  exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt hnot) hh.2

/-- The executable scan remembers only the preceding cell and its payload. -/
def remembered (init : Cell → Nat) (p : Option Event) (c : Cell) : Nat :=
  match p with
  | none => init c
  | some e => if c = e.cell then e.value else init c

def adjacent (init : Cell → Nat) (p : Option Event) : List Event → Prop
  | [] => True
  | e::es => rowOK (remembered init p e.cell) e ∧ adjacent init (some e) es

def noReturn (p : Option Event) : List Event → Prop
  | [] => True
  | e::es => (∀ prior, p = some prior → e.cell ≠ prior.cell →
      ∀ f ∈ es, f.cell ≠ prior.cell) ∧ noReturn (some e) es

theorem adjacent_iff_correct (es : List Event) (init m : Cell → Nat) (prev : Option Event)
    (grouped : noReturn prev es)
    (agreement : ∀ e ∈ es, m e.cell = remembered init prev e.cell) :
    adjacent init prev es ↔ correct m es := by
  induction es generalizing prev m with
  | nil => rfl
  | cons e es ih =>
    rw [adjacent, correct, agreement e List.mem_cons_self]
    apply and_congr_right
    intro _
    apply ih _ _ grouped.2
    intro f hf
    by_cases same : f.cell = e.cell
    · simp [update, remembered, same]
    · rw [update, if_neg same, agreement f (List.mem_cons_of_mem _ hf)]
      cases prev with
      | none => simp [remembered, same]
      | some p =>
        have extra : f.cell ≠ p.cell := by
          by_cases h : e.cell = p.cell
          · simpa only [← h] using same
          · exact grouped.1 p rfl h f hf
        simp [remembered, same, extra]

def rankPart (T V k : Nat) := (k/V/2)/T

private theorem rankPart_mono {T V a b : Nat} (h : a ≤ b) :
    rankPart T V a ≤ rankPart T V b :=
  by
    have mono {x y r : Nat} (hxy : x ≤ y) : x/r ≤ y/r := by
      cases r with
      | zero => simp
      | succ r =>
        have hd := Nat.div_le_iff_le_mul (x := y) (y := y/(r+1)) (Nat.succ_pos r)
        exact (Nat.div_le_iff_le_mul (Nat.succ_pos r)).mpr
          (Nat.le_trans hxy (hd.mp (Nat.le_refl _)))
    exact mono (mono (mono h))

private theorem between_cells (A T V p q k : Nat) (h₁ : p < q) (h₂ : q < k)
    (same : (unpacked A T V p).cell = (unpacked A T V k).cell) :
    (unpacked A T V q).cell = (unpacked A T V p).cell := by
  let rp := rankPart T V p
  let rk := rankPart T V k
  have d : rp/A = rk/A := congrArg Prod.fst same
  have m : rp%A = rk%A := congrArg Prod.snd same
  have eq : rp = rk := by
    calc rp = rp%A + A*(rp/A) := (Nat.mod_add_div _ _).symm
         _ = rk%A + A*(rk/A) := by rw [d,m]
         _ = rk := Nat.mod_add_div _ _
  have le₁ := rankPart_mono (T := T) (V := V) (Nat.le_of_lt h₁)
  have le₂ := rankPart_mono (T := T) (V := V) (Nat.le_of_lt h₂)
  have middle : rankPart T V q = rp := Nat.le_antisymm (by change rankPart T V q ≤ rk at le₂; simpa only [eq] using le₂) le₁
  change (rankPart T V q / A, rankPart T V q % A) = (rp/A,rp%A)
  rw [middle]

private theorem ordered_noReturn (A T V : Nat) (gs : List Nat) (prev : Option Nat)
    (ord : (prev.toList++gs).Pairwise (· < ·)) :
    noReturn (prev.map (unpacked A T V)) (gs.map (unpacked A T V)) := by
  induction gs generalizing prev with
  | nil => trivial
  | cons q qs ih =>
    simp only [List.map_cons, noReturn]
    constructor
    · intro prior hprev hchange f hf
      cases prev with
      | none => simp at hprev
      | some p =>
        simp at hprev
        subst prior
        obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hf
        have ord' : (p::q::qs).Pairwise (· < ·) := by simpa using ord
        obtain ⟨above,rest⟩ := List.pairwise_cons.mp ord'
        have hpq := above q List.mem_cons_self
        have hqk := (List.pairwise_cons.mp rest).1 k hk
        exact fun same => hchange (between_cells A T V p q k hpq hqk same.symm)
    · apply ih (some q)
      cases prev with
      | none => simpa using ord
      | some p =>
        have ord' : (p::q::qs).Pairwise (· < ·) := by simpa using ord
        simpa using (List.pairwise_cons.mp ord').2

theorem verifier_correct {A T V : Nat} {es : List Event} {g : List Nat}
    (hb : ∀ e ∈ es, bounded A T V e) (ht : es.Pairwise timeOrder)
    (init : Cell → Nat) :
    (PositiveEnumeration (es.map (packed A T V)) g ∧
      adjacent init none (g.map (unpacked A T V))) ↔
    g = sortedKeys (es.map (packed A T V)) ∧ correct init es := by
  have unique := positive_iff_canonical (guesses := g) (actual_keys_distinct hb ht)
  have step (hg : PositiveEnumeration (es.map (packed A T V)) g) :
      adjacent init none (g.map (unpacked A T V)) ↔ correct init es := by
    have grouped := ordered_noReturn A T V g none (by simpa using hg.2.1)
    exact (adjacent_iff_correct _ init init none grouped (fun _ _ => rfl)).trans
      (correct_iff_cell_checks.trans (packed_memory_check hb ht hg init).symm)
  exact ⟨fun ⟨hg,h⟩ => ⟨unique.mp hg, (step hg).mp h⟩,
    fun ⟨hg,h⟩ => ⟨unique.mpr hg, (step (unique.mpr hg)).mpr h⟩⟩

end MarkedRamMemoryScan
