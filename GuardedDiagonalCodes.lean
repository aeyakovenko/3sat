import Std

namespace GuardedDiagonalCodes

/-- The suffix in this predicate is the particular accepting suffix selected
from the genuine diagonal run on the right-hand input.  The guard can depend
on the unequal file. No common rejecting guard is required. -/
theorem hybrid_forces_injection {X C S I : Type}
    (cpu : X → C) (guard : X → I → S)
    (tailOK : I → C → S → X → Prop) (possible : I → X → X → Prop)
    (transparent : ∀ y j, tailOK j (cpu y) (guard y j) y)
    (splice : ∀ x y j, tailOK j (cpu x) (guard x j) y → possible j x y)
    (kills : ∀ x y, x ≠ y → ∃ j, ¬ possible j x y)
    {x y : X} (sameCPU : cpu x = cpu y) (sameGuard : ∀ j, guard x j = guard y j) :
    x = y := by
  apply Classical.byContradiction
  intro distinct
  obtain ⟨j, killed⟩ := kills x y distinct
  apply killed
  apply splice
  rw [sameCPU, sameGuard j]
  exact transparent y j

/-- All vectors of checker states, with one entry for each checker. -/
def allVectors (K : Nat) : (G : Nat) → List (Fin G → Fin K)
  | 0 => [Fin.elim0]
  | g+1 => (List.finRange K).flatMap fun a =>
      (allVectors K g).map fun t => Fin.cases a t

private theorem all_fin {n : Nat} (i : Fin n) : i ∈ List.finRange n :=
  List.mem_ofFn.mpr ⟨i, rfl⟩

theorem mem_allVectors {G K : Nat} (v : Fin G → Fin K) : v ∈ allVectors K G := by
  induction G with
  | zero =>
    simp only [allVectors, List.mem_singleton]
    funext i
    exact Fin.elim0 i
  | succ g ih =>
    apply List.mem_flatMap.mpr
    refine ⟨v 0, all_fin _, List.mem_map.mpr ⟨fun i => v i.succ, ih _, ?_⟩⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem length_allVectors (K G : Nat) : (allVectors K G).length = K^G := by
  induction G with
  | zero => simp [allVectors]
  | succ g ih => simp [allVectors, List.length_flatMap, ih, Nat.pow_succ, Nat.mul_comm,
      List.map_const']

theorem nodup_allVectors (K G : Nat) : (allVectors K G).Nodup := by
  induction G with
  | zero => simp [allVectors]
  | succ g ih =>
    apply List.pairwise_flatMap.mpr
    constructor
    · intro a _
      apply List.pairwise_map.mpr
      apply ih.imp
      intro s t ne same
      apply ne
      funext i
      exact congrFun same i.succ
    · have nd : (List.finRange K).Nodup := by
        apply List.pairwise_iff_getElem.mpr
        intro i j hi hj hij eq
        exact (Nat.ne_of_lt hij) (by simpa using congrArg Fin.val eq)
      apply nd.imp
      intro a b ne u hu v hv same
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp hu
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hv
      exact ne (congrFun same 0)

private theorem nodup_subset_length {α : Type} (xs ys : List α)
    (hn : xs.Nodup) (sub : xs ⊆ ys) : xs.length ≤ ys.length := by
  classical
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, nd⟩ := List.nodup_cons.mp hn
    have h := sub List.mem_cons_self
    have smaller := ih (ys.erase x) nd (by
      intro y hy
      have ne : y ≠ x := by rintro rfl; exact fresh hy
      exact (List.mem_erase_of_ne ne).mpr (sub (List.mem_cons_of_mem _ hy)))
    have pos := List.length_pos_of_mem h
    rw [List.length_erase_of_mem h] at smaller
    simp only [List.length_cons]
    omega

/-- Counts arbitrary finite diagonal labels, including the controller factor. -/
theorem count_signatures {n H G K : Nat} (cpu : Fin n → Fin H)
    (guard : Fin n → Fin G → Fin K)
    (inj : ∀ x y, cpu x = cpu y → (∀ j, guard x j = guard y j) → x = y) :
    n ≤ H * K^G := by
  let signature := fun x => (cpu x, guard x)
  let palette := (List.finRange H).flatMap fun h =>
    (allVectors K G).map fun v => (h, v)
  have nd : (List.ofFn signature).Nodup := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij eq
    simp only [List.getElem_ofFn] at eq
    have equal := inj _ _ (congrArg Prod.fst eq) (congrFun (congrArg Prod.snd eq))
    exact (Nat.ne_of_lt hij) (congrArg Fin.val equal)
  have bound := nodup_subset_length (List.ofFn signature) palette nd (by
    intro s hs
    obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hs
    exact List.mem_flatMap.mpr ⟨cpu x, all_fin _, List.mem_map.mpr
      ⟨guard x, mem_allVectors _, rfl⟩⟩)
  simpa [palette, List.length_flatMap, length_allVectors, List.map_const'] using bound

/-- For an m-bit private half, there are exactly 2^m candidate diagonal labels. -/
theorem guarded_diagonal_capacity {m H G K : Nat}
    (cpu : Fin (2^m) → Fin H) (guard : Fin (2^m) → Fin G → Fin K)
    (tailOK : Fin G → Fin H → Fin K → Fin (2^m) → Prop)
    (possible : Fin G → Fin (2^m) → Fin (2^m) → Prop)
    (transparent : ∀ y j, tailOK j (cpu y) (guard y j) y)
    (splice : ∀ x y j, tailOK j (cpu x) (guard x j) y → possible j x y)
    (kills : ∀ x y, x ≠ y → ∃ j, ¬ possible j x y) :
    2^m ≤ H * K^G :=
  count_signatures cpu guard fun _ _ =>
    hybrid_forces_injection cpu guard tailOK possible transparent splice kills

/-- With a fixed controller, each guard stores its own coordinate and checks
that coordinate in the right half. These guard tests recognize precisely the
diagonal on the whole K^G-element vector alphabet enumerated above. -/
theorem coordinate_guards_exact {G K : Nat} (left right : Fin G → Fin K) :
    (∀ j, left j = right j) ↔ left = right :=
  ⟨fun h => funext h, fun h j => congrFun h j⟩

def hamming {G K : Nat} (u v : Fin G → Fin K) : Nat :=
  (List.finRange G).countP fun j => decide (u j ≠ v j)

/-- All guards in this count see the same false accepting chronology. The
splice assumption says exactly which guards must pass that chronology. -/
theorem distance_of_fixed_hybrid {X C : Type} {G K d : Nat}
    (cpu : X → C) (guard : X → Fin G → Fin K) (rejects : X → X → Fin G → Bool)
    (splice : ∀ x y, cpu x = cpu y → ∀ j, guard x j = guard y j → rejects x y j = false)
    (many : ∀ x y, x ≠ y → cpu x = cpu y → d ≤ (List.finRange G).countP (rejects x y))
    {x y : X} (different : x ≠ y) (same : cpu x = cpu y) :
    d ≤ hamming (guard x) (guard y) := by
  apply Nat.le_trans (many x y different same)
  apply List.countP_mono_left
  intro j _ hr
  apply decide_eq_true
  intro eq
  simp [splice _ _ same _ eq] at hr

/-- Conversely, coordinate-by-coordinate comparison rejects at exactly
the Hamming distance, for arbitrary codewords in any chosen code. -/
theorem coordinate_guard_rejections {G K : Nat} (u v : Fin G → Fin K) :
    (List.finRange G).countP (fun j => decide (u j ≠ v j)) = hamming u v := rfl

/-- Use a CPU tag and the same selected code inside each tag class.
Different tags have no accepting CPU splice.  When tags match, each guard
retains one symbol and rejects exactly a disagreement at its coordinate. -/
theorem realize_distance_code {H n G K d : Nat} (encode : Fin n → Fin G → Fin K)
    (distance : ∀ a b, a ≠ b → d ≤ hamming (encode a) (encode b)) :
    let passes := fun (x y : Fin H × Fin n) (j : Fin G) =>
      x.1 = y.1 ∧ encode x.2 j = encode y.2 j
    (∀ x j, passes x x j) ∧
    (∀ x y, x ≠ y → x.1 = y.1 →
      d ≤ (List.finRange G).countP (fun j => decide (¬ passes x y j))) := by
  dsimp only
  constructor
  · simp
  · intro x y different sameTag
    have distinct : x.2 ≠ y.2 := fun eq => different (Prod.ext sameTag eq)
    simpa [sameTag, hamming] using distance x.2 y.2 distinct

private theorem length_flatMap_le {α β : Type} (xs : List α) (f : α → List β) (A : Nat)
    (h : ∀ x, (f x).length ≤ A) : (xs.flatMap f).length ≤ xs.length * A := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := h x
    omega

/-- A can be the extremal size of a K-ary code of block length G and
minimum distance d.  CPU fibers may use different codes. -/
theorem distance_capacity {n H G K d A : Nat} (positive : 0 < d)
    (cpu : Fin n → Fin H) (guard : Fin n → Fin G → Fin K)
    (separates : ∀ x y, x ≠ y → cpu x = cpu y → d ≤ hamming (guard x) (guard y))
    (packing : ∀ code : List (Fin G → Fin K),
      code.Nodup → code.Pairwise (fun u v => d ≤ hamming u v) → code.length ≤ A) :
    n ≤ H * A := by
  classical
  let used := fun (h : Fin H) (v : Fin G → Fin K) => ∃ x, cpu x = h ∧ guard x = v
  let fiber := fun h => (allVectors K G).filter fun v => decide (used h v)
  have belongs (v : Fin G → Fin K) (h : Fin H) : v ∈ fiber h ↔ used h v := by
    simp [fiber, List.mem_filter, mem_allVectors]
  have bounded (h : Fin H) : (fiber h).length ≤ A := by
    have nd : (fiber h).Nodup := (nodup_allVectors K G).filter _
    apply packing _ nd
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj lt
    let vi := (fiber h)[i]
    let vj := (fiber h)[j]
    have distinct : vi ≠ vj := List.pairwise_iff_getElem.mp nd i j hi hj lt
    obtain ⟨x, hcx, hvx⟩ := (belongs vi h).mp (List.getElem_mem hi)
    obtain ⟨y, hcy, hvy⟩ := (belongs vj h).mp (List.getElem_mem hj)
    have xy : x ≠ y := by rintro rfl; exact distinct (hvx.symm.trans hvy)
    change d ≤ hamming vi vj
    rw [← hvx, ← hvy]
    exact separates x y xy (hcx.trans hcy.symm)
  let signature := fun x => (cpu x, guard x)
  let choices := fun h => (fiber h).map fun v => (h, v)
  have sigND : (List.ofFn signature).Nodup := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj lt eq
    simp only [List.getElem_ofFn] at eq
    have hcpu := congrArg Prod.fst eq
    have hguard := congrArg Prod.snd eq
    have ne : (⟨i, by simpa using hi⟩ : Fin n) ≠ ⟨j, by simpa using hj⟩ := by
      intro e
      exact (Nat.ne_of_lt lt) (congrArg Fin.val e)
    have hd := separates _ _ ne hcpu
    change guard _ = guard _ at hguard
    rw [hguard] at hd
    simp [hamming] at hd
    omega
  have hits := nodup_subset_length (List.ofFn signature) ((List.finRange H).flatMap choices)
    sigND (by
      intro s hs
      obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hs
      exact List.mem_flatMap.mpr ⟨cpu x, all_fin _, List.mem_map.mpr
        ⟨guard x, (belongs _ _).mpr ⟨x, rfl, rfl⟩, rfl⟩⟩)
  have cap := length_flatMap_le (List.finRange H) choices A
    (fun h => by simpa [choices] using bounded h)
  simpa using Nat.le_trans hits cap

namespace NegativeDiagonal

/-- The genuine positive suffix has origin (z,x), with z different from x.
After transplanting it to (x,x), a guard which kills *every* false accepting
suffix on that diagonal must distinguish x from z within their CPU fiber. -/
theorem singleton_of_global_protection {X C S I : Type}
    (cpu : X → C) (state : X → I → S)
    (tailOK : I → C → S → X → X → Prop) (fake : I → X → Prop)
    (positiveOK : ∀ z x, z ≠ x → ∀ j, tailOK j (cpu z) (state z j) z x)
    (splice : ∀ x z j, tailOK j (cpu x) (state x j) z x → fake j x)
    {x z : X} {j : I} (protects : ¬ fake j x) (sameCPU : cpu x = cpu z)
    (sameState : state x j = state z j) : x = z := by
  apply Classical.byContradiction
  intro different
  apply protects
  apply splice x z j
  rw [sameCPU, sameState]
  exact positiveOK z x (Ne.symm different) j

private theorem finrange_nodup (n : Nat) : (List.finRange n).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij eq
  exact (Nat.ne_of_lt hij) (by simpa using congrArg Fin.val eq)

/-- One state must be reserved for an unprotected label when there are
more labels than available states. This yields K-1, rather than K. -/
theorem singleton_count {M K : Nat} (large : K < M) (state : Fin M → Fin K)
    (kept : Fin M → Bool)
    (singleton : ∀ x, kept x = true → ∀ z, state x = state z → x = z) :
    (List.finRange M).countP kept ≤ K-1 := by
  let labels := (List.finRange M).filter kept
  have nd : labels.Nodup := (finrange_nodup M).filter _
  have eligible {x} (hx : x ∈ labels) : kept x = true := (List.mem_filter.mp hx).2
  have sigND : (labels.map state).Nodup := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj lt eq
    simp only [List.length_map] at hi hj
    simp only [List.getElem_map] at eq
    have z := singleton labels[i] (eligible (List.getElem_mem hi)) labels[j] eq
    exact List.pairwise_iff_getElem.mp nd i j hi hj lt z
  have bound := nodup_subset_length (labels.map state) (List.finRange K) sigND
    (fun _ _ => all_fin _)
  have short : labels.length < M := Nat.lt_of_le_of_lt (by simpa using bound) large
  have missing : ∃ a : Fin M, kept a = false := by
    apply Classical.byContradiction
    intro none
    have allKept : ∀ a : Fin M, kept a = true := fun a => by
      cases h : kept a with
      | false => exact False.elim (none ⟨a, h⟩)
      | true => rfl
    have full : (List.finRange M).countP kept = M := by
      rw [List.countP_eq_length.mpr (fun a _ => allKept a), List.length_finRange]
    rw [List.countP_eq_length_filter] at full
    change labels.length = M at full
    omega
  obtain ⟨a, ha⟩ := missing
  have fresh : state a ∉ labels.map state := by
    rintro h
    obtain ⟨x, hx, eq⟩ := List.mem_map.mp h
    have hk := eligible hx
    have xe := singleton x hk a eq
    simp [xe, ha] at hk
  have larger := nodup_subset_length (state a :: labels.map state) (List.finRange K)
    (List.nodup_cons.mpr ⟨fresh, sigND⟩) (fun _ _ => all_fin _)
  simp only [List.length_cons, List.length_map, List.length_finRange] at larger
  change (List.finRange M).countP kept ≤ K-1
  rw [List.countP_eq_length_filter]
  change labels.length ≤ K-1
  omega

private theorem sum_counts_at (xs : List α) (p : α → Bool) :
    (xs.map (fun x => if p x then 1 else 0)).sum = xs.countP p := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.countP_cons, ih, Nat.add_comm]

private theorem sum_add (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem swap_counts {X I : Type} (xs : List X) (js : List I) (p : X → I → Bool) :
    (xs.map (fun x => js.countP (p x))).sum =
    (js.map (fun j => xs.countP (fun x => p x j))).sum := by
  induction xs with
  | nil => simp [List.map_const']
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    rw [sum_add, sum_counts_at, ih, Nat.add_comm]

private theorem sum_mono (xs : List α) (f g : α → Nat) (h : ∀ x, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => exact Nat.add_le_add (h x) ih

/-- Sharp upper bound per CPU boundary fiber. Covers are chosen separately
for each negative input but each selected coordinate must globally protect it. -/
theorem global_guard_fiber_capacity {M G K d : Nat} (positive : 0 < d)
    (state : Fin M → Fin G → Fin K) (protects : Fin M → Fin G → Bool)
    (singleton : ∀ x j, protects x j = true → ∀ z, state x j = state z j → x = z)
    (coverage : ∀ x, d ≤ (List.finRange G).countP (protects x)) :
    M ≤ max K (G * (K-1) / d) := by
  by_cases small : M ≤ K
  · exact Nat.le_trans small (Nat.le_max_left ..)
  · have large : K < M := by omega
    have upper (j : Fin G) : (List.finRange M).countP (fun x => protects x j) ≤ K-1 :=
      singleton_count large (fun x => state x j) _ (fun x => singleton x j)
    have lo := sum_mono (List.finRange M) (fun _ => d)
      (fun x => (List.finRange G).countP (protects x)) coverage
    have hi := sum_mono (List.finRange G)
      (fun j => (List.finRange M).countP (fun x => protects x j)) (fun _ => K-1) upper
    rw [swap_counts] at lo
    have prod : M*d ≤ G*(K-1) := by
      simpa [List.map_const'] using Nat.le_trans lo hi
    exact Nat.le_trans ((Nat.le_div_iff_mul_le positive).2 prod) (Nat.le_max_right ..)

/-- Consecutive tickets of one label have distinct residues when their
number is no more than the number of checkers. -/
private theorem add_mod_injective {u v G : Nat} (off : Nat) (hu : u < G) (hv : v < G)
    (same : (off+u)%G = (off+v)%G) : u = v := by
  have l := @Nat.mod_add_mod_eq off u G
  have r := @Nat.mod_add_mod_eq off v G
  rw [Nat.mod_eq_of_lt hu] at l
  rw [Nat.mod_eq_of_lt hv] at r
  split at l <;> split at r <;> omega

/-- Allocate the Md tickets to columns cyclically. Each nonempty ticket
provides a private nonzero symbol; zero means the column did not receive
that label. This realizes the second branch of the capacity formula. -/
theorem round_robin_realization {M G K d : Nat} (dp : 0 < d) (fit : d ≤ G)
    (kp : 0 < K) (room : M*d ≤ G*(K-1)) :
    ∃ (state : Fin M → Fin G → Fin K) (protects : Fin M → Fin G → Bool),
      (∀ x j, protects x j = true → ∀ z, state x j = state z j → x = z) ∧
      (∀ x, d ≤ (List.finRange G).countP (protects x)) := by
  classical
  have gp : 0 < G := by omega
  let ticket := fun (x : Fin M) (t : Fin d) => d*x.val+t.val
  let col := fun x t => (⟨ticket x t % G, Nat.mod_lt _ gp⟩ : Fin G)
  have small (x : Fin M) (t : Fin d) : ticket x t < G*(K-1) := by
    have step : d*(x.val+1) ≤ d*M := Nat.mul_le_mul_left _ x.isLt
    rw [Nat.mul_succ] at step
    have bound := Nat.le_trans step (by simpa [Nat.mul_comm d M] using room)
    dsimp [ticket]
    have := t.isLt
    omega
  let row := fun (x : Fin M) (t : Fin d) =>
    (⟨ticket x t / G, (Nat.div_lt_iff_lt_mul gp).2 (by
      simpa [Nat.mul_comm G] using small x t)⟩ : Fin (K-1))
  let named := fun x j => ∃ t : Fin d, col x t = j
  let state := fun x j => if h : named x j then
      (⟨(row x (Classical.choose h)).val + 1, by have := (row x (Classical.choose h)).isLt; omega⟩ : Fin K)
    else ⟨0, kp⟩
  refine ⟨state, fun x j => decide (named x j), ?_, ?_⟩
  · intro x j hx z same
    have hx' : named x j := of_decide_eq_true hx
    by_cases hz : named z j
    · let s := Classical.choose hx'
      let t := Classical.choose hz
      have he : col x s = col z t := (Classical.choose_spec hx').trans (Classical.choose_spec hz).symm
      have residues : ticket x s % G = ticket z t % G := congrArg Fin.val he
      have rows : ticket x s / G = ticket z t / G := by
        simpa [state, hx', hz, row, s, t] using congrArg Fin.val same
      have tickets : ticket x s = ticket z t := by
        calc ticket x s = ticket x s % G + G*(ticket x s/G) := (Nat.mod_add_div _ _).symm
             _ = ticket z t % G + G*(ticket z t/G) := by rw [residues, rows]
             _ = ticket z t := Nat.mod_add_div _ _
      apply Fin.ext
      simpa [ticket, Nat.mul_add_div dp, Nat.div_eq_of_lt s.isLt, Nat.div_eq_of_lt t.isLt]
        using congrArg (fun n => n/d) tickets
    · have := congrArg Fin.val same
      simp [state, hx', hz] at this
  · intro x
    have unique (s t : Fin d) (eq : col x s = col x t) : s = t := by
      apply Fin.ext
      exact add_mod_injective (d*x.val) (Nat.lt_of_lt_of_le s.isLt fit)
        (Nat.lt_of_lt_of_le t.isLt fit) (congrArg Fin.val eq)
    have nd : (List.ofFn (col x)).Nodup := by
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj lt eq
      simp only [List.getElem_ofFn] at eq
      exact (Nat.ne_of_lt lt) (congrArg Fin.val (unique _ _ eq))
    have cover := nodup_subset_length (List.ofFn (col x))
      ((List.finRange G).filter (fun j => decide (named x j))) nd (by
        intro j hj
        obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hj
        exact List.mem_filter.mpr ⟨all_fin _, decide_eq_true (show named x (col x t) from ⟨t, rfl⟩)⟩)
    simpa [List.countP_eq_length_filter] using cover

/-- The alternate branch uses distinct symbols for every label at every
guard. Together with the upper bound this is an iff at all positive d≤G. -/
theorem global_guard_capacity_iff {M G K d : Nat} (dp : 0 < d) (fit : d ≤ G) (kp : 0 < K) :
    (∃ (state : Fin M → Fin G → Fin K) (protects : Fin M → Fin G → Bool),
      (∀ x j, protects x j = true → ∀ z, state x j = state z j → x = z) ∧
      (∀ x, d ≤ (List.finRange G).countP (protects x))) ↔
    M ≤ max K (G*(K-1)/d) := by
  constructor
  · rintro ⟨state, protects, single, cover⟩
    exact global_guard_fiber_capacity dp state protects single cover
  · intro cap
    by_cases small : M ≤ K
    · refine ⟨fun x _ => ⟨x.val, Nat.lt_of_lt_of_le x.isLt small⟩, fun _ _ => true, ?_, ?_⟩
      · intro x _ _ z eq
        exact Fin.ext (congrArg (fun s : Fin K => s.val) eq)
      · intro _
        simpa using fit
    · have h : M ≤ G*(K-1)/d := by omega
      exact round_robin_realization dp fit kp ((Nat.le_div_iff_mul_le dp).1 h)

end NegativeDiagonal

end GuardedDiagonalCodes
