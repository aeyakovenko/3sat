import Std

namespace MatrixColumnCertificates

variable {Data Column Value Summary Answer Address Word : Type}

def AgreesOn (col : Data → Column → Value) (U : Column → Prop) (x y : Data) : Prop :=
  ∀ c, U c → col x c = col y c

/-- A certificate is local to the chosen input and the given public summary. -/
def CertifiesAt (col : Data → Column → Value) (Z : Data → Summary)
    (answer : Data → Answer) (x : Data) (U : Column → Prop) : Prop :=
  ∀ y, Z x = Z y → AgreesOn col U x y → answer x = answer y

theorem outside_erasure {col : Data → Column → Value} {Z : Data → Summary}
    {answer : Data → Answer} {x : Data} {U K : Column → Prop}
    (cert : CertifiesAt col Z answer x U) (disjoint : ∀ c, U c → ¬ K c) :
    CertifiesAt col Z answer x (fun c => ¬ K c) :=
  fun y same visible => cert y same (fun c member => visible c (disjoint c member))

/-- A uniform factorization is available when the local certificate may change
with the input but every such certificate avoids the same erasure. The output
on observations outside the image can be left unspecified. -/
theorem decode_visible {col : Data → Column → Value} {Z : Data → Summary}
    {answer : Data → Answer} {K : Column → Prop} (U : Data → Column → Prop)
    (cert : ∀ x, CertifiesAt col Z answer x (U x))
    (disjoint : ∀ x c, U x c → ¬ K c) :
    ∃ decode : Summary → ({c : Column // ¬ K c} → Value) → Option Answer,
      ∀ x, decode (Z x) (fun c => col x c.val) = some (answer x) := by
  classical
  let visible (x : Data) := fun c : {c : Column // ¬ K c} => col x c.val
  let compatible (s : Summary) (v : {c : Column // ¬ K c} → Value) (x : Data) :=
    Z x = s ∧ visible x = v
  let decode (s : Summary) (v : {c : Column // ¬ K c} → Value) :=
    if h : ∃ x, compatible s v x then some (answer (Classical.choose h)) else none
  refine ⟨decode, fun x => ?_⟩
  have h : ∃ y, compatible (Z x) (visible x) y := ⟨x, rfl, rfl⟩
  change decode (Z x) (visible x) = _
  unfold decode
  rw [dif_pos h]
  have info := Classical.choose_spec h
  apply congrArg some
  apply outside_erasure (cert (Classical.choose h)) (disjoint (Classical.choose h)) x info.1
  intro c hc
  exact congrFun info.2 ⟨c, hc⟩

/-- Between requests for inherited words the deterministic continuation may
perform arbitrary local work. Each branch selects its next request from the
reply actually obtained. -/
inductive Suffix (Address Word Answer : Type) where
  | done : Answer → Suffix Address Word Answer
  | read : Address → (Word → Suffix Address Word Answer) → Suffix Address Word Answer

def run (P : Suffix Address Word Answer) (reply : Address → Word) :
    List (Address × Word) × Answer :=
  match P with
  | .done a => ([], a)
  | .read p next =>
    let w := reply p
    let rest := run (next w) reply
    ((p, w) :: rest.1, rest.2)

theorem replay (P : Suffix Address Word Answer) (left right : Address → Word)
    (agree : ∀ p w, (p, w) ∈ (run P left).1 → left p = right p) :
    run P left = run P right := by
  induction P with
  | done a => rfl
  | read p next ih =>
    have first : left p = right p := agree p (left p) (by simp [run])
    have tail := ih (left p) (fun q w h => agree q w (by simp [run, h]))
    simp only [run]
    rw [← first, tail]

/-- Supports may depend on the baseline input and address. Only supports
along the actual baseline path enter the union. The control tree can be any
function of the public summary. -/
theorem visited_support_certificate (col : Data → Column → Value) (Z : Data → Summary)
    (P : Summary → Suffix Address Word Answer) (reply : Data → Address → Word)
    (support : Data → Address → Column → Prop)
    (locality : ∀ x p, CertifiesAt col Z (fun y => reply y p) x (support x p))
    (x : Data) :
    CertifiesAt col Z (fun y => (run (P (Z y)) (reply y)).2) x
      (fun c => ∃ p w, (p, w) ∈ (run (P (Z x)) (reply x)).1 ∧ support x p c) := by
  intro y same pins
  have path := replay (P (Z x)) (reply x) (reply y) (by
    intro p w used
    exact locality x p y same (fun c hc => pins c ⟨p, w, used, hc⟩))
  change (run (P (Z x)) (reply x)).2 = (run (P (Z y)) (reply y)).2
  rw [← same]
  exact congrArg Prod.snd path

section RankBound

def bitStrings : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (bitStrings n).map (false :: ·) ++ (bitStrings n).map (true :: ·)

theorem bitStrings_length (n : Nat) : (bitStrings n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bitStrings, ih, Nat.pow_succ, Nat.mul_two]

private theorem atMostOne {α : Type} (xs : List α) (p : α → Bool) (hd : xs.Nodup)
    (unique : ∀ x ∈ xs, ∀ y ∈ xs, p x = true → p y = true → x = y) :
    (xs.filter p).length ≤ 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, nd⟩ := List.nodup_cons.mp hd
    cases hx : p x with
    | false =>
      simpa [hx] using ih nd (fun a ha b hb => unique a (by simp [ha]) b (by simp [hb]))
    | true =>
      have empty : xs.filter p = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro y h
        obtain ⟨hy, yes⟩ := List.mem_filter.mp h
        have eq := unique x (by simp) y (by simp [hy]) hx yes
        exact fresh (eq ▸ hy)
      simp [hx, empty]

/-- With independent pivot columns the pivot contribution is injective.
For each fixed string of free coordinates, XOR cancellation leaves at most
one choice of the pivot coordinates in the target fiber. -/
theorem rank_fiber_count {Pivot Index : Type} (n : Nat)
    (pivots : List Pivot) (distinct : pivots.Nodup)
    (pivotValue : Pivot → Index → Bool) (freeValue : List Bool → Index → Bool)
    (injective : ∀ p q, pivotValue p = pivotValue q → p = q)
    (target : Index → Bool) (accept : List Bool → Pivot → Bool)
    (spec : ∀ f p, accept f p = true ↔
      ∀ i, (pivotValue p i ^^ freeValue f i) = target i) :
    ((bitStrings n).map (fun f => (pivots.filter (accept f)).length)).sum ≤ 2 ^ n := by
  have each (f : List Bool) : (pivots.filter (accept f)).length ≤ 1 := by
    apply atMostOne pivots (accept f) distinct
    intro p _ q _ hp hq
    apply injective
    funext i
    have eq := ((spec f p).mp hp i).trans ((spec f q).mp hq i).symm
    cases h : freeValue f i <;> simpa [h] using eq
  have bound (xs : List (List Bool)) :
      (xs.map (fun f => (pivots.filter (accept f)).length)).sum ≤ xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := each x
      omega
  simpa [bitStrings_length] using bound (bitStrings n)

end RankBound

end MatrixColumnCertificates
