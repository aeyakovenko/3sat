import Std

/-! Affine coordinate functions are represented on a parametrizing binary
vector space. Its zero and addition are the only structure the proofs need. -/

namespace CarryFlatAddition

def Affine (o : X) (plus : X → X → X) (f : X → Bool) : Prop :=
  ∀ x y, f (plus x y) = (f x ^^ f y ^^ f o)

def Fixed (o : X) (f : X → Bool) : Prop := ∀ x, f x = f o

def bxor (f g : X → Bool) (v : X) := f v ^^ g v
def band (f g : X → Bool) (v : X) := f v && g v

private theorem xor_rule (a b c d e f : Bool) :
    ((a ^^ b ^^ c) ^^ (d ^^ e ^^ f)) = ((a ^^ d) ^^ (b ^^ e) ^^ (c ^^ f)) := by decide +revert

theorem affine_xor {o : X} {plus : X → X → X} {f g : X → Bool}
    (hf : Affine o plus f) (hg : Affine o plus g) : Affine o plus (bxor f g) := by
  intro x y
  change (f (plus x y) ^^ g (plus x y)) = _
  rw [hf x y,hg x y]
  exact xor_rule _ _ _ _ _ _

private theorem polar (a b c d e f : Bool)
    (p : ((a ^^ b ^^ c) && (d ^^ e ^^ f)) = ((a && d) ^^ (b && e) ^^ (c && f))) :
    ((a ^^ c) && (e ^^ f)) = ((b ^^ c) && (d ^^ f)) := by decide +revert

private theorem rank_one (a b c d e f : Bool) (h : ((a ^^ c) && (e ^^ f)) = ((b ^^ c) && (d ^^ f)))
    (ha : a ≠ c) : (d = f → e = f) ∧ (d ≠ f → (b ^^ e) = (c ^^ f)) := by decide +revert

private theorem sufficient_bits (a b c d e f : Bool)
    (h : (a = c ∧ b = c) ∨ (d = f ∧ e = f) ∨ ((a ^^ d) = (c ^^ f) ∧ (b ^^ e) = (c ^^ f))) :
    ((a ^^ b ^^ c) && (d ^^ e ^^ f)) = ((a && d) ^^ (b && e) ^^ (c && f)) := by decide +revert

/-- Over F₂ the product of two affine bits is affine iff their slopes are
linearly dependent. This includes constant one in each of the three cases. -/
theorem affine_product_iff {o : X} {plus : X → X → X} {f g : X → Bool}
    (hf : Affine o plus f) (hg : Affine o plus g) :
    Affine o plus (band f g) ↔ Fixed o f ∨ Fixed o g ∨ Fixed o (bxor f g) := by
  constructor
  · intro hp
    have minor (x y : X) : ((f x ^^ f o) && (g y ^^ g o)) = ((f y ^^ f o) && (g x ^^ g o)) := by
      apply polar
      simpa only [band,hf x y,hg x y] using hp x y
    by_cases left : Fixed o f
    · exact Or.inl left
    · obtain ⟨x, hx⟩ := Classical.not_forall.mp left
      by_cases same : g x = g o
      · exact Or.inr (Or.inl (fun y => (rank_one _ _ _ _ _ _ (minor x y) hx).1 same))
      · exact Or.inr (Or.inr (fun y => (rank_one _ _ _ _ _ _ (minor x y) hx).2 same))
  · intro which x y
    simp only [band,hf x y,hg x y]
    apply sufficient_bits
    rcases which with H|H|H
    · exact Or.inl ⟨H x,H y⟩
    · exact Or.inr (Or.inl ⟨H x,H y⟩)
    · exact Or.inr (Or.inr ⟨H x,H y⟩)

def next (x y c : Bool) := ((x ^^ c) && (y ^^ c)) ^^ c

theorem carry_is_majority (x y c : Bool) : next x y c = ((x && y) || ((x ^^ y) && c)) := by decide +revert

def carry (x y : Nat → X → Bool) : Nat → X → Bool
  | 0, _ => false
  | n+1, v => next (x n v) (y n v) (carry x y n v)

def output (x y : Nat → X → Bool) (n : Nat) := bxor (bxor (x n) (y n)) (carry x y n)

def Local (o : X) (x y : Nat → X → Bool) (i : Nat) : Prop :=
  Fixed o (bxor (x i) (carry x y i)) ∨ Fixed o (bxor (y i) (carry x y i)) ∨ Fixed o (bxor (x i) (y i))

private theorem cancel (x y c : Bool) : ((x ^^ c) ^^ (y ^^ c)) = (x ^^ y) := by decide +revert
private theorem solve (a b : Bool) : (a ^^ (a ^^ b)) = b := by decide +revert
private theorem solve' (a b : Bool) : ((a ^^ b) ^^ b) = a := by decide +revert

private theorem carry_step {o : X} {plus : X → X → X} {x y : Nat → X → Bool} {i : Nat}
    (hx : Affine o plus (x i)) (hy : Affine o plus (y i)) (hc : Affine o plus (carry x y i)) :
    Affine o plus (carry x y (i+1)) ↔ Local o x y i := by
  let u := bxor (x i) (carry x y i)
  let v := bxor (y i) (carry x y i)
  have xorEq : bxor u v = bxor (x i) (y i) := by funext t; exact cancel _ _ _
  have hp := affine_product_iff (affine_xor hx hc) (affine_xor hy hc)
  change Affine o plus (band u v) ↔ Fixed o u ∨ Fixed o v ∨ Fixed o (bxor u v) at hp
  rw [xorEq] at hp
  constructor
  · intro hn
    apply hp.mp
    have e : bxor (carry x y (i+1)) (carry x y i) = band u v := by funext t; exact solve' _ _
    rw [←e]; exact affine_xor hn hc
  · intro h
    exact affine_xor (hp.mpr h) hc

/-- Exact local classification at width w. The carry out of the highest bit
is discarded. A width-one sum therefore imposes no triangular restriction. -/
theorem affine_addition_iff {o : X} {plus : X → X → X} (w : Nat) (x y : Nat → X → Bool)
    (hx : ∀ i < w, Affine o plus (x i)) (hy : ∀ i < w, Affine o plus (y i)) :
    (∀ i < w, Affine o plus (output x y i)) ↔ ∀ i, i+1 < w → Local o x y i := by
  have sums (i : Nat) (hi : i < w) : Affine o plus (output x y i) ↔ Affine o plus (carry x y i) := by
    have hxy := affine_xor (hx i hi) (hy i hi)
    constructor
    · intro ho
      have e : bxor (bxor (x i) (y i)) (output x y i) = carry x y i := by funext t; exact solve _ _
      rw [←e]; exact affine_xor hxy ho
    · exact fun h => affine_xor hxy h
  constructor
  · intro ha i hi
    have p : i < w := by omega
    exact (carry_step (hx i p) (hy i p) ((sums i p).mp (ha i p))).mp ((sums _ hi).mp (ha _ hi))
  · intro conditions
    have carries (i) (hi : i < w) : Affine o plus (carry x y i) := by
      induction i with
      | zero => intro _ _; rfl
      | succ i ih =>
        have p : i < w := by omega
        exact (carry_step (hx i p) (hy i p) (ih p)).mpr (conditions i hi)
    exact fun i hi => (sums i hi).mpr (carries i hi)

inductive Mode where
  | left (b : Bool)
  | right (b : Bool)
  | parity (b : Bool)
  deriving DecidableEq

abbrev Row := Bool × Bool

def allowed : Mode → Bool → Row → Bool
  | .left b, c, (x,_) => (x ^^ c) == b
  | .right b, c, (_,y) => (y ^^ c) == b
  | .parity b, _, (x,y) => (x ^^ y) == b

def row : Mode → Bool → Bool → Row
  | .left b, c, f => (c ^^ b,f)
  | .right b, c, f => (f,c ^^ b)
  | .parity b, _, f => (f,f ^^ b)

def free : Mode → Row → Bool
  | .left _, p => p.2
  | .right _, p | .parity _, p => p.1

theorem row_inverse (m : Mode) (c f : Bool) :
    allowed m c (row m c f) = true ∧ free m (row m c f) = f := by
  cases m <;> decide +revert

theorem row_surjective (m : Mode) (c : Bool) (p : Row) (h : allowed m c p = true) :
    row m c (free m p) = p := by
  rcases p with ⟨x,y⟩
  cases m <;> decide +revert

def nextRow (p : Row) (c : Bool) := next p.1 p.2 c

theorem signed_projection (m : Mode) (c f : Bool) :
    let p := row m c f
    (((p.1 ^^ p.2) ^^ c), nextRow p c) = match m with
      | .left b | .right b => (f ^^ b, if b then f else c)
      | .parity b => (c ^^ b, if b then c else f) := by
  cases m <;> decide +revert

def accepted : List Mode → Bool → List Row → Prop
  | [], _, [_] => True
  | m::ms, c, p::ps => allowed m c p = true ∧ accepted ms (nextRow p c) ps
  | _, _, _ => False

def params : List Mode → Type
  | [] => Row
  | _::ms => Bool × params ms

def encode : (ms : List Mode) → Bool → params ms → List Row
  | [], _, p => [p]
  | m::ms, c, (f,rest) => let p := row m c f; p :: encode ms (nextRow p c) rest

theorem accepts_encoding (ms : List Mode) (c : Bool) (v : params ms) :
    accepted ms c (encode ms c v) := by
  induction ms generalizing c with
  | nil => trivial
  | cons m ms ih => exact ⟨(row_inverse m c v.1).1,ih _ _⟩

theorem parameter_injective (ms : List Mode) (c : Bool) {u v : params ms}
    (h : encode ms c u = encode ms c v) : u = v := by
  induction ms generalizing c with
  | nil => simpa [encode] using h
  | cons m ms ih =>
    rcases u with ⟨f,u⟩; rcases v with ⟨g,v⟩
    have hh := List.cons.inj h
    have e := congrArg (free m) hh.1
    rw [(row_inverse m c f).2,(row_inverse m c g).2] at e
    subst g
    exact Prod.ext rfl (ih _ hh.2)

theorem parameter_surjective (ms : List Mode) (c : Bool) (ps : List Row)
    (h : accepted ms c ps) : ∃ v : params ms, encode ms c v = ps := by
  induction ms generalizing c ps with
  | nil =>
    cases ps with
    | nil => contradiction
    | cons p ps => cases ps with
      | nil => exact ⟨p,rfl⟩
      | cons _ _ => contradiction
  | cons m ms ih =>
    cases ps with
    | nil => contradiction
    | cons p ps =>
      obtain ⟨v,hv⟩ := ih _ _ h.2
      exact ⟨(free m p,v), by simp only [encode, row_surjective m c p h.1, hv]⟩

private def sample : (ms : List Mode) → params ms
  | [] => (false,false)
  | _::ms => (false, sample ms)

private theorem row_extendible (m : Mode) (ms : List Mode) (c : Bool) (p : Row) :
    (∃ ps, accepted (m::ms) c (p::ps)) ↔ allowed m c p = true := by
  constructor
  · rintro ⟨_,h⟩; exact h.1
  · intro h; exact ⟨_,h,accepts_encoding ms _ (sample ms)⟩

private theorem mode_injective (m m' : Mode) (c : Bool)
    (h : ∀ p, allowed m c p = allowed m' c p) : m = m' := by
  have a := h (false,false); have b := h (false,true)
  have d := h (true,false); have e := h (true,true)
  clear h
  cases m <;> cases m' <;> decide +revert

/-- Distinct triangular choices give distinct sets of input words. -/
theorem language_injective (ms ns : List Mode) (c : Bool) (len : ms.length = ns.length)
    (same : ∀ ps, accepted ms c ps ↔ accepted ns c ps) : ms = ns := by
  induction ms generalizing ns c with
  | nil => simpa using len.symm
  | cons m ms ih =>
    cases ns with
    | nil => simp at len
    | cons n ns =>
      have eqMode : m = n := by
        apply mode_injective m n c
        intro p
        apply Bool.eq_iff_iff.mpr
        rw [← row_extendible m ms c p, ← row_extendible n ns c p]
        exact exists_congr (fun ps => same (p::ps))
      subst n
      let p := row m c false
      have yes : allowed m c p = true := (row_inverse m c false).1
      have eqRest := ih ns (nextRow p c) (by simpa using len) (fun ps => by
        simpa [accepted,yes] using same (p::ps))
      rw [eqRest]

/-- Every parametrized affine restriction on which the whole sum stays affine
satisfies one common triangular mode per low coordinate, simultaneously on
all its inputs. -/
theorem common_modes {o : X} {plus : X → X → X} (w : Nat) (x y : Nat → X → Bool)
    (hx : ∀ i < w, Affine o plus (x i)) (hy : ∀ i < w, Affine o plus (y i))
    (ha : ∀ i < w, Affine o plus (output x y i)) :
    ∃ modes : Fin (w-1) → Mode, ∀ i v,
      allowed (modes i) (carry x y i.val v) (x i.val v,y i.val v) = true := by
  classical
  have chooseMode (i : Fin (w-1)) : ∃ m : Mode, ∀ v,
      allowed m (carry x y i.val v) (x i.val v,y i.val v) = true := by
    have hi := i.isLt
    rcases (affine_addition_iff w x y hx hy).mp ha i.val (by omega) with h|h|h
    · exact ⟨.left (bxor (x i.val) (carry x y i.val) o), fun v => beq_iff_eq.mpr (h v)⟩
    · exact ⟨.right (bxor (y i.val) (carry x y i.val) o), fun v => beq_iff_eq.mpr (h v)⟩
    · exact ⟨.parity (bxor (x i.val) (y i.val) o), fun v => beq_iff_eq.mpr (h v)⟩
  exact ⟨fun i => (chooseMode i).choose, fun i => (chooseMode i).choose_spec⟩

def allParams : (ms : List Mode) → List (params ms)
  | [] => [(false,false),(false,true),(true,false),(true,true)]
  | _::ms => (allParams ms).map (fun z => (false,z)) ++ (allParams ms).map (fun z => (true,z))

theorem allParams_length (ms : List Mode) : (allParams ms).length = 4 * 2 ^ ms.length := by
  induction ms with
  | nil => decide
  | cons m ms ih => simp [allParams,ih,Nat.pow_succ]; omega

def allModes : List Mode := [.left false,.left true,.right false,.right true,.parity false,.parity true]

def allModeLists : Nat → List (List Mode)
  | 0 => [[]]
  | n+1 => allModes.flatMap (fun m => (allModeLists n).map (fun ms => m::ms))

theorem allModeLists_length (n : Nat) : (allModeLists n).length = 6^n := by
  induction n with
  | zero => decide
  | succ n ih => simp [allModeLists,allModes,ih,Nat.pow_succ]; omega

def xor3 (a b c : Bool) := (a ^^ b) ^^ c

def combineRow (a b c : Row) : Row := (xor3 a.1 b.1 c.1, xor3 a.2 b.2 c.2)

def zip3 (op : A → A → A → A) : List A → List A → List A → List A
  | a::as, b::bs, c::cs => op a b c :: zip3 op as bs cs
  | _,_,_ => []

def combineParams : (ms : List Mode) → params ms → params ms → params ms → params ms
  | [], a, b, c => combineRow a b c
  | _::ms, (a,as), (b,bs), (c,cs) => (xor3 a b c, combineParams ms as bs cs)

def lane (p : Row) (c : Bool) := xor3 p.1 p.2 c

def addWord : List Row → Bool → List Bool
  | [], _ => []
  | p::ps, c => lane p c :: addWord ps (nextRow p c)

private theorem row_ternary (m : Mode) (c d e f g h : Bool) :
    row m (xor3 c d e) (xor3 f g h) = combineRow (row m c f) (row m d g) (row m e h) ∧
    nextRow (row m (xor3 c d e) (xor3 f g h)) (xor3 c d e) =
      xor3 (nextRow (row m c f) c) (nextRow (row m d g) d) (nextRow (row m e h) e) := by
  cases m <;> decide +revert

private theorem lane_ternary (a b c : Row) (i j k : Bool) :
    lane (combineRow a b c) (xor3 i j k) = xor3 (lane a i) (lane b j) (lane c k) := by
  rcases a with ⟨_,_⟩; rcases b with ⟨_,_⟩; rcases c with ⟨_,_⟩
  decide +revert

/-- Every mode language is affinely parametrized and its entire sum is affine
in the same free parameters. Over F₂ the ternary-XOR identities include all
translated flats. -/
theorem affine_parametrization (ms : List Mode) (a b c : params ms) (i j k : Bool) :
    encode ms (xor3 i j k) (combineParams ms a b c) =
      zip3 combineRow (encode ms i a) (encode ms j b) (encode ms k c) ∧
    addWord (encode ms (xor3 i j k) (combineParams ms a b c)) (xor3 i j k) =
      zip3 xor3 (addWord (encode ms i a) i) (addWord (encode ms j b) j) (addWord (encode ms k c) k) := by
  induction ms generalizing i j k with
  | nil => exact ⟨rfl,congrArg (fun z => [z]) (lane_ternary a b c i j k)⟩
  | cons m ms ih =>
    rcases a with ⟨f,as⟩; rcases b with ⟨g,bs⟩; rcases c with ⟨h,cs⟩
    have step := row_ternary m i j k f g h
    have tail := ih as bs cs (nextRow (row m i f) i) (nextRow (row m j g) j) (nextRow (row m k h) k)
    simp only [encode,combineParams,addWord,zip3]
    rw [step.2]
    rw [tail.2,tail.1,step.1,lane_ternary]
    exact ⟨rfl,rfl⟩

#print axioms affine_product_iff
#print axioms affine_addition_iff
#print axioms signed_projection
#print axioms language_injective
#print axioms common_modes
#print axioms affine_parametrization

end CarryFlatAddition
