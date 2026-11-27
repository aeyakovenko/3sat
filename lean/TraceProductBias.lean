import Std

namespace TraceProductBias

def total (domain : List α) (f : α → Int) : Int :=
  (domain.map f).sum

private theorem permSum {xs ys : List Int} (p : xs.Perm ys) : xs.sum = ys.sum := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp [Int.add_comm, Int.add_left_comm, Int.add_assoc]
  | trans _ _ p q => exact p.trans q

private theorem totalAdd (xs : List α) (f g : α → Int) :
    total xs (fun x => f x + g x) = total xs f + total xs g := by
  induction xs with
  | nil => simp [total]
  | cons a xs ih =>
    change (f a + g a) + total xs _ = (f a + total xs f) + (g a + total xs g)
    rw [ih]; omega

private theorem totalScale (xs : List α) (c : Int) (f : α → Int) :
    total xs (fun x => c * f x) = c * total xs f := by
  induction xs with
  | nil => simp [total]
  | cons a xs ih =>
    change c * f a + total xs _ = c * (f a + total xs f)
    rw [ih, Int.mul_add]

private theorem totalZero (xs : List α) : total xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change 0 + total xs _ = 0
    omega

private theorem totalSwap (xs : List α) (ys : List β) (g : α → β → Int) :
    total xs (fun x => total ys (g x)) = total ys (fun y => total xs (fun x => g x y)) := by
  induction xs with
  | nil => exact (totalZero ys).symm
  | cons x xs ih =>
    change total ys (g x) + total xs _ =
      total ys (fun y => g x y + total xs (fun u => g u y))
    rw [totalAdd, ih]

theorem totalTranslate (xs : List α) (f : α → Int) (shift : α → α)
    (p : (xs.map shift).Perm xs) : total xs (fun x => f (shift x)) = total xs f := by
  simpa [total, List.map_map, Function.comp_def] using permSum (p.map f)

/-- Exact finite autocorrelation whenever each family of translates enumerates the domain. -/
theorem autocorrelation (xs : List α) (add : α → α → α)
    (translate : ∀ x, (xs.map (add x)).Perm xs) (f : α → Int) :
    total xs (fun z => total xs (fun x => f x * f (add x z))) = total xs f * total xs f := by
  rw [totalSwap]
  have row (x : α) : total xs (fun z => f x * f (add x z)) = f x * total xs f := by
    rw [totalScale, totalTranslate xs f _ (translate x)]
  simp only [row]
  simpa only [Int.mul_comm] using totalScale xs (total xs f) f

/-- A shift that reverses every sign cancels the whole sum. -/
theorem shiftCancellation (xs : List α) (f : α → Int) (shift : α → α)
    (p : (xs.map shift).Perm xs) (flip : ∀ x, f (shift x) = -f x) :
    total xs f = 0 := by
  have h := totalTranslate xs f shift p
  have eq (x : α) : f (shift x) = (-1 : Int) * f x := by simp [flip]
  simp only [eq, totalScale] at h
  omega


def sign (b : Bool) : Int := if b then -1 else 1

private theorem signXor (a b : Bool) : sign (a ^^ b) = sign a * sign b := by
  cases a <;> cases b <;> decide

private theorem totalConst (xs : List α) (k : Int) : total xs (fun _ => k) = xs.length * k := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    change k + total xs _ = ((xs.length+1 : Nat) : Int) * k
    rw [ih]
    simp [Int.add_mul, Int.add_comm]

/-- A quadratic phase has zero sum if its first derivative is one on a radical vector. -/
theorem radicalCancellation (xs : List α) (add : α → α → α)
    (plusPerm : ∀ z, (xs.map (fun x => add x z)).Perm xs) (F : α → Bool)
    (z : α) (odd : ∀ x, (F x ^^ F (add x z)) = true) :
    total xs (fun x => sign (F x)) = 0 := by
  apply shiftCancellation xs _ _ (plusPerm z)
  intro x
  have h := odd x
  cases a : F x <;> cases b : F (add x z) <;> simp [a,b,sign] at *

/-- The signed autocorrelation of a quadratic is supported on its polar radical. -/
theorem quadraticMoment (xs : List α) (add : α → α → α)
    (leftPerm : ∀ z, (xs.map (add z)).Perm xs)
    (rightPerm : ∀ z, (xs.map (fun x => add x z)).Perm xs)
    (F c rad : α → Bool) (polar : α → α → Bool)
    (derivative : ∀ x z, (F x ^^ F (add x z)) = (c z ^^ polar z x))
    (linear : ∀ z x t, polar z (add x t) = (polar z x ^^ polar z t))
    (inside : ∀ z, rad z = true → ∀ x, polar z x = false)
    (outside : ∀ z, rad z = false → ∃ t, polar z t = true) :
    total xs (fun x => sign (F x)) * total xs (fun x => sign (F x)) =
    xs.length * total xs (fun z => if rad z then sign (c z) else 0) := by
  have row (z : α) :
      total xs (fun x => sign (F x) * sign (F (add x z))) =
      xs.length * (if rad z then sign (c z) else 0) := by
    have eq (x : α) :
        sign (F x) * sign (F (add x z)) = sign (c z) * sign (polar z x) := by
      rw [← signXor, derivative, signXor]
    simp only [eq]
    cases b : rad z with
    | true =>
      simp only [inside z b, sign, Bool.false_eq_true, if_false, Int.mul_one, if_true,
        totalConst]
    | false =>
      obtain ⟨t, ht⟩ := outside z b
      have vanish : total xs (fun x => sign (polar z x)) = 0 := by
        apply shiftCancellation xs _ _ (rightPerm t)
        intro x
        rw [linear, ht]
        cases polar z x <;> decide
      simp [totalScale, vanish]
  rw [← autocorrelation xs add leftPerm, ← totalScale]
  simp only [row]

/-- Expansion of the second derivative of a balanced trilinear phase in collinear
directions. For the trace product, scale is multiplication by the field element t. -/
theorem collinearDerivative (plus : α → α → α) (scale : α → α)
    (triple : α → α → α → Bool)
    (linear₁ : ∀ a b c d, triple (plus a b) c d = (triple a c d ^^ triple b c d))
    (linear₂ : ∀ a b c d, triple a (plus b c) d = (triple a b d ^^ triple a c d))
    (linear₃ : ∀ a b c d, triple a b (plus c d) = (triple a b c ^^ triple a b d))
    (transfer₁ : ∀ a b c, triple (scale a) b c = triple a b (scale c))
    (transfer₂ : ∀ a b c, triple a (scale b) c = triple a b (scale c))
    (x y z a b c : α) :
    (triple x y z ^^ triple (plus x a) (plus y b) (plus z c) ^^
      triple (plus x (scale a)) (plus y (scale b)) (plus z (scale c)) ^^
      triple (plus (plus x a) (scale a)) (plus (plus y b) (scale b))
        (plus (plus z c) (scale c))) =
    (triple a b (scale (scale c)) ^^ triple a b (scale c)) := by
  simp only [linear₁, linear₂, linear₃, transfer₁, transfer₂]
  bv_decide

private theorem totalLe (xs : List α) (f g : α → Int)
    (le : ∀ x ∈ xs, f x ≤ g x) : total xs f ≤ total xs g := by
  induction xs with
  | nil => exact Int.le_refl _
  | cons a xs ih =>
    change f a + total xs f ≤ g a + total xs g
    exact Int.add_le_add (le a (by simp)) (ih (fun x hx => le x (by simp [hx])))

/-- A binary-linear obstruction in the scalar variable contributes a full row
precisely on compatible directions. The two exceptional scalar columns and the
pointwise bounds on the others imply the unnormalized compatibility moment. -/
theorem compatibilityMoment (shifts : List α) (s₀ s₁ : β) (rest : List β)
    (add : β → β → β) (compat : α → Bool) (obstruction : α → β → Bool) (B : Int)
    (perm : ∀ u, ((s₀ :: s₁ :: rest).map (fun x => add x u)).Perm (s₀ :: s₁ :: rest))
    (linear : ∀ z x y, obstruction z (add x y) = (obstruction z x ^^ obstruction z y))
    (positive : ∀ z, compat z = true → ∀ t, obstruction z t = false)
    (negative : ∀ z, compat z = false → ∃ t, obstruction z t = true)
    (zeroCol : ∀ z, obstruction z s₀ = false)
    (oneCol : ∀ z, obstruction z s₁ = false)
    (otherCols : ∀ t ∈ rest, total shifts (fun z => sign (obstruction z t)) ≤ B) :
    ((s₀ :: s₁ :: rest).length : Int) * total shifts (fun z => if compat z then 1 else 0)
      ≤ 2 * (shifts.length : Int) + rest.length * B := by
  let scalars := s₀ :: s₁ :: rest
  have row (z : α) : total scalars (fun t => sign (obstruction z t)) =
      (scalars.length : Int) * (if compat z then 1 else 0) := by
    cases h : compat z with
    | true => simp [positive z h, sign, totalConst]
    | false =>
      obtain ⟨t, ht⟩ := negative z h
      have van : total scalars (fun b => sign (obstruction z b)) = 0 := by
        apply shiftCancellation scalars _ _ (perm t)
        intro x
        rw [linear, ht]
        cases obstruction z x <;> decide
      simp [van]
  have eq : (scalars.length : Int) * total shifts (fun z => if compat z then 1 else 0) =
      total scalars (fun t => total shifts (fun z => sign (obstruction z t))) := by
    rw [← totalSwap]
    simp only [row, totalScale]
  change (scalars.length : Int) * total shifts _ ≤ _
  rw [eq]
  change total shifts (fun z => sign (obstruction z s₀)) +
      (total shifts (fun z => sign (obstruction z s₁)) +
        total rest (fun t => total shifts (fun z => sign (obstruction z t)))) ≤ _
  have bound := totalLe rest _ (fun _ => B) otherCols
  rw [totalConst] at bound
  have signFalse : sign false = 1 := by decide
  simp only [zeroCol, oneCol, signFalse, totalConst, Int.mul_one]
  omega

/-- Finite counting form of the first moment bound, with the zero direction
handled separately from the compatible nonzero directions. -/
theorem compatibleDerivativeBound (zero : α) (rest : List α)
    (corr : α → Int) (compat : α → Bool) (q B : Int)
    (zeroCompat : compat zero = true) (zeroSum : corr zero = q*q*q)
    (corrBound : ∀ z ∈ rest, corr z ≤ q*q * (if compat z then 1 else 0))
    (moment : B*B = total (zero :: rest) corr) :
    B*B ≤ q*q*q + (q*q)*(total (zero :: rest) (fun z => if compat z then 1 else 0)-1) := by
  have sumBound := totalLe rest _ _ corrBound
  simp only [totalScale] at sumBound
  rw [moment]
  change corr zero + total rest corr ≤ q*q*q + q*q*((if compat zero then 1 else 0) +
    total rest (fun z => if compat z then 1 else 0)-1)
  rw [zeroSum, zeroCompat]
  simp only [if_true]
  have simpl (a : Int) : 1 + a - 1 = a := by omega
  rw [simpl]
  omega

/-- The two unnormalized moment bounds imply the sharp scalar bias bound. -/
theorem sharpMoment (q B E : Int) (qPos : 0 < q)
    (first : B*B ≤ q*q*q + (q*q)*(E-1))
    (second : q*E ≤ 2*(q*q*q) + (q-2)*B) :
    B ≤ 2*(q*q)-q := by
  have qSq := Int.mul_pos qPos qPos
  have scaled := Int.mul_le_mul_of_nonneg_left second (Int.le_of_lt qPos)
  have factor :
      (B-(2*(q*q)-q))*(B+q*q+q) ≤ 0 := by
    rw [show (2:Int) = 1+1 by decide] at scaled ⊢
    simp only [Int.add_mul, Int.sub_mul, Int.mul_sub, Int.mul_add, Int.mul_one, Int.one_mul] at *
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at *
    omega
  by_cases h : B ≤ 2*(q*q)-q
  · exact h
  · have p : 0 < B-(2*(q*q)-q) := by omega
    have p' : 0 < B + q*q + q := by omega
    have hp := Int.mul_pos p p'
    omega

def Pairs : Nat → Type
  | 0 => Unit
  | n+1 => (Bool × Bool) × Pairs n

def bitPairs : List (Bool × Bool) :=
  [(false,false), (false,true), (true,false), (true,true)]

def cubeSum : (n : Nat) → (Pairs n → Int) → Int
  | 0, f => f ()
  | n+1, f => total bitPairs (fun p => cubeSum n (fun x => f (p,x)))

def pairPhase (ab uv : Bool × Bool) : Bool :=
  ((uv.1 && uv.2) ^^ (ab.1 && uv.1)) ^^ (ab.2 && uv.2)

def quadraticPhase : (n : Nat) → Pairs n → Pairs n → Bool
  | 0, _, _ => false
  | n+1, (ab, rest), (uv, xs) => pairPhase ab uv ^^ quadraticPhase n rest xs

def dotPhase : (n : Nat) → Pairs n → Bool
  | 0, _ => false
  | n+1, (ab, rest) => (ab.1 && ab.2) ^^ dotPhase n rest

private theorem cubeScale (n : Nat) (c : Int) (f : Pairs n → Int) :
    cubeSum n (fun x => c * f x) = c * cubeSum n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cubeSum, ih, totalScale]

private theorem onePair : ∀ ab : Bool × Bool,
    total bitPairs (fun uv => sign (pairPhase ab uv)) = 2 * sign (ab.1 && ab.2) := by
  intro ab
  obtain ⟨a,b⟩ := ab
  cases a <;> cases b <;> decide

/-- The symplectic sign sum used by the matching adaptive query construction. -/
theorem symplecticGaussian (n : Nat) (linearBits : Pairs n) :
    cubeSum n (fun xs => sign (quadraticPhase n linearBits xs)) =
      (2 : Int)^n * sign (dotPhase n linearBits) := by
  induction n with
  | zero => simp [cubeSum, quadraticPhase, dotPhase]
  | succ n ih =>
    obtain ⟨ab, tail⟩ := linearBits
    simp only [cubeSum, quadraticPhase, signXor, cubeScale, ih, dotPhase, Int.pow_succ]
    have switch (x y : Int) : x*y=y*x := Int.mul_comm _ _
    have swap (uv : Bool × Bool) :
        sign (pairPhase ab uv) * (2 ^ n * sign (dotPhase n tail)) =
          (2 ^ n * sign (dotPhase n tail)) * sign (pairPhase ab uv) := switch _ _
    simp only [swap, totalScale, onePair]
    ac_rfl

/-- An XOR of monomials. Repeated variables in a monomial are allowed;
their Boolean simplification can only lower its degree. -/
abbrev Polynomial (I : Type) := List (List I)

def monomial (assign : I → Bool) : List I → Bool
  | [] => true
  | x :: xs => assign x && monomial assign xs

def evaluate (assign : I → Bool) : Polynomial I → Bool
  | [] => false
  | term :: rest => monomial assign term ^^ evaluate assign rest

def degreeBound (p : Polynomial I) (d : Nat) : Prop := ∀ term ∈ p, term.length ≤ d

def productPolynomial (p q : Polynomial I) : Polynomial I :=
  p.flatMap (fun term => q.map (term ++ ·))

private theorem monomialAppend (assign : I → Bool) (a b : List I) :
    monomial assign (a++b) = (monomial assign a && monomial assign b) := by
  induction a with
  | nil => simp [monomial]
  | cons x xs ih => simp [monomial, ih, Bool.and_assoc]

private theorem evaluateAppend (assign : I → Bool) (p q : Polynomial I) :
    evaluate assign (p++q) = (evaluate assign p ^^ evaluate assign q) := by
  induction p with
  | nil => simp [evaluate]
  | cons x xs ih => simp [evaluate, ih, Bool.xor_assoc]

private theorem evaluateScaled (assign : I → Bool) (term : List I) (q : Polynomial I) :
    evaluate assign (q.map (term ++ ·)) = (monomial assign term && evaluate assign q) := by
  induction q with
  | nil => simp [evaluate]
  | cons x xs ih =>
    simp only [List.map_cons, evaluate, monomialAppend, ih]
    cases monomial assign term <;> simp

theorem evaluateProduct (assign : I → Bool) (p q : Polynomial I) :
    evaluate assign (productPolynomial p q) = (evaluate assign p && evaluate assign q) := by
  induction p with
  | nil => simp [productPolynomial, evaluate]
  | cons x xs ih =>
    change evaluate assign (q.map (x ++ ·) ++ productPolynomial xs q) = _
    rw [evaluateAppend, evaluateScaled, ih]
    simp only [evaluate]
    cases evaluate assign q <;> simp

theorem degreeProduct (p q : Polynomial I) (dp dq : Nat)
    (hp : degreeBound p dp) (hq : degreeBound q dq) :
    degreeBound (productPolynomial p q) (dp+dq) := by
  intro term member
  obtain ⟨u, hu, v⟩ := List.mem_flatMap.mp member
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp v
  simp only [List.length_append]
  exact Nat.add_le_add (hp u hu) (hq w hw)

/-- The polynomial whose value asserts that all prescribed branch bits were seen. -/
def pathPolynomial : List (Polynomial I × Bool) → Polynomial I
  | [] => [[]]
  | (p, b) :: rest =>
    productPolynomial (if b then p else [] :: p) (pathPolynomial rest)

theorem pathIndicates (assign : I → Bool) (path : List (Polynomial I × Bool)) :
    evaluate assign (pathPolynomial path) =
      path.all (fun probe => evaluate assign probe.1 == probe.2) := by
  induction path with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨p,b⟩ := pair
    simp only [pathPolynomial, evaluateProduct, ih, List.all_cons]
    cases b <;> simp [evaluate, monomial]

theorem pathDegree (path : List (Polynomial I × Bool)) (limit : Nat)
    (h : ∀ entry ∈ path, degreeBound entry.1 limit) :
    degreeBound (pathPolynomial path) (path.length * limit) := by
  induction path with
  | nil => simp [pathPolynomial, degreeBound]
  | cons pair rest ih =>
    obtain ⟨p,b⟩ := pair
    have hp := h (p,b) (by simp)
    have ht := ih (fun entry mem => h entry (List.mem_cons_of_mem _ mem))
    have hf : degreeBound (if b then p else [] :: p) limit := by
      cases b
      · intro term mem
        simp only [Bool.false_eq_true, if_false, List.mem_cons] at mem
        rcases mem with rfl | hx
        · simp
        · exact hp term hx
      · exact hp
    simpa [pathPolynomial, Nat.succ_mul, Nat.add_comm] using
      degreeProduct _ _ _ _ hf ht

end TraceProductBias
