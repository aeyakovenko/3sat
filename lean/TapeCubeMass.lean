import Std

namespace List

@[simp] def tapeWeightProduct : List Nat → Nat
  | [] => 1
  | x :: xs => x * tapeWeightProduct xs

end List

namespace TapeCubeMass

/-- All block error fractions have denominator D. Multiplying two retained
    fractions loses at most the sum of the error numerators. -/
private theorem twoLoss (D a b : Nat) :
    D * (D - (a+b)) ≤ (D-a)*(D-b) := by
  by_cases h : a+b ≤ D
  · obtain ⟨k, eq⟩ := Nat.exists_eq_add_of_le h
    subst D
    have x : a+b+k-a=b+k := by omega
    have y : a+b+k-b=a+k := by omega
    have z : a+b+k-(a+b)=k := by omega
    rw [x,y,z]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm k a]
    omega
  · have hz : D-(a+b)=0 := by omega
    simp [hz]

/-- Fair and generated coordinate-pattern masses use the same integer
    scale in each block. The scales are allowed to differ between blocks.
    Their products are the masses of the joint event by independence. -/
theorem independentFloor {B : Type} (blocks : List B) (D : Nat) (pos : 0 < D)
    (err fair generated : B → Nat)
    (relative : ∀ b ∈ blocks, (D-err b)*fair b ≤ D*generated b) :
    (D-(blocks.map err).sum)*(blocks.map fair).tapeWeightProduct ≤ D*(blocks.map generated).tapeWeightProduct := by
  induction blocks with
  | nil => simp
  | cons b bs ih =>
    have head := relative b (by simp)
    have tail := ih (fun z hz => relative z (by simp [hz]))
    simp only [List.map_cons, List.sum_cons, List.tapeWeightProduct]
    apply Nat.le_of_mul_le_mul_left (c := D) _ pos
    calc
      D * ((D-(err b+(bs.map err).sum))*(fair b*(bs.map fair).tapeWeightProduct)) =
        (D*(D-(err b+(bs.map err).sum)))*(fair b*(bs.map fair).tapeWeightProduct) := by ac_rfl
      _ ≤ ((D-err b)*(D-(bs.map err).sum))*(fair b*(bs.map fair).tapeWeightProduct) :=
        Nat.mul_le_mul_right _ (twoLoss ..)
      _ = ((D-err b)*fair b)*((D-(bs.map err).sum)*(bs.map fair).tapeWeightProduct) := by ac_rfl
      _ ≤ (D*generated b)*(D*(bs.map generated).tapeWeightProduct) := Nat.mul_le_mul head tail
      _ = D*(D*(generated b*(bs.map generated).tapeWeightProduct)) := by ac_rfl

/-- The division-free form of 1-sum(e_i) ≤ product(1-e_i). -/
theorem productFloor (es : List Nat) (D : Nat) (pos : 0 < D) :
    (D-es.sum)*D^es.length ≤ D*(es.map (fun e => D-e)).tapeWeightProduct := by
  have constProduct : (es.map (fun _ => D)).tapeWeightProduct = D^es.length := by
    induction es with
    | nil => simp
    | cons e es ih => simp [Nat.pow_succ, Nat.mul_comm, ih]
  have h := independentFloor es D pos id (fun _ => D) (fun e => D-e)
    (fun e _ => by exact Nat.le_of_eq (Nat.mul_comm ..))
  simpa [constProduct] using h

/-- Integer mass of an event in a finite weighted sample space. A list
    with unit weights can enumerate equally likely distinct random tapes. -/
def mass {X : Type} (xs : List X) (weight : X → Nat) (e : X → Bool) : Nat :=
  (xs.map (fun x => if e x then weight x else 0)).sum

private theorem addDisjoint {X : Type} (xs : List X) (w : X → Nat) (a b : X → Bool)
    (disj : ∀ x ∈ xs, a x = true → b x = false) :
    mass xs w (fun x => a x || b x) = mass xs w a + mass xs w b := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih =>
    have ht := ih (fun z hz => disj z (by simp [hz]))
    have hh := disj x (by simp)
    cases ha : a x <;> cases hb : b x <;> simp [mass, ha, hb] at * <;> omega

/-- Pairwise disjoint successful cylinders may have different shapes and
    sizes. Their masses add without any independence between cylinders. -/
theorem disjointMass {X C : Type} (xs : List X) (w : X → Nat) (cs : List C)
    (hit : C → X → Bool) (nd : cs.Nodup)
    (disj : ∀ x ∈ xs, ∀ a ∈ cs, ∀ b ∈ cs,
      hit a x = true → hit b x = true → a = b) :
    mass xs w (fun x => cs.any (fun c => hit c x)) = (cs.map (fun c => mass xs w (hit c))).sum := by
  induction cs with
  | nil =>
    simp only [List.any_nil, mass, Bool.false_eq_true, ↓reduceIte, List.map_nil, List.sum_nil]
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa using ih (fun _ _ _ h => by simp at h)
  | cons c cs ih =>
    obtain ⟨absent,nodup⟩ := List.nodup_cons.mp nd
    have rest := ih nodup (fun x hx a ha b hb => disj x hx a (by simp [ha]) b (by simp [hb]))
    have sep : ∀ x ∈ xs, hit c x = true → (cs.any (fun z => hit z x)) = false := by
      intro x hx hc
      cases hh : cs.any (fun z => hit z x) with
      | false => rfl
      | true =>
        obtain ⟨z,hz,ht⟩ := List.any_eq_true.mp hh
        have eq := disj x hx c (by simp) z (by simp [hz]) hc ht
        exact (absent (eq ▸ hz)).elim
    simpa only [List.any_cons, List.map_cons, List.sum_cons, ← rest] using
      addDisjoint xs w (hit c) (fun x => cs.any (fun z => hit z x)) sep

private theorem sumScales {C : Type} (cs : List C) (A B : Nat) (f g : C → Nat)
    (bound : ∀ c ∈ cs, A*f c ≤ B*g c) :
    A*(cs.map f).sum ≤ B*(cs.map g).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have h := bound c (by simp)
    have t := ih (fun z hz => bound z (by simp [hz]))
    simpa [Nat.mul_add] using Nat.add_le_add h t

/-- After matching the fair and generated mass units for each block, a
    uniform additive error budget for every successful cylinder also bounds
    the relative loss on their union. The fair and generated product
    factorization premises express block independence for the given law. -/
theorem successfulCylinderMass {X C B : Type} (xs : List X) (f g : X → Nat)
    (cs : List C) (hit : C → X → Bool) (nd : cs.Nodup)
    (disj : ∀ x ∈ xs, ∀ a ∈ cs, ∀ b ∈ cs, hit a x = true → hit b x = true → a = b)
    (bs : List B) (fair gen err : C → B → Nat) (D E : Nat) (pos : 0 < D)
    (ff : ∀ c ∈ cs, mass xs f (hit c) = (bs.map (fair c)).tapeWeightProduct)
    (fg : ∀ c ∈ cs, mass xs g (hit c) = (bs.map (gen c)).tapeWeightProduct)
    (loss : ∀ c ∈ cs, (bs.map (err c)).sum ≤ E)
    (relative : ∀ c ∈ cs, ∀ b ∈ bs, (D-err c b)*fair c b ≤ D*gen c b) :
    (D-E)*mass xs f (fun x => cs.any (fun c => hit c x)) ≤
      D*mass xs g (fun x => cs.any (fun c => hit c x)) := by
  rw [disjointMass xs f cs hit nd disj, disjointMass xs g cs hit nd disj]
  apply sumScales
  intro c hc
  rw [ff c hc, fg c hc]
  have hb : D-E ≤ D-(bs.map (err c)).sum := by have := loss c hc; omega
  exact Nat.le_trans (Nat.mul_le_mul_right _ hb)
    (independentFloor bs D pos _ _ _ (relative c hc))

private theorem sumAppend (a b : List Nat) : (a++b).sum = a.sum+b.sum := by
  induction a with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc]

private theorem constantOn {X : Type} (xs : List X) (w : X → Nat) (e : X → Bool) (b : Bool)
    (stable : ∀ x ∈ xs, e x = b) :
    mass xs w e = if b then (xs.map w).sum else 0 := by
  induction xs with
  | nil => cases b <;> simp [mass]
  | cons x xs ih =>
    have tail := ih (fun z hz => stable z (by simp [hz]))
    have head := stable x (by simp)
    cases b <;> simp [mass, head] at * <;> omega

/-- Extending the finite tape horizon preserves the probability of every
    earlier event when all child masses add to the parent, after a common
    scale conversion. No independence is needed for this consistency step. -/
theorem horizonRefinement {X Y : Type} (parents : List X) (children : X → List Y)
    (oldWeight : X → Nat) (newWeight : Y → Nat) (D : Nat)
    (oldHit : X → Bool) (newHit : Y → Bool)
    (normalize : ∀ x ∈ parents, ((children x).map newWeight).sum = D*oldWeight x)
    (stable : ∀ x ∈ parents, ∀ y ∈ children x, newHit y = oldHit x) :
    mass (parents.flatMap children) newWeight newHit = D*mass parents oldWeight oldHit := by
  induction parents with
  | nil => simp [mass]
  | cons x xs ih =>
    have tail := ih (fun z hz => normalize z (by simp [hz]))
      (fun z hz => stable z (by simp [hz]))
    have head := constantOn (children x) newWeight newHit (oldHit x) (stable x (by simp))
    have total := normalize x (by simp)
    cases h : oldHit x <;>
      simp [mass, h, Nat.mul_add, sumAppend] at head tail ⊢ <;> omega

end TapeCubeMass
