import Std

/-! Cutting binary wires produces independent terminal parts. If each part
contains at most two coordinates from each Hamming block, the product of
possible terminal assignments contains at most one tuple of codewords. -/
namespace GluedCodeCut

/-- Standard [7,4,3] Hamming encoding, with parity at positions 1,2,4
    when positions are numbered from one. -/
def hamming (message : Fin 16) (coordinate : Fin 7) : Bool :=
  let a := message.val.testBit 0
  let b := message.val.testBit 1
  let c := message.val.testBit 2
  let d := message.val.testBit 3
  match coordinate.val with
  | 0 => a ^^ b ^^ d
  | 1 => a ^^ c ^^ d
  | 2 => a
  | 3 => b ^^ c ^^ d
  | 4 => b
  | 5 => c
  | _ => d

def distance (a b : Fin 16) : Nat :=
  (List.finRange 7).countP (fun i => hamming a i != hamming b i)

theorem hamming_distance : ∀ a b : Fin 16, a ≠ b → 3 ≤ distance a b := by decide

theorem distance_attained : distance 0 1 = 3 := by decide

private theorem count_imp {X : Type} (xs : List X) (u v : X → Bool)
    (imp : ∀ x, u x = true → v x = true) : xs.countP u ≤ xs.countP v := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have h := imp a
    cases hu : u a <;> cases hv : v a <;> simp_all [List.countP_cons] <;> omega

theorem hamming_injective {a b : Fin 16} (eq : ∀ i, hamming a i = hamming b i) : a = b := by
  apply Classical.byContradiction
  intro ne
  have low := hamming_distance a b ne
  have high : distance a b = 0 := by simp [distance,eq]
  omega

theorem hamming_rigid {P : Type} [DecidableEq P] (owner : Fin 7 → P) (p : P)
    (small : (List.finRange 7).countP (fun i => decide (owner i = p)) ≤ 2)
    {a b : Fin 16} (off : ∀ i, owner i ≠ p → hamming a i = hamming b i) : a = b := by
  apply Classical.byContradiction
  intro ne
  have low := hamming_distance a b ne
  have high := count_imp (List.finRange 7)
    (fun i => hamming a i != hamming b i) (fun i => decide (owner i = p)) (by
      intro i disagrees
      by_cases same : owner i = p
      · simp [same]
      · simp [off i same] at disagrees)
  unfold distance at low
  omega

/-- Each local factor only inspects the terminals assigned to its own part. -/
def Local {I T P : Type} (owner : I → T → P)
    (factor : P → (I → T → Bool) → Prop) : Prop :=
  ∀ p x y, (∀ i t, owner i t = p → x i t = y i t) → (factor p x ↔ factor p y)

/-- Full Cartesian gluing on independent parts and closure inside a rigid
    product code imply uniqueness of the accepted tuple of messages. -/
theorem product_unique {I T P D : Type} [DecidableEq P]
    (owner : I → T → P) (code : D → T → Bool)
    (rigid : ∀ i p a b, (∀ t, owner i t ≠ p → code a t = code b t) → a = b)
    (injective : ∀ a b, (∀ t, code a t = code b t) → a = b)
    (factor : P → (I → T → Bool) → Prop) (loc : Local owner factor)
    (sound : ∀ z, (∀ p, factor p z) → ∃ m : I → D, ∀ i t, z i t = code (m i) t)
    (a b : I → D)
    (va : ∀ p, factor p (fun i t => code (a i) t))
    (vb : ∀ p, factor p (fun i t => code (b i) t)) : a = b := by
  funext i
  apply injective
  intro t
  let p := owner i t
  let z := fun j u => if owner j u = p then code (b j) u else code (a j) u
  have vz (q : P) : factor q z := by
    by_cases same : q = p
    · subst q
      apply (loc p z (fun j u => code (b j) u) ?_).mpr (vb p)
      intro j u belongs
      simp [z,belongs]
    · apply (loc q z (fun j u => code (a j) u) ?_).mpr (va q)
      intro j u belongs
      simp [z,belongs,same]
  obtain ⟨m,hm⟩ := sound z vz
  have agrees : m i = a i := rigid i p (m i) (a i) (by
    intro u elsewhere
    rw [← hm i u]
    simp [z,elsewhere])
  have bit := hm i t
  rw [agrees] at bit
  simpa [z,p] using bit.symm

theorem hamming_product_unique {I P : Type} [DecidableEq P]
    (owner : I → Fin 7 → P)
    (small : ∀ i p, (List.finRange 7).countP (fun t => decide (owner i t = p)) ≤ 2)
    (factor : P → (I → Fin 7 → Bool) → Prop) (loc : Local owner factor)
    (sound : ∀ z, (∀ p, factor p z) → ∃ m : I → Fin 16, ∀ i t, z i t = hamming (m i) t)
    (a b : I → Fin 16) (va : ∀ p, factor p (fun i t => hamming (a i) t))
    (vb : ∀ p, factor p (fun i t => hamming (b i) t)) : a = b :=
  product_unique owner hamming
    (fun i p _ _ => hamming_rigid (owner i) p (small i p))
    (fun _ _ => hamming_injective) factor loc sound a b va vb

/-- Vacant leaves model unmarked loose ends. Subdividing an edge of an
undirected subcubic tree gives a rooted binary tree of this form, after
suppressing unary vertices. -/
inductive Tree (I : Type) where
  | vacant
  | terminal (color : I)
  | fork (left right : Tree I)

def Tree.mass {I : Type} [DecidableEq I] : Tree I → I → Nat
  | .vacant, _ => 0
  | .terminal c, i => if c = i then 1 else 0
  | .fork t u, i => t.mass i + u.mass i

/-- A cut plan records the color populations of the component at the root
and one charge color for each actually removed child edge. -/
inductive Plan {I : Type} [DecidableEq I] :
    Tree I → (I → Nat) → List I → Prop where
  | vacant : Plan .vacant (fun _ => 0) []
  | terminal (c : I) : Plan (.terminal c) (fun i => if c = i then 1 else 0) []
  | join (l : Plan t a left) (r : Plan u b right)
      (fits : ∀ i, a i + b i ≤ 2) :
      Plan (.fork t u) (fun i => a i + b i) (left ++ right)
  | cutLeft (l : Plan t a left) (r : Plan u b right) (c : I) (two : a c = 2) :
      Plan (.fork t u) b (c :: (left ++ right))
  | cutRight (l : Plan t a left) (r : Plan u b right) (c : I) (two : b c = 2) :
      Plan (.fork t u) a (c :: (left ++ right))

theorem plan_bounds {I : Type} [DecidableEq I] {t : Tree I} {a paid}
    (plan : Plan t a paid) : ∀ i, a i ≤ 2 ∧ 2 * paid.count i + a i ≤ t.mass i := by
  induction plan with
  | vacant => simp [Tree.mass]
  | terminal c =>
    intro i
    by_cases h : c = i <;> simp [Tree.mass,h]
  | join l r fits il ir =>
    intro i
    obtain ⟨_,hl⟩ := il i
    obtain ⟨_,hr⟩ := ir i
    refine ⟨fits i, ?_⟩
    simp only [List.count_append,Tree.mass]
    omega
  | cutLeft l r c two il ir =>
    intro i
    obtain ⟨_,hl⟩ := il i
    obtain ⟨br,hr⟩ := ir i
    refine ⟨br, ?_⟩
    by_cases eq : c = i
    · subst i
      simp only [List.count_cons, List.count_append, beq_self_eq_true, ↓reduceIte,Tree.mass]
      omega
    · simp [List.count_cons,List.count_append,Tree.mass,beq_iff_eq,eq]
      omega
  | cutRight l r c two il ir =>
    intro i
    obtain ⟨al,hl⟩ := il i
    obtain ⟨_,hr⟩ := ir i
    refine ⟨al, ?_⟩
    by_cases eq : c = i
    · subst i
      simp only [List.count_cons,List.count_append,beq_self_eq_true,↓reduceIte,Tree.mass]
      omega
    · simp [List.count_cons,List.count_append,Tree.mass,beq_iff_eq,eq]
      omega

theorem colored_plan {I : Type} [DecidableEq I] (t : Tree I) :
    ∃ a paid, Plan t a paid := by
  classical
  induction t with
  | vacant => exact ⟨_, _, Plan.vacant⟩
  | terminal i => exact ⟨_, _, Plan.terminal i⟩
  | fork l r il ir =>
    obtain ⟨a,tl,pl⟩ := il
    obtain ⟨b,tr,pr⟩ := ir
    by_cases fits : ∀ i, a i+b i ≤ 2
    · exact ⟨_, _, Plan.join pl pr fits⟩
    · obtain ⟨c,hc⟩ := Classical.not_forall.mp fits
      by_cases full : a c = 2
      · exact ⟨_, _, Plan.cutLeft pl pr c full⟩
      · have ha := (plan_bounds pl c).1
        have hb := (plan_bounds pr c).1
        exact ⟨_, _, Plan.cutRight pl pr c (by omega)⟩

private def total {I : Type} [DecidableEq I] (bins xs : List I) : Nat :=
  (bins.map fun i => xs.count i).sum

private theorem total_cons {I : Type} [DecidableEq I] (bins xs : List I) (c : I) :
    total bins (c::xs) = total bins xs + bins.count c := by
  induction bins with
  | nil => simp [total]
  | cons a bs ih =>
    change (c::xs).count a + total bs (c::xs) = xs.count a + total bs xs + (a::bs).count c
    rw [ih]
    by_cases eq : c = a
    · subst a
      simp [List.count_cons]
      omega
    · simp [List.count_cons,beq_iff_eq,eq,Ne.symm eq]
      omega

private theorem total_bounds {I : Type} [DecidableEq I] (bins xs : List I)
    (covers : ∀ i ∈ xs, i ∈ bins) : xs.length ≤ total bins xs := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons c xs ih =>
    have prev := ih (fun i hi => covers i (by simp [hi]))
    have positive : 0 < bins.count c := List.count_pos_iff.mpr (covers c (by simp))
    rw [total_cons]
    simp only [List.length_cons]
    omega

private theorem total_cap {I : Type} [DecidableEq I] (bins xs : List I) (cap : Nat)
    (per : ∀ i, xs.count i ≤ cap) : total bins xs ≤ cap*bins.length := by
  induction bins with
  | nil => simp [total]
  | cons c cs ih =>
    change xs.count c + total cs xs ≤ cap*(cs.length+1)
    have bound := per c
    rw [Nat.mul_succ]
    omega

theorem hamming_tree_cut {q : Nat} (t : Tree (Fin q)) (size : ∀ i, t.mass i ≤ 7) :
    ∃ a paid, Plan t a paid ∧ paid.length ≤ 3*q := by
  obtain ⟨a,paid,plan⟩ := colored_plan t
  refine ⟨a,paid,plan,?_⟩
  have per (i : Fin q) : paid.count i ≤ 3 := by
    have bound := (plan_bounds plan i).2
    have cap := size i
    omega
  have low := total_bounds (List.finRange q) paid (fun i _ => by
    apply List.mem_iff_getElem.mpr
    exact ⟨i.val, by simp, by simp⟩)
  have high := total_cap (List.finRange q) paid 3 per
  simp only [List.length_finRange] at high
  omega

#print axioms hamming_tree_cut

/-- The list records the terminal population of each component detached by an
actual cut of a child edge. The root component has the separate population `a`. -/
inductive DistancePlan (d : Nat) : Tree Unit → Nat → List Nat → Prop where
  | vacant : DistancePlan d .vacant 0 []
  | terminal : DistancePlan d (.terminal ()) 1 []
  | join (l : DistancePlan d t a xs) (r : DistancePlan d u b ys) (fits : a + b < d) :
      DistancePlan d (.fork t u) (a + b) (xs ++ ys)
  | cutLeft (l : DistancePlan d t a xs) (r : DistancePlan d u b ys) (charge : (d+1)/2 ≤ a) :
      DistancePlan d (.fork t u) b (a :: (xs ++ ys))
  | cutRight (l : DistancePlan d t a xs) (r : DistancePlan d u b ys) (charge : (d+1)/2 ≤ b) :
      DistancePlan d (.fork t u) a (b :: (xs ++ ys))

private theorem piece_sum (xs ys : List Nat) : (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_assoc]

theorem distance_plan_bounds {d a : Nat} {t : Tree Unit} {pieces : List Nat}
    (hd : 2 ≤ d) (plan : DistancePlan d t a pieces) :
    a < d ∧ (∀ k ∈ pieces, (d+1)/2 ≤ k ∧ k < d) ∧ a + pieces.sum = t.mass () := by
  induction plan with
  | vacant => simp [Tree.mass]; omega
  | terminal => simp [Tree.mass]; omega
  | join l r fits il ir =>
    obtain ⟨_,hl,el⟩ := il
    obtain ⟨_,hr,er⟩ := ir
    refine ⟨fits, ?_, by simp only [piece_sum,Tree.mass]; omega⟩
    intro k hk
    exact (List.mem_append.mp hk).elim (hl k) (hr k)
  | cutLeft l r charge il ir =>
    obtain ⟨al,hl,el⟩ := il
    obtain ⟨br,hr,er⟩ := ir
    refine ⟨br, ?_, by simp only [List.sum_cons,piece_sum,Tree.mass]; omega⟩
    intro k hk
    rcases List.mem_cons.mp hk with e | rest
    · subst k; exact ⟨charge,al⟩
    · exact (List.mem_append.mp rest).elim (hl k) (hr k)
  | cutRight l r charge il ir =>
    obtain ⟨al,hl,el⟩ := il
    obtain ⟨br,hr,er⟩ := ir
    refine ⟨al, ?_, by simp only [List.sum_cons,piece_sum,Tree.mass]; omega⟩
    intro k hk
    rcases List.mem_cons.mp hk with e | rest
    · subst k; exact ⟨charge,br⟩
    · exact (List.mem_append.mp rest).elim (hl k) (hr k)

private theorem distance_plan_exists (d : Nat) (t : Tree Unit) :
    ∃ a pieces, DistancePlan d t a pieces := by
  induction t with
  | vacant => exact ⟨_, _, DistancePlan.vacant⟩
  | terminal c => cases c; exact ⟨_, _, DistancePlan.terminal⟩
  | fork t u il ir =>
    obtain ⟨a,xs,l⟩ := il
    obtain ⟨b,ys,r⟩ := ir
    by_cases fits : a + b < d
    · exact ⟨_, _, DistancePlan.join l r fits⟩
    · by_cases full : (d+1)/2 ≤ a
      · exact ⟨_, _, DistancePlan.cutLeft l r full⟩
      · exact ⟨_, _, DistancePlan.cutRight l r (by omega)⟩

/-- Each removed edge detaches between `⌈d/2⌉` and `d−1` terminals. The
root component may be smaller. All terminals are accounted for exactly. -/
theorem single_color_tree_cut (d : Nat) (hd : 2 ≤ d) (t : Tree Unit) :
    ∃ a pieces, DistancePlan d t a pieces ∧ a < d ∧
      (∀ k ∈ pieces, (d+1)/2 ≤ k ∧ k < d) ∧ a + pieces.sum = t.mass () ∧
      (d+1)/2 * pieces.length + a ≤ t.mass () := by
  obtain ⟨a,pieces,plan⟩ := distance_plan_exists d t
  obtain ⟨small,range,mass⟩ := distance_plan_bounds hd plan
  have charge (xs : List Nat) (h : ∀ k ∈ xs, (d+1)/2 ≤ k) : (d+1)/2 * xs.length ≤ xs.sum := by
    induction xs with
    | nil => simp
    | cons k xs ih =>
      have first := h k (by simp)
      have rest := ih (fun i hi => h i (by simp [hi]))
      simp only [List.length_cons,List.sum_cons,Nat.mul_succ]
      omega
  have bound := charge pieces (fun k hk => (range k hk).1)
  exact ⟨a,pieces,plan,small,range,mass,by omega⟩

#print axioms single_color_tree_cut

theorem cycle_budget (blocks cycles paid : Nat) (cost : paid ≤ 3*blocks)
    (codes : 2^(4*blocks) ≤ 2^(cycles+paid)) : blocks ≤ cycles := by
  have e := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp codes
  omega

#print axioms hamming_product_unique
#print axioms hamming_distance
#print axioms cycle_budget
end GluedCodeCut
