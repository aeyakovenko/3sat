import Std

/-! Cardinality of a ternary-XOR-closed cover of independent positive
three-literal clauses, including projection of a common existential witness. -/
namespace FlatCoverCapacity

private theorem subset_length {A : Type} (s t : List A) (nd : s.Nodup)
    (sub : ∀ x ∈ s, x ∈ t) : s.length ≤ t.length := by
  classical
  induction s generalizing t with
  | nil => simp
  | cons x s ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp nd
    have xt := sub x (by simp)
    have pos := List.length_pos_of_mem xt
    have h := ih (t.erase x) tail (by
      intro y hy
      have ne : y ≠ x := fun eq => fresh (eq ▸ hy)
      exact (List.mem_erase_of_ne ne).mpr (sub y (by simp [hy])))
    rw [List.length_erase_of_mem xt] at h
    simp; omega

private theorem concat_bound {A B : Type} (l : List A) (f : A → List B) (k : Nat)
    (sizes : ∀ a ∈ l, (f a).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h := sizes a (by simp)
    have t := ih (fun b hb => sizes b (by simp [hb]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

/-- Ordinary union bound for a finite cover. The outer lists need not be
disjoint or duplicate-free. -/
theorem cover_capacity {A C : Type} (points : List A) (cases : List C)
    (pool : C → List A) (k : Nat) (nd : points.Nodup)
    (cover : ∀ x ∈ points, ∃ i ∈ cases, x ∈ pool i)
    (size : ∀ i ∈ cases, (pool i).length ≤ k) :
    points.length ≤ cases.length * k := by
  exact Nat.le_trans (subset_length points (cases.flatMap pool) nd
    (fun x hx => List.mem_flatMap.mpr (cover x hx))) (concat_bound cases pool k size)

private def pairs (as : List A) (bs : List B) : List (A × B) :=
  as.flatMap (fun a => bs.map (fun b => (a,b)))

private theorem pair_mem (as : List A) (bs : List B) (a : A) (b : B) :
    (a,b) ∈ pairs as bs ↔ a ∈ as ∧ b ∈ bs := by simp [pairs]

private theorem pair_size (as : List A) (bs : List B) :
    (pairs as bs).length = as.length * bs.length := by
  induction as with
  | nil => simp [pairs]
  | cons a as ih =>
    simp only [pairs, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons, Nat.succ_mul] at *
    omega

private theorem pair_distinct (as : List A) (bs : List B) (ha : as.Nodup) (hb : bs.Nodup) :
    (pairs as bs).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a _
    exact List.pairwise_map.mpr (hb.imp (fun h same => h (congrArg Prod.snd same)))
  · apply ha.imp
    intro a b h x hx y hy same
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
    exact h (congrArg Prod.fst same)

abbrev Triple := Bool × Bool × Bool

def zero : Triple := (false, false, false)
def add (x y : Triple) : Triple := (x.1 ^^ y.1, x.2.1 ^^ y.2.1, x.2.2 ^^ y.2.2)
def mix (a b c : Triple) := add (add a b) c

def eight : List Triple :=
  [(false,false,false), (false,false,true), (false,true,false), (false,true,true),
   (true,false,false),  (true,false,true),  (true,true,false),  (true,true,true)]

def seven : List Triple := eight.tail

private theorem all_eight (a : Triple) : a ∈ eight := by
  obtain ⟨p,q,r⟩ := a
  cases p <;> cases q <;> cases r <;> decide

private theorem in_seven (a : Triple) : a ∈ seven ↔ a ≠ zero := by
  obtain ⟨p,q,r⟩ := a
  cases p <;> cases q <;> cases r <;> decide

private theorem cancel_triple (a b : Triple) : mix a b (add a b) = zero := by
  simp [mix, add, zero]

private theorem shift_inj (a b c : Triple) (h : add a b = add a c) : b = c := by
  have back (d : Triple) : add a (add a d) = d := by simp [add]
  exact (back b).symm.trans ((congrArg (add a) h).trans (back c))

/-- In a nonempty ternary-XOR-closed family omitting zero, translate the
family by one of its members: the translate is disjoint and has equal size. -/
theorem one_block (S : Triple → Prop) (avoids : ¬ S zero)
    (closed : ∀ a b c, S a → S b → S c → S (mix a b c)) :
    ∃ l : List Triple, l.length ≤ 4 ∧ ∀ a, a ∈ l ↔ S a := by
  classical
  let l := eight.filter (fun a => decide (S a))
  have exactList : ∀ a, a ∈ l ↔ S a := by intro a; simp [l, all_eight]
  have nd : l.Nodup := List.Pairwise.filter _ (by decide : eight.Nodup)
  refine ⟨l, ?_, exactList⟩
  by_cases nonempty : ∃ a, S a
  · obtain ⟨a,ha⟩ := nonempty
    have dis : (l ++ l.map (add a)).Nodup := by
      apply List.pairwise_append.mpr
      refine ⟨nd, List.pairwise_map.mpr (nd.imp (fun h eq => h (shift_inj a _ _ eq))), ?_⟩
      intro b hb t ht eq
      obtain ⟨c,hc,htc⟩ := List.mem_map.mp ht
      have both : S (add a c) := (htc.trans eq.symm).symm ▸ (exactList b).mp hb
      exact avoids (cancel_triple a c ▸ closed a c _ ha ((exactList c).mp hc) both)
    have bound := subset_length _ eight dis (fun x _ => all_eight x)
    simp only [List.length_append, List.length_map] at bound
    change l.length + l.length ≤ 8 at bound
    omega
  · have empty : l = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun a ha => nonempty ⟨a,(exactList a).mp ha⟩)
    simp [empty]

def Word : Nat → Type
  | 0 => Unit
  | m+1 => Triple × Word m

def ternary : (m : Nat) → Word m → Word m → Word m → Word m
  | 0, _, _, _ => ()
  | m+1, a,b,c => (mix a.1 b.1 c.1, ternary m a.2 b.2 c.2)

def Good : (m : Nat) → Word m → Prop
  | 0, _ => True
  | m+1, x => x.1 ≠ zero ∧ Good m x.2

def goodWords : (m : Nat) → List (Word m)
  | 0 => [()]
  | m+1 => pairs seven (goodWords m)

private theorem good_mem (m : Nat) (x : Word m) : x ∈ goodWords m ↔ Good m x := by
  induction m with
  | zero => cases x; simp [goodWords, Good]
  | succ m ih =>
    rcases x with ⟨a,t⟩
    exact (pair_mem ..).trans (and_congr (in_seven _) (ih t))

private theorem good_size (m : Nat) : (goodWords m).length = 7^m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (pairs seven (goodWords m)).length = _
    rw [pair_size, ih, Nat.pow_succ, Nat.mul_comm (7^m)]
    rfl

private theorem good_distinct (m : Nat) : (goodWords m).Nodup := by
  induction m with
  | zero => exact List.nodup_cons.mpr ⟨by simp, by simp⟩
  | succ m ih => exact pair_distinct _ _ (by decide : seven.Nodup) ih

def Closed (m : Nat) (F : Word m → Prop) : Prop :=
  ∀ a b c, F a → F b → F c → F (ternary m a b c)

/-- Enclose any ternary-XOR-closed subset of the clause relation by a box
of capacity 4^m. Coordinate projections need not be independent in F. -/
theorem flat_capacity (m : Nat) (F : Word m → Prop) (closed : Closed m F)
    (valid : ∀ x, F x → Good m x) :
    ∃ l : List (Word m), l.length ≤ 4^m ∧ ∀ x, F x → x ∈ l := by
  induction m with
  | zero => exact ⟨[()], Nat.le_refl _, fun x _ => by cases x; simp⟩
  | succ m ih =>
    let H (a : Triple) := ∃ t, F (a,t)
    let T (t : Word m) := ∃ a, F (a,t)
    have avoid : ¬H zero := by
      rintro ⟨t,ht⟩
      exact (valid _ ht).1 rfl
    have hClosed : ∀ a b c, H a → H b → H c → H (mix a b c) := by
      rintro a b c ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz⟩
      exact ⟨_, closed (a,x) (b,y) (c,z) hx hy hz⟩
    have tClosed : Closed m T := by
      rintro x y z ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩
      exact ⟨_, closed (a,x) (b,y) (c,z) ha hb hc⟩
    obtain ⟨heads,hSize,hMem⟩ := one_block H avoid hClosed
    obtain ⟨tails,tSize,tMem⟩ := ih T tClosed (by
      rintro t ⟨a,ha⟩
      exact (valid (a,t) ha).2)
    refine ⟨pairs heads tails, ?_, ?_⟩
    · rw [pair_size, Nat.pow_succ, Nat.mul_comm (4^m)]
      exact Nat.mul_le_mul hSize tSize
    · rintro ⟨a,t⟩ h
      exact (pair_mem ..).mpr ⟨(hMem a).mpr ⟨t,h⟩, tMem t ⟨a,h⟩⟩

/-- For an arbitrary index set, any listed family of contained affine flats
covering the entire relation needs at least 7^m / 4^m listed members. -/
theorem flat_cover {I : Type} (m : Nat) (ids : List I) (F : I → Word m → Prop)
    (closed : ∀ i ∈ ids, Closed m (F i))
    (valid : ∀ i ∈ ids, ∀ x, F i x → Good m x)
    (cover : ∀ x, Good m x → ∃ i ∈ ids, F i x) :
    7^m ≤ ids.length * 4^m := by
  classical
  let pool (i : I) := if hi : i ∈ ids then
    (flat_capacity m (F i) (closed i hi) (valid i hi)).choose else []
  have props (i : I) (hi : i ∈ ids) :
      (pool i).length ≤ 4^m ∧ ∀ x, F i x → x ∈ pool i := by
    simpa [pool,hi] using (flat_capacity m (F i) (closed i hi) (valid i hi)).choose_spec
  rw [← good_size]
  apply cover_capacity (goodWords m) ids pool _ (good_distinct m)
  · intro x hx
    obtain ⟨i,hi,h⟩ := cover x ((good_mem m x).mp hx)
    exact ⟨i,hi,(props i hi).2 x h⟩
  · exact fun i hi => (props i hi).1

/-! A family of readers chooses one case per reader, using a single witness.
Projection of an intersection is handled after selecting all the cases. -/

abbrev Case (m : Nat) (H : Type) := Word m → H → Prop

def choices {m : Nat} {H : Type} : List (List (Case m H)) → List (Case m H)
  | [] => [fun _ _ => True]
  | group :: rest => group.flatMap (fun c =>
      (choices rest).map (fun d x w => c x w ∧ d x w))

def factorProduct : List Nat → Nat
  | [] => 1
  | a :: l => a * factorProduct l

private theorem choices_length {m : Nat} {H : Type} (g : List (List (Case m H))) :
    (choices g).length = factorProduct (g.map List.length) := by
  induction g with
  | nil => rfl
  | cons head rest ih =>
    simp only [choices, List.map_cons, factorProduct]
    induction head with
    | nil => simp
    | cons c tail h =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons,
        Nat.succ_mul, ih, h]
      omega

private theorem select_cases {m : Nat} {H : Type} (groups : List (List (Case m H)))
    (x : Word m) (w : H) :
    (∃ f ∈ choices groups, f x w) ↔ ∀ g ∈ groups, ∃ c ∈ g, c x w := by
  induction groups with
  | nil => simp [choices]
  | cons g rest ih =>
    simp only [choices, List.mem_flatMap, List.mem_map, List.forall_mem_cons]
    constructor
    · rintro ⟨f,⟨c,hc,d,hd,rfl⟩,cx,dx⟩
      exact ⟨⟨c,hc,cx⟩, ih.mp ⟨d,hd,dx⟩⟩
    · rintro ⟨⟨c,hc,cx⟩,other⟩
      obtain ⟨d,hd,dx⟩ := ih.mpr other
      exact ⟨_,⟨c,hc,d,hd,rfl⟩,cx,dx⟩

def JointClosed {m : Nat} {H : Type} (join : H → H → H → H) (p : Case m H) :=
  ∀ a b c u v w, p a u → p b v → p c w → p (ternary m a b c) (join u v w)

private theorem choices_closed {m : Nat} {H : Type} (join : H → H → H → H)
    (groups : List (List (Case m H)))
    (laws : ∀ g ∈ groups, ∀ f ∈ g, JointClosed join f) :
    ∀ f ∈ choices groups, JointClosed join f := by
  induction groups with
  | nil => simp [choices, JointClosed]
  | cons g rest ih =>
    intro f hf
    obtain ⟨c,hc,entry⟩ := List.mem_flatMap.mp hf
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp entry
    have left := laws g (by simp) c hc
    have right := ih (fun t ht => laws t (by simp [ht])) d hd
    intro a b z u v w ax bx zx
    exact ⟨left _ _ _ _ _ _ ax.1 bx.1 zx.1, right _ _ _ _ _ _ ax.2 bx.2 zx.2⟩

/-- Each group is one reader's list of accepting cases. The reader count
product is derived; validity and completeness pertain to a common witness.
The upstream derivation of each reader's cases is outside this theorem. -/
theorem common_witness_product {H : Type} (m : Nat) (join : H → H → H → H)
    (groups : List (List (Case m H)))
    (laws : ∀ g ∈ groups, ∀ f ∈ g, JointClosed join f)
    (exact_on_public : ∀ x, Good m x ↔ ∃ w, ∀ g ∈ groups, ∃ c ∈ g, c x w) :
    7^m ≤ factorProduct (groups.map List.length) * 4^m := by
  rw [← choices_length groups]
  apply flat_cover m (choices groups) (fun f x => ∃ w, f x w)
  · intro f hf a b c ha hb hc
    obtain ⟨u,hu⟩ := ha
    obtain ⟨v,hv⟩ := hb
    obtain ⟨w,hw⟩ := hc
    exact ⟨_, choices_closed join groups laws f hf a b c u v w hu hv hw⟩
  · rintro f hf x ⟨w,hw⟩
    exact (exact_on_public x).mpr ⟨w, (select_cases groups x w).mp ⟨f,hf,hw⟩⟩
  · intro x hx
    obtain ⟨w,hw⟩ := (exact_on_public x).mp hx
    obtain ⟨f,hf,holds⟩ := (select_cases groups x w).mpr hw
    exact ⟨f,hf,w,holds⟩

/-- A lower bound applicable to all finite contained-flat covers in m blocks. -/
def Floor (m q : Nat) : Prop :=
  ∀ (I : Type) (ids : List I) (F : I → Word m → Prop),
    (∀ i ∈ ids, Closed m (F i)) →
    (∀ i ∈ ids, ∀ x, F i x → Good m x) →
    (∀ x, Good m x → ∃ i ∈ ids, F i x) → q ≤ ids.length

private theorem scaled_floor {A : Type} (l : List A) (f : A → Nat) (q : Nat)
    (lower : ∀ x ∈ l, q ≤ f x) : l.length * q ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x tail ih =>
    have h := lower x (by simp)
    have t := ih (fun y hy => lower y (by simp [hy]))
    simp only [List.length_cons, Nat.succ_mul, List.map_cons, List.sum_cons]
    omega

private theorem scaled_ceiling {A : Type} (l : List A) (f : A → Nat) (q : Nat)
    (upper : ∀ x ∈ l, f x ≤ q) : (l.map f).sum ≤ l.length * q := by
  induction l with
  | nil => simp
  | cons x tail ih =>
    have h := upper x (by simp)
    have t := ih (fun y hy => upper y (by simp [hy]))
    simp only [List.length_cons, Nat.succ_mul, List.map_cons, List.sum_cons]
    omega

private theorem count_cons {A B : Type} (as : List A) (bs : List B) (p : A → B → Bool) (b : B) :
    (as.map (fun a => ((b :: bs).filter (p a)).length)).sum =
      (as.filter (fun a => p a b)).length + (as.map (fun a => (bs.filter (p a)).length)).sum := by
  induction as with
  | nil => simp
  | cons a ts ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    cases h : p a b <;> simp [List.filter_cons, h] <;> omega

private theorem count_transpose {A B : Type} (as : List A) (bs : List B) (p : A → B → Bool) :
    (as.map (fun a => (bs.filter (p a)).length)).sum =
      (bs.map (fun b => (as.filter (fun a => p a b)).length)).sum := by
  induction bs with
  | nil => induction as <;> simp_all
  | cons b t ih => rw [count_cons, ih]; rfl

private theorem mix_same (a : Triple) : mix a a a = a := by simp [mix, add]

/-- For each of the seven first-block values, the nonempty slices give a
cover on m blocks. Any one flat appears in at most four of those seven
covers. The ceiling form keeps the integral improvement at each step. -/
theorem floor_successor {m q : Nat} (base : Floor m q) :
    Floor (m+1) ((7*q + 3)/4) := by
  classical
  intro I ids F closed valid cover
  let hit (a : Triple) (i : I) : Bool := decide (∃ t, F i (a,t))
  let subset (a : Triple) := ids.filter (hit a)
  have floorAt (a : Triple) (ha : a ∈ seven) : q ≤ (subset a).length := by
    apply base I (subset a) (fun i t => F i (a,t))
    · intro i hi x y z hx hy hz
      have law := closed i (List.mem_filter.mp hi).1 (a,x) (a,y) (a,z) hx hy hz
      simpa only [ternary, mix_same] using law
    · intro i hi t ht
      exact (valid i (List.mem_filter.mp hi).1 (a,t) ht).2
    · intro t ht
      obtain ⟨i,hi,sat⟩ := cover (a,t) ⟨(in_seven a).mp ha,ht⟩
      exact ⟨i,List.mem_filter.mpr ⟨hi,by simp [hit]; exact ⟨t,sat⟩⟩,sat⟩
  have atMost (i : I) (hi : i ∈ ids) :
      (seven.filter (fun a => hit a i)).length ≤ 4 := by
    let S (a : Triple) := ∃ t, F i (a,t)
    have outside : ¬ S zero := by
      rintro ⟨t,ht⟩
      exact (valid i hi (zero,t) ht).1 rfl
    obtain ⟨l,lim,exactList⟩ := one_block S outside (by
      rintro a b c ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz⟩
      exact ⟨_, closed i hi (a,x) (b,y) (c,z) hx hy hz⟩)
    apply Nat.le_trans _ lim
    apply subset_length _ _ (List.Pairwise.filter _ (by decide : seven.Nodup))
    intro a mem
    exact (exactList a).mpr (of_decide_eq_true (List.mem_filter.mp mem).2)
  have low := scaled_floor seven (fun a => (subset a).length) q floorAt
  change 7*q ≤ (seven.map (fun a => (ids.filter (hit a)).length)).sum at low
  rw [count_transpose] at low
  have high := scaled_ceiling ids (fun i => (seven.filter (fun a => hit a i)).length) 4 atMost
  omega

/-! Exact one- and two-block optima. The seven nonzero triples form the
Fano plane, which has no coloring with two colors avoiding monochrome lines. -/

private def bits (n : Nat) : Triple := (n.testBit 0, n.testBit 1, n.testBit 2)

private def coloring (c0 c1 c2 c3 c4 c5 c6 c7 : Bool) : Triple → Bool
  | (false,false,false) => c0
  | (true, false,false) => c1
  | (false,true, false) => c2
  | (true, true, false) => c3
  | (false,false,true)  => c4
  | (true, false,true)  => c5
  | (false,true, true)  => c6
  | (true, true, true)  => c7

private def lines : List (Triple × Triple × Triple) :=
  [(bits 1,bits 2,bits 3), (bits 1,bits 4,bits 5), (bits 1,bits 6,bits 7),
   (bits 2,bits 4,bits 6), (bits 2,bits 5,bits 7), (bits 3,bits 4,bits 7),
   (bits 3,bits 5,bits 6)]

private def mono (p : Triple → Bool) (l : Triple × Triple × Triple) :=
  (p l.1 == p l.2.1) && (p l.1 == p l.2.2)

private theorem fano (p : Triple → Bool) :
    ∃ a b c, a ≠ zero ∧ b ≠ zero ∧ c ≠ zero ∧ mix a b c = zero ∧
      p a = p b ∧ p a = p c := by
  have table : ∀ c0 c1 c2 c3 c4 c5 c6 c7 : Bool,
      lines.any (mono (coloring c0 c1 c2 c3 c4 c5 c6 c7)) = true := by decide
  have line := table (p (bits 0)) (p (bits 1)) (p (bits 2)) (p (bits 3))
    (p (bits 4)) (p (bits 5)) (p (bits 6)) (p (bits 7))
  have agrees : coloring (p (bits 0)) (p (bits 1)) (p (bits 2)) (p (bits 3))
      (p (bits 4)) (p (bits 5)) (p (bits 6)) (p (bits 7)) = p := by
    funext v; rcases v with ⟨x,y,z⟩
    cases x <;> cases y <;> cases z <;> rfl
  rw [agrees] at line
  obtain ⟨l,hl,h⟩ := List.any_eq_true.mp line
  have geometry : ∀ t ∈ lines, t.1 ≠ zero ∧ t.2.1 ≠ zero ∧ t.2.2 ≠ zero ∧
      mix t.1 t.2.1 t.2.2 = zero := by
    simp only [lines, List.mem_cons, List.not_mem_nil, or_false]
    intro t ht
    rcases ht with h|h|h|h|h|h|h <;> subst t <;> decide
  obtain ⟨ha,hb,hc,eq⟩ := geometry l hl
  exact ⟨_,_,_,ha,hb,hc,eq,by simpa [mono] using h⟩

private theorem no_two (P Q : Word 1 → Prop) (cp : Closed 1 P) (cq : Closed 1 Q)
    (vp : ∀ x, P x → Good 1 x) (vq : ∀ x, Q x → Good 1 x)
    (cover : ∀ x, Good 1 x → P x ∨ Q x) : False := by
  classical
  obtain ⟨a,b,c,ha,hb,hc,zeroSum,sameB,sameC⟩ := fano (fun u => decide (P (u,())))
  by_cases col : P (a,())
  · simp [col] at sameB sameC
    have hz := cp _ _ _ col sameB sameC
    exact (vp _ hz).1 zeroSum
  · simp [col] at sameB sameC
    have extract (u : Triple) (hu : u ≠ zero) (miss : ¬P (u,())) : Q (u,()) :=
      (cover _ ⟨hu, trivial⟩).resolve_left miss
    have hz := cq _ _ _ (extract a ha col) (extract b hb sameB) (extract c hc sameC)
    exact (vq _ hz).1 zeroSum

/-- Fano's two-color obstruction rules out covers by only two affine flats. -/
theorem one_block_floor : Floor 1 3 := by
  intro I ids F closed valid cover
  cases ids with
  | nil =>
    have h := cover (bits 1, ()) ⟨by decide, trivial⟩
    simp at h
  | cons i tail =>
    cases tail with
    | nil =>
      apply False.elim
      apply no_two (F i) (F i) (closed i (by simp)) (closed i (by simp))
        (valid i (by simp)) (valid i (by simp))
      intro x hx
      simpa only [List.mem_singleton, exists_eq_left, or_self] using cover x hx
    | cons j tail =>
      cases tail with
      | cons a t => simp
      | nil =>
        apply False.elim
        apply no_two (F i) (F j) (closed i (by simp)) (closed j (by simp))
          (valid i (by simp)) (valid j (by simp))
        intro x hx
        obtain ⟨k,hk,good⟩ := cover x hx
        rcases List.mem_cons.mp hk with h | h
        · exact Or.inl (h ▸ good)
        · exact Or.inr ((List.mem_singleton.mp h) ▸ good)

/-- The integral successor step gives six in two blocks. -/
theorem two_block_floor : Floor 2 6 := floor_successor one_block_floor

def dot (a x : Triple) : Bool :=
  (a.1 && x.1) ^^ (a.2.1 && x.2.1) ^^ (a.2.2 && x.2.2)

private theorem dot_mix (a x y z : Triple) :
    dot a (mix x y z) = ((dot a x ^^ dot a y) ^^ dot a z) := by
  rcases a with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> simp [dot,mix,add] <;> bv_decide

private def orth (a x : Triple) := dot a x = true

private theorem orth_good {a x : Triple} (h : orth a x) : x ≠ zero := by
  intro eq
  simp [orth,eq,zero,dot] at h

private theorem orth_mixes (a x y z : Triple) (h₁ : orth a x) (h₂ : orth a y) (h₃ : orth a z) :
    orth a (mix x y z) := by
  change dot a (mix x y z) = true
  rw [dot_mix, h₁, h₂, h₃]
  decide

def HasCover (m k : Nat) : Prop :=
  ∃ (ids : List Triple) (F : Triple → Word m → Prop), ids.length = k ∧
    (∀ i ∈ ids, Closed m (F i)) ∧ (∀ i ∈ ids, ∀ x, F i x → Good m x) ∧
    ∀ x, Good m x → ∃ i ∈ ids, F i x

/-- Three coordinate planes attain the lower bound in one block. -/
theorem three_planes_cover : HasCover 1 3 := by
  refine ⟨[bits 1,bits 2,bits 4], fun a x => orth a x.1, rfl, ?_, ?_, ?_⟩
  · intro a _ x y z hx hy hz; exact orth_mixes _ _ _ _ hx hy hz
  · intro a _ x hx; exact ⟨orth_good hx, trivial⟩
  · rintro ⟨⟨x,y,z⟩,u⟩ h
    have test : bits 1 ∈ [bits 1,bits 2,bits 4] := by simp
    cases x <;> cases y <;> cases z <;> first
      | exact False.elim (h.1 rfl)
      | exact ⟨bits 1, test, rfl⟩
      | exact ⟨bits 2, by simp, rfl⟩
      | exact ⟨bits 4, by simp, rfl⟩

/-- Six product planes, one per common normal other than 000 and 111. -/
theorem six_product_planes_cover : HasCover 2 6 := by
  let ids := [bits 1,bits 2,bits 3,bits 4,bits 5,bits 6]
  refine ⟨ids, fun a x => orth a x.1 ∧ orth a x.2.1, rfl, ?_, ?_, ?_⟩
  · intro a _ x y z hx hy hz
    exact ⟨orth_mixes _ _ _ _ hx.1 hy.1 hz.1, orth_mixes _ _ _ _ hx.2 hy.2 hz.2⟩
  · intro a _ x hx; exact ⟨orth_good hx.1, orth_good hx.2, trivial⟩
  · rintro ⟨⟨a,b,c⟩,⟨d,e,f⟩,u⟩ h
    have each : ∀ a b c d e f : Bool,
        (a || b || c) && (d || e || f) = true →
        ids.any (fun t => dot t (a,b,c) && dot t (d,e,f)) = true := by decide
    have live : (a || b || c) && (d || e || f) = true := by
      have first := h.1
      have second := h.2.1
      cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
        first | rfl | exact False.elim (first rfl) | exact False.elim (second rfl)
    obtain ⟨i,hi,win⟩ := List.any_eq_true.mp (each a b c d e f live)
    exact ⟨i,hi,by simpa [orth] using win⟩

end FlatCoverCapacity
