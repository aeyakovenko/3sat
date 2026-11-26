import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Tauto
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-! A binary vector is its set of nonzero coordinates. Ternary symmetric difference
is the affine operation (x,y,z) ↦ x+y+z over the field with two elements. -/

namespace AffineWeightFlats
open Finset
open scoped symmDiff

abbrev Word := Finset Nat
abbrev Family := Finset Word

def Flat (W : Family) := ∀ x ∈ W, ∀ y ∈ W, ∀ z ∈ W, (x ∆ y) ∆ z ∈ W

def Opp (i j : Nat) (x : Word) := (i ∈ x ↔ j ∉ x)

instance (i j : Nat) : DecidablePred (Opp i j) := fun x => by unfold Opp; infer_instance

def Cross (W : Family) (i j : Nat) :=
  (∃ x ∈ W, Opp i j x) ∧ (∃ y ∈ W, ¬ Opp i j y)

def Stable (W : Family) (i j : Nat) := ∀ x ∈ W, x ∆ {i,j} ∈ W

def Avoids (W : Family) (r : Nat) := ∀ x ∈ W, x.card % 3 ≠ r

private theorem flipTwice (x a : Word) : (x ∆ a) ∆ a = x := by
  ext j
  simp only [mem_symmDiff]
  tauto

private theorem xorCancel (x y a : Word) (h : x ∆ a = y ∆ a) : x = y := by
  simpa only [flipTwice] using congrArg (fun z : Word => z ∆ a) h

private theorem translated (W : Family) (h : Flat W) {x p q : Word}
    (hx : x ∈ W) (hp : p ∈ W) (hq : q ∈ W) : x ∆ (p ∆ q) ∈ W := by
  rw [← symmDiff_assoc]; exact h x hx p hp q hq

private theorem oppositeChanges (i j : Nat) (x p q : Word)
    (hp : Opp i j p) (hq : ¬ Opp i j q) :
    Opp i j (x ∆ (p ∆ q)) ↔ ¬ Opp i j x := by
  unfold Opp at *
  simp only [mem_symmDiff]
  tauto

private theorem equalSlices (W : Family) (h : Flat W) (i j : Nat) (hc : Cross W i j) :
    W.card = 2 * (W.filter (Opp i j)).card := by
  classical
  obtain ⟨⟨p,hp,op⟩,⟨q,hq,oq⟩⟩ := hc
  let a := p ∆ q
  have switch (x : Word) : Opp i j (x ∆ a) ↔ ¬ Opp i j x :=
    oppositeChanges i j x p q op oq
  have stay (x : Word) (hx : x ∈ W) : x ∆ a ∈ W := translated W h hx hp hq
  have sz : (W.filter (fun x => ¬ Opp i j x)).card = (W.filter (Opp i j)).card := by
    apply Finset.card_bij (fun x _ => x ∆ a)
    · intro x hx
      obtain ⟨hw,ho⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨stay x hw,(switch x).mpr ho⟩
    · intro x _ y _ eq; exact xorCancel _ _ _ eq
    · intro x hx
      obtain ⟨hw,ho⟩ := mem_filter.mp hx
      exact ⟨x ∆ a, mem_filter.mpr ⟨stay x hw,fun hh => (switch x).mp hh ho⟩, flipTwice _ _⟩
  have tot : (W.filter (Opp i j)).card + (W.filter (fun x => ¬ Opp i j x)).card = W.card := by
    exact card_filter_add_card_filter_not (Opp i j)
  omega

private theorem togglePair (W : Family) (hf : Flat W) {x y : Word} (hx : x ∈ W)
    (hy : y ∈ W) {i j : Nat} (delta : x ∆ y = {i,j}) : Stable W i j := by
  intro z hz
  rw [← delta]
  exact translated W hf hz hx hy

private theorem projInj (W : Family) (hf : Flat W) (i j : Nat) (ij : i ≠ j)
    (ns : ¬ Stable W i j) :
    Set.InjOn (fun x : Word => x \ {i,j}) ↑(W.filter (Opp i j)) := by
  classical
  intro x hx y hy eq
  obtain ⟨hx,ox⟩ := mem_filter.mp hx
  obtain ⟨hy,oy⟩ := mem_filter.mp hy
  have outer (k : Nat) (ki : k ≠ i) (kj : k ≠ j) : k ∈ x ↔ k ∈ y := by
    have h := Finset.ext_iff.mp eq k
    simpa only [mem_sdiff, mem_insert, mem_singleton, ki,kj,false_or,not_false_eq_true,and_true] using h
  by_cases hi : (i ∈ x ↔ i ∈ y)
  · ext k
    by_cases ki : k = i
    · simpa [ki] using hi
    by_cases kj : k = j
    · subst k; unfold Opp at ox oy; tauto
    exact outer k ki kj
  · exfalso
    apply ns (togglePair W hf hx hy ?_)
    ext k
    simp only [mem_symmDiff,mem_insert,mem_singleton]
    unfold Opp at ox oy
    by_cases ki : k = i
    · subst k; tauto
    by_cases kj : k = j
    · subst k; tauto
    have hk := outer k ki kj
    tauto

private theorem projectedFlat (W : Family) (hf : Flat W) (i j : Nat) :
    Flat ((W.filter (Opp i j)).image (fun x => x \ {i,j})) := by
  classical
  intro xx hx yy hy zz hz
  obtain ⟨x,fx,rfl⟩ := mem_image.mp hx
  obtain ⟨y,fy,rfl⟩ := mem_image.mp hy
  obtain ⟨z,fz,rfl⟩ := mem_image.mp hz
  obtain ⟨hx,ox⟩ := mem_filter.mp fx
  obtain ⟨hy,oy⟩ := mem_filter.mp fy
  obtain ⟨hz,oz⟩ := mem_filter.mp fz
  apply mem_image.mpr
  refine ⟨(x ∆ y) ∆ z,mem_filter.mpr ⟨hf _ hx _ hy _ hz,?_⟩,?_⟩
  · unfold Opp at *
    simp only [mem_symmDiff]
    tauto
  · ext k
    by_cases hk : k ∈ ({i,j} : Word) <;> simp [mem_symmDiff,mem_sdiff,hk]


private theorem opp_constant (W : Family) {i j : Nat} (hn : ¬Cross W i j)
    {x y : Word} (hx : x ∈ W) (hy : y ∈ W) : Opp i j x ↔ Opp i j y := by
  constructor
  · intro a; by_contra b; exact hn ⟨⟨x,hx,a⟩,⟨y,hy,b⟩⟩
  · intro b; by_contra a; exact hn ⟨⟨y,hy,b⟩,⟨x,hx,a⟩⟩

private theorem nc_sym (W : Family) (i j : Nat) : ¬Cross W i j → ¬Cross W j i := by
  intro nc ⟨⟨x,hx,ox⟩,⟨y,hy,oy⟩⟩
  have eq := opp_constant W nc hx hy
  unfold Opp at *
  tauto

private theorem nc_trans (W : Family) (i j k : Nat) :
    ¬Cross W i j → ¬Cross W j k → ¬Cross W i k := by
  intro a b ⟨⟨x,hx,ox⟩,⟨y,hy,oy⟩⟩
  have eq1 := opp_constant W a hx hy
  have eq2 := opp_constant W b hx hy
  unfold Opp at *
  tauto

private theorem cross_ne (W : Family) {i j : Nat} (hc : Cross W i j) : i ≠ j := by
  rintro rfl
  obtain ⟨⟨x,_,ox⟩,_⟩ := hc
  unfold Opp at ox; tauto

private theorem stable_path (W : Family) {i j k : Nat} (ij : i ≠ j) (ik : i ≠ k)
    (jk : j ≠ k) (sik : Stable W i k) (sjk : Stable W j k) : Stable W i j := by
  intro x hx
  have eq : ({i,k} : Word) ∆ {j,k} = {i,j} := by
    ext t
    simp only [mem_symmDiff,mem_insert,mem_singleton]
    by_cases ti : t=i <;> by_cases tj : t=j <;> by_cases tk : t=k <;> grind
  rw [←eq,←symmDiff_assoc]
  exact sjk _ (sik _ hx)

private theorem allStable (W : Family) (G : Word)
    (someCross : ∃ i ∈ G, ∃ j ∈ G, Cross W i j)
    (good : ∀ i ∈ G, ∀ j ∈ G, Cross W i j → Stable W i j) :
    ∀ i ∈ G, ∀ j ∈ G, i ≠ j → Stable W i j := by
  obtain ⟨a,ha,b,hb,cab⟩ := someCross
  intro i hi j hj ij
  by_cases cij : Cross W i j
  · exact good _ hi _ hj cij
  have aux : ∃ k ∈ G, Cross W i k := by
    by_cases cia : Cross W i a
    · exact ⟨a,ha,cia⟩
    refine ⟨b,hb,?_⟩
    by_contra cib
    exact (nc_trans W a i b (nc_sym W i a cia) cib) cab
  obtain ⟨k,hk,cik⟩ := aux
  have cjk : Cross W j k := by
    by_contra nc
    exact (nc_trans W i j k cij nc) cik
  exact stable_path W ij (cross_ne W cik) (cross_ne W cjk)
    (good _ hi _ hk cik) (good _ hj _ hk cjk)

private theorem noCrossSmall (W : Family) (G : Word) (g : G.Nonempty)
    (support : ∀ x ∈ W, x ⊆ G) (nc : ∀ i ∈ G, ∀ j ∈ G, ¬Cross W i j) : W.card ≤ 2 := by
  classical
  obtain ⟨i,hi⟩ := g
  have bound : W.card ≤ (univ : Finset Bool).card := by
    apply card_le_card_of_injOn (fun x : Word => decide (i ∈ x))
    · intro _ _; exact mem_univ _
    · intro x hx y hy eq
      have ix : i ∈ x ↔ i ∈ y := by simpa only [decide_eq_decide] using eq
      ext j
      by_cases hj : j ∈ G
      · have u := opp_constant W (nc i hi j hj) hx hy
        unfold Opp at u; tauto
      · have xj : j ∉ x := fun h => hj (support _ hx h)
        have yj : j ∉ y := fun h => hj (support _ hy h)
        tauto
  simpa only [Finset.card_univ, Fintype.card_bool] using bound

private theorem grow (G : Word) (W : Family) (mov : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → Stable W i j)
    {x : Word} (hx : x ∈ W) (room : 2 ≤ (G \ x).card) :
    ∃ y ∈ W, y.card = x.card + 2 := by
  obtain ⟨t,ht,sz⟩ := exists_subset_card_eq room
  obtain ⟨i,j,ij,rfl⟩ := card_eq_two.mp sz
  have hi := mem_sdiff.mp (ht (show i ∈ ({i,j} : Word) by simp))
  have hj := mem_sdiff.mp (ht (show j ∈ ({i,j} : Word) by simp))
  refine ⟨x ∆ {i,j},mov i hi.1 j hj.1 ij x hx,?_⟩
  have dj : Disjoint x ({i,j} : Word) := by
    rw [Finset.disjoint_left]
    intro k h hk; simp only [mem_insert,mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hi.2 h
    · exact hj.2 h
  rw [Finset.symmDiff_eq_union dj,card_union_of_disjoint dj,card_pair ij]

private theorem shrink (G : Word) (W : Family)
    (mov : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → Stable W i j)
    {x : Word} (hx : x ∈ W) (sub : x ⊆ G) (room : 2 ≤ x.card) :
    ∃ y ∈ W, y.card + 2 = x.card := by
  obtain ⟨t,ht,sz⟩ := exists_subset_card_eq room
  obtain ⟨i,j,ij,rfl⟩ := card_eq_two.mp sz
  have hi := ht (show i ∈ ({i,j} : Word) by simp)
  have hj := ht (show j ∈ ({i,j} : Word) by simp)
  refine ⟨x ∆ {i,j},mov i (sub hi) j (sub hj) ij x hx,?_⟩
  have eq : x ∆ {i,j} = x \ {i,j} := by
    ext k
    have hs := @ht k
    simp only [mem_symmDiff, mem_sdiff]
    tauto
  rw [eq,card_sdiff_of_subset ht,card_pair ij]
  omega

private theorem stableHits (G : Word) (W : Family) (hn : 5 ≤ G.card) (ne : W.Nonempty)
    (support : ∀ x ∈ W, x ⊆ G) (mov : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → Stable W i j)
    (r : Nat) (hr : r < 3) : ¬Avoids W r := by
  intro avoid
  obtain ⟨x,hx⟩ := ne
  have h0 := avoid x hx
  have sx := card_sdiff_of_subset (support x hx)
  have cx := card_le_card (support x hx)
  by_cases hu : 4 ≤ G.card - x.card
  · obtain ⟨y,hy,yc⟩ := grow G W mov hx (by omega)
    have sy := card_sdiff_of_subset (support y hy)
    obtain ⟨z,hz,zc⟩ := grow G W mov hy (by omega)
    have h1 := avoid y hy; have h2 := avoid z hz
    omega
  by_cases hd : 4 ≤ x.card
  · obtain ⟨y,hy,yc⟩ := shrink G W mov hx (support x hx) (by omega)
    obtain ⟨z,hz,zc⟩ := shrink G W mov hy (support y hy) (by omega)
    have h1 := avoid y hy; have h2 := avoid z hz
    omega
  obtain ⟨y,hy,yc⟩ := grow G W mov hx (by omega)
  obtain ⟨z,hz,zc⟩ := shrink G W mov hx (support x hx) (by omega)
  have h1 := avoid y hy; have h2 := avoid z hz
  omega


private theorem shiftWeight (i j : Nat) (x : Word) (ox : Opp i j x) :
    (x \ {i,j}).card + 1 = x.card := by
  have h := card_sdiff_add_card_inter x ({i,j} : Word)
  have hi : (x ∩ {i,j}).card = 1 := by
    by_cases ix : i ∈ x
    · have jx := ox.mp ix
      have eq : x ∩ {i,j} = {i} := by
        ext k; simp only [mem_inter,mem_insert,mem_singleton]
        constructor
        · rintro ⟨hk,hk' | rfl⟩
          · exact hk'
          · contradiction
        · rintro rfl; exact ⟨ix,Or.inl rfl⟩
      simp [eq]
    · have jx : j ∈ x := by unfold Opp at ox; tauto
      have eq : x ∩ {i,j} = {j} := by
        ext k; simp only [mem_inter,mem_insert,mem_singleton]
        constructor
        · rintro ⟨hk,rfl | hk'⟩
          · contradiction
          · exact hk'
        · rintro rfl; exact ⟨jx,Or.inr rfl⟩
      simp [eq]
  omega

private theorem hasHalf (G : Word) (W : Family) (ne : W.Nonempty) (hf : Flat W)
    (sub : ∀ x ∈ W, x ⊆ G) {y : Word} (sy : y ⊆ G) (ny : y ∉ W) :
    2*W.card ≤ 2^G.card := by
  classical
  obtain ⟨a,ha⟩ := ne
  have subW : W ⊆ G.powerset := fun x hx => mem_powerset.mpr (sub x hx)
  have ineq : W.card ≤ (G.powerset \ W).card := by
    apply card_le_card_of_injOn (fun x => x ∆ (a ∆ y))
    · intro x hx
      apply mem_sdiff.mpr
      constructor
      · apply mem_powerset.mpr
        intro k hk
        obtain hk | hk := mem_symmDiff.mp hk
        · exact sub _ hx hk.1
        · obtain hh | hh := mem_symmDiff.mp hk.1
          · exact sub _ ha hh.1
          · exact sy hh.1
      · intro hh
        apply ny
        have hw := hf a ha x hx _ hh
        have eq : (a ∆ x) ∆ (x ∆ (a ∆ y)) = y := by
          ext k; by_cases ka : k ∈ a <;> by_cases kx : k ∈ x <;> simp [mem_symmDiff,ka,kx]
        rwa [eq] at hw
    · intro x _ z _ eq; exact xorCancel _ _ _ eq
  rw [card_sdiff_of_subset subW, card_powerset] at ineq
  have ss := card_le_card subW
  rw [card_powerset] at ss
  omega

/-- Cardinal form of the extremal bound for affine flats over the binary field.
The coordinates may be any finite set of natural names. -/
theorem card_bound (G : Word) (W : Family) (hf : Flat W)
    (sub : ∀ x ∈ W, x ⊆ G) (r : Nat) (hr : r < 3) (ha : Avoids W r) :
    W.card ≤ 2^(G.card/2+1) := by
  classical
  generalize he : G.card = m
  induction m using Nat.strong_induction_on generalizing G W r with
  | h m ih =>
    by_cases small : m ≤ 4
    · have subW : W ⊆ G.powerset := fun x hx => mem_powerset.mpr (sub x hx)
      have card := card_le_card subW
      rw [card_powerset,he] at card
      by_cases tiny : m ≤ 2
      · rcases (show m=0 ∨ m=1 ∨ m=2 by omega) with eq|eq|eq <;> rw [eq] at card ⊢ <;> omega
      by_cases empty : W = ∅
      · simp [empty]
      have ne := nonempty_iff_ne_empty.mpr empty
      obtain ⟨y,hy,yc⟩ := exists_subset_card_eq (show r ≤ G.card by omega)
      have ny : y ∉ W := by
        intro h
        exact ha _ h (by rw [yc,Nat.mod_eq_of_lt hr])
      have half := hasHalf G W ne hf sub hy ny
      rw [he] at half
      rcases (show m=3 ∨ m=4 by omega) with eq|eq <;> rw [eq] at half ⊢ <;> omega
    by_cases cut : ∃ i ∈ G, ∃ j ∈ G, Cross W i j ∧ ¬Stable W i j
    · obtain ⟨i,hi,j,hj,hc,ns⟩ := cut
      have ij := cross_ne W hc
      let t : Word := {i,j}
      let A : Family := (W.filter (Opp i j)).image (fun x => x \ t)
      have tG : t ⊆ G := by
        intro k hk; rcases (show k = i ∨ k = j by simpa [t] using hk) with rfl|rfl
        · exact hi
        · exact hj
      have gt : (G \ t).card = m-2 := by rw [card_sdiff_of_subset tG,show t.card=2 from card_pair ij,he]
      have smallA : A.card ≤ 2^((m-2)/2+1) := by
        refine ih (m-2) (by omega) (G \ t) A (projectedFlat W hf i j) ?_ ((r+2)%3) ?_ ?_ gt
        · intro z hz
          obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
          exact sdiff_subset_sdiff_left t (sub _ (mem_filter.mp hx).1)
        · show (r+2)%3 < 3; omega
        · intro z hz
          obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
          obtain ⟨wx,ox⟩ := mem_filter.mp hx
          have sh := shiftWeight i j x ox
          have avoid := ha x wx
          dsimp [t]
          omega
      have sz : A.card = (W.filter (Opp i j)).card := card_image_iff.mpr (projInj W hf i j ij ns)
      have full := equalSlices W hf i j hc
      have step : m/2+1 = ((m-2)/2+1)+1 := by omega
      rw [step, Nat.pow_succ]
      omega
    · by_cases cross : ∃ i ∈ G, ∃ j ∈ G, Cross W i j
      · have good : ∀ i ∈ G, ∀ j ∈ G, Cross W i j → Stable W i j := by
          intro i hi j hj hc; by_contra ns; exact cut ⟨i,hi,j,hj,hc,ns⟩
        by_cases em : W = ∅
        · simp [em]
        exact False.elim ((stableHits G W (by omega) (nonempty_iff_ne_empty.mpr em)
          sub (allStable W G cross good) r hr) ha)
      · have nc : ∀ i ∈ G, ∀ j ∈ G, ¬Cross W i j := by
          intro i hi j hj hc; exact cross ⟨i,hi,j,hj,hc⟩
        have smallW := noCrossSmall W G (card_pos.mp (by omega)) sub nc
        have two : 1 ≤ 2^(m/2) := Nat.one_le_pow _ _ (by decide)
        rw [Nat.pow_succ]
        omega



/-- An injectively parametrized d-dimensional binary affine flat of length m
that avoids some Hamming-weight residue modulo 3 has d ≤ floor(m/2)+1.
Vectors are represented by the positions of their ones. Preserving ternary
addition is the translation-invariant definition of an affine map over F₂. -/
theorem dimension_bound {m d : Nat} (f : (Fin d → Bool) → Word)
    (inj : Function.Injective f) (support : ∀ a, f a ⊆ range m)
    (affine : ∀ a b c, f (fun i => (a i ^^ b i) ^^ c i) = (f a ∆ f b) ∆ f c)
    (r : Nat) (hr : r < 3) (avoid : ∀ a, (f a).card % 3 ≠ r) :
    d ≤ m/2+1 := by
  classical
  let W : Family := univ.image f
  have hf : Flat W := by
    intro x hx y hy z hz
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    obtain ⟨b,_,rfl⟩ := mem_image.mp hy
    obtain ⟨c,_,rfl⟩ := mem_image.mp hz
    exact mem_image.mpr ⟨_,mem_univ _,affine a b c⟩
  have ss : ∀ x ∈ W, x ⊆ range m := by
    intro x hx; obtain ⟨a,_,rfl⟩ := mem_image.mp hx; exact support a
  have aa : Avoids W r := by
    intro x hx; obtain ⟨a,_,rfl⟩ := mem_image.mp hx; exact avoid a
  have bd := card_bound (range m) W hf ss r hr aa
  have sz : W.card = 2^d := by
    simp only [W,card_image_of_injective _ inj,card_univ,Fintype.card_fun,
      Fintype.card_fin,Fintype.card_bool]
  rw [sz,card_range] at bd
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp bd

end AffineWeightFlats
