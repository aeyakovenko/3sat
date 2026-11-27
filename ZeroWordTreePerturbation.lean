import Std

namespace ZeroWordTreePerturbation

/-- A partial solution records its boundary word and whether an internal input changed. -/
abbrev Rel := Nat → Bool → Prop

def bit (B : Nat) (v : Bool) : Nat := if v then B else 0

def Corner (B : Nat) (f : Nat → Nat → Nat) : Prop :=
  ∃ a b : Bool, (a || b) = true ∧
    (f (bit B a) (bit B b) = f 0 0 ∨ (f 0 0 = 0 ∧ f (bit B a) (bit B b) = B))

structure Supply (B x : Nat) (r : Rel) : Prop where
  base : r x false
  alternative : r x true ∨ (x = 0 ∧ r B true)

structure Demand (B x : Nat) (r : Rel) : Prop where
  base : r x false
  alternative : x = 0 → r x true ∨ ∃ b, r B b

def joined (p q : Rel) : Rel := fun x changed =>
  ∃ a b, p x a ∧ q x b ∧ (a || b) = changed

theorem fresh (B : Nat) : Supply B 0 (fun x b => x = bit B b) :=
  ⟨rfl, Or.inr ⟨rfl, by simp [bit]⟩⟩

theorem emptyDemand (B x : Nat) : Demand B x (fun _ b => b=false) :=
  ⟨rfl, fun _ => Or.inr ⟨false,rfl⟩⟩

theorem nonzeroPin (B x : Nat) (h : x ≠ 0) :
    Demand B x (fun y changed => y=x ∧ changed=false) :=
  ⟨⟨rfl,rfl⟩, fun e => (h e).elim⟩

theorem combineDemand {B x : Nat} {p q : Rel} (hp : Demand B x p) (hq : Demand B x q) :
    Demand B x (joined p q) := by
  refine ⟨⟨false,false,hp.base,hq.base,rfl⟩, ?_⟩
  intro hx
  rcases hp.alternative hx with e | ⟨a,e⟩
  · exact Or.inl ⟨true,false,e,hq.base,rfl⟩
  rcases hq.alternative hx with t | ⟨b,t⟩
  · exact Or.inl ⟨false,true,hp.base,t,rfl⟩
  · exact Or.inr ⟨a || b,a,b,e,t,rfl⟩

theorem attach {B x : Nat} {p q : Rel} (hp : Supply B x p) (hq : Demand B x q) :
    Supply B x (joined p q) := by
  refine ⟨⟨false,false,hp.base,hq.base,rfl⟩, ?_⟩
  rcases hp.alternative with e | ⟨hx,e⟩
  · exact Or.inl ⟨true,false,e,hq.base,rfl⟩
  rcases hq.alternative hx with t | ⟨b,t⟩
  · exact Or.inl ⟨false,true,hp.base,t,rfl⟩
  · exact Or.inr ⟨hx,true,b,e,t,rfl⟩

def produce (f : Nat → Nat → Nat) (p q : Rel) : Rel := fun z c =>
  ∃ x y a b, p x a ∧ q y b ∧ f x y = z ∧ (a || b) = c

private theorem supplyBit {B : Nat} {p : Rel} (zero : p 0 false) (one : p B true) :
    ∀ a, p (bit B a) a := by intro a; cases a <;> simp_all [bit]

theorem produceGood {B x y : Nat} {p q : Rel} {f : Nat → Nat → Nat}
    (hf : Corner B f) (hp : Supply B x p) (hq : Supply B y q) :
    Supply B (f x y) (produce f p q) := by
  refine ⟨⟨x,y,false,false,hp.base,hq.base,rfl,rfl⟩, ?_⟩
  rcases hp.alternative with e | ⟨rfl,e⟩
  · exact Or.inl ⟨x,y,true,false,e,hq.base,rfl,rfl⟩
  rcases hq.alternative with t | ⟨rfl,t⟩
  · exact Or.inl ⟨0,y,false,true,hp.base,t,rfl,rfl⟩
  rcases hf with ⟨a,b,change,cases⟩
  rcases cases with same | ⟨hz,other⟩
  · exact Or.inl ⟨_,_,a,b,supplyBit hp.base e a,supplyBit hq.base t b,same,change⟩
  · exact Or.inr ⟨hz,_,_,a,b,supplyBit hp.base e a,supplyBit hq.base t b,other,change⟩

def consume (f : Nat → Nat → Nat) (other output : Rel) : Rel := fun x c =>
  ∃ y b d, other y b ∧ output (f x y) d ∧ (b || d) = c

private theorem inputCorner {B : Nat} {f : Nat → Nat → Nat} {q out : Rel}
    (qbit : ∀ b, q (bit B b) b) (hf : Corner B f)
    (baseline : out (f 0 0) false) (extend : f 0 0 = 0 → ∃ d, out B d) :
    consume f q out 0 true ∨ ∃ b, consume f q out B b := by
  rcases hf with ⟨a,b,hab,hvalue⟩
  have ok : ∃ d, out (f (bit B a) (bit B b)) d := by
    rcases hvalue with h | ⟨h,h'⟩
    · exact ⟨false, h ▸ baseline⟩
    · rw [h']; exact extend h
  obtain ⟨d,hd⟩ := ok
  cases a with
  | false =>
    have hb : b = true := by simpa using hab
    subst b
    exact Or.inl ⟨_,true,d,qbit true,hd,rfl⟩
  | true => exact Or.inr ⟨b || d,_,b,d,qbit b,hd,rfl⟩

theorem consumeGood {B x y : Nat} {q out : Rel} {f : Nat → Nat → Nat}
    (hf : Corner B f) (hq : Supply B y q) (ho : Demand B (f x y) out) :
    Demand B x (consume f q out) := by
  refine ⟨⟨y,false,false,hq.base,ho.base,rfl⟩, ?_⟩
  rintro rfl
  rcases hq.alternative with h | ⟨rfl,h⟩
  · exact Or.inl ⟨y,true,false,h,ho.base,rfl⟩
  by_cases hidden : out (f 0 0) true
  · exact Or.inl ⟨0,false,true,hq.base,hidden,rfl⟩
  · exact inputCorner (supplyBit hq.base h) hf ho.base (fun h0 => (ho.alternative h0).resolve_left hidden)

theorem reverseCorner {B : Nat} {f : Nat → Nat → Nat} (hf : Corner B f) :
    Corner B (fun x y => f y x) := by
  rcases hf with ⟨a,b,hab,h⟩
  exact ⟨b,a,by simpa [Bool.or_comm] using hab,h⟩

def compareTo (g : Nat → Nat → Bool) (base : Bool) (other : Rel) : Rel := fun x c =>
  ∃ y, other y c ∧ g x y = base

theorem compareGood {B x y : Nat} {q : Rel} {g : Nat → Nat → Bool}
    (diag : g 0 0 = g B B) (hq : Supply B y q) :
    Demand B x (compareTo g (g x y) q) := by
  refine ⟨⟨y,hq.base,rfl⟩, ?_⟩
  rintro rfl
  rcases hq.alternative with h | ⟨rfl,h⟩
  · exact Or.inl ⟨y,h,rfl⟩
  · exact Or.inr ⟨true,B,h,diag.symm⟩

theorem full_perturbation {B x : Nat} {r : Rel} (h : Supply B x r) : ∃ value, r value true := by
  rcases h.alternative with hidden | ⟨_,altered⟩
  · exact ⟨x,hidden⟩
  · exact ⟨B,altered⟩

end ZeroWordTreePerturbation

#print axioms ZeroWordTreePerturbation.produceGood
#print axioms ZeroWordTreePerturbation.consumeGood
#print axioms ZeroWordTreePerturbation.full_perturbation
