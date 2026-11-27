import Std

namespace PrefixRankParity

inductive Variable where
  | flag (slot : Nat)
  | seen (bound : Nat)
  | acc (time : Nat)
  deriving DecidableEq

structure Literal where
  var : Variable
  positive : Bool

abbrev Clause := Literal × Literal × Literal
abbrev CNF := List Clause

private def pos (v : Variable) : Literal := ⟨v,true⟩
private def neg (v : Variable) : Literal := ⟨v,false⟩
private def unit (v : Literal) : Clause := (v,v,v)
private def binary (a b : Literal) : Clause := (a,b,b)

def value (set : Variable → Bool) (lit : Literal) := if lit.positive then set lit.var else !set lit.var

def eval (set : Variable → Bool) (cl : Clause) :=
  value set cl.1 || value set cl.2.1 || value set cl.2.2

def Satisfies (set : Variable → Bool) (f : CNF) : Prop := ∀ cl ∈ f, eval set cl = true

private theorem andCNF (v : Variable → Bool) (a b : CNF) :
    Satisfies v (a++b) ↔ Satisfies v a ∧ Satisfies v b := by
  simp only [Satisfies,List.mem_append,or_imp,forall_and]

/-- One prefix-OR gate and an incompatibility clause forbid a second flag. -/
def selector (i : Nat) : CNF :=
  let p := Variable.seen i
  let x := Variable.flag i
  let z := Variable.seen (i+1)
  [binary (neg p) (pos z),binary (neg x) (pos z),(pos p,pos x,neg z),binary (neg p) (neg x)]

/-- Four exact-three clauses express z = p XOR x. -/
def accumulator (c : Nat → Nat) (i : Nat) : CNF :=
  let p := Variable.acc i
  let x := Variable.flag (c i)
  let z := Variable.acc (i+1)
  [(pos p,pos x,neg z),(pos p,neg x,pos z),(neg p,pos x,pos z),(neg p,neg x,neg z)]

private theorem selectorSpec (v : Variable → Bool) (i : Nat) :
    Satisfies v (selector i) ↔ v (.seen (i+1)) = (v (.seen i) || v (.flag i)) ∧
      (v (.seen i) && v (.flag i)) = false := by
  cases a : v (.seen i) <;> cases b : v (.flag i) <;> cases c : v (.seen (i+1)) <;>
    simp [Satisfies,selector,eval,value,pos,neg,binary,a,b,c]

private theorem accSpec (v : Variable → Bool) (c : Nat → Nat) (i : Nat) :
    Satisfies v (accumulator c i) ↔ v (.acc (i+1)) = (v (.acc i) ^^ v (.flag (c i))) := by
  cases a : v (.acc i) <;> cases b : v (.flag (c i)) <;> cases z : v (.acc (i+1)) <;>
    simp [Satisfies,accumulator,eval,value,pos,neg,a,b,z]

/-- Only the two final units of this explicit clause list depend on the query.
    Unit and binary constraints repeat literals to keep every clause ternary. -/
def body (slots steps : Nat) (c : Nat → Nat) : CNF :=
  [unit (neg (.seen 0)),unit (neg (.acc 0))] ++
    ((List.range slots).flatMap selector ++ (List.range steps).flatMap (accumulator c))

def query (slots steps : Nat) (c : Nat → Nat) (s j : Nat) : CNF :=
  body slots steps c ++ [unit (pos (.flag s)),unit (pos (.acc j))]

private theorem familyCNF (v : Variable → Bool) (f : Nat → CNF) (n : Nat) :
    Satisfies v ((List.range n).flatMap f) ↔ ∀ i < n, Satisfies v (f i) := by
  constructor
  · intro h i hi cl member
    exact h cl (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,member⟩)
  · intro h cl member
    obtain ⟨i,hi,inside⟩ := List.mem_flatMap.mp member
    exact h i (List.mem_range.mp hi) cl inside

private theorem querySpec (v : Variable → Bool) (slots steps : Nat) (c : Nat → Nat) (s j : Nat) :
    Satisfies v (query slots steps c s j) ↔
      (v (.seen 0) = false ∧ v (.acc 0) = false) ∧
      ((∀ i < slots, v (.seen (i+1)) = (v (.seen i) || v (.flag i)) ∧
                    (v (.seen i) && v (.flag i)) = false) ∧
       (∀ i < steps, v (.acc (i+1)) = (v (.acc i) ^^ v (.flag (c i))))) ∧
      (v (.flag s) = true ∧ v (.acc j) = true) := by
  simp only [query,body,andCNF,familyCNF,selectorSpec,accSpec]
  simp [Satisfies,unit,eval,value,pos,neg,and_assoc]

/-- Number of occurrences in c[0],...,c[j−1]. -/
def rank (c : Nat → Nat) (s : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => rank c s j + (if c j = s then 1 else 0)

def parity (n : Nat) : Bool := decide (n % 2 = 1)

private theorem parityStep (c : Nat → Nat) (s i : Nat) :
    parity (rank c s (i+1)) = (parity (rank c s i) ^^ decide (c i = s)) := by
  by_cases hit : c i = s
  · by_cases odd : rank c s i % 2 = 1
    · have even : ¬ (rank c s i+1) % 2 = 1 := by omega
      simp [rank,hit,parity,odd,even]
    · have next : (rank c s i+1) % 2 = 1 := by omega
      simp [rank,hit,parity,odd,next]
  · simp [rank,hit]

private theorem flaggedSeen (F P : Nat → Bool) (slots : Nat) (a : Nat) (on : F a = true)
    (step : ∀ i < slots, P (i+1) = (P i || F i) ∧ (P i && F i) = false)
    (b : Nat) (after : a < b) (within : b ≤ slots) : P b = true := by
  induction b with
  | zero => omega
  | succ b ih =>
    have next := (step b (by omega)).1
    by_cases eq : b = a
    · rw [next,eq,on,Bool.or_true]
    · rw [next,ih (by omega) (by omega)]
      rfl

private theorem onlyChosen (F P : Nat → Bool) (slots s : Nat) (inside : s < slots)
    (chosen : F s = true)
    (step : ∀ i < slots, P (i+1) = (P i || F i) ∧ (P i && F i) = false)
    (i : Nat) (hi : i < slots) : F i = decide (i = s) := by
  by_cases eq : i = s
  · cases eq
    simpa using chosen
  · rw [decide_eq_false eq]
    cases fi : F i with
    | false => rfl
    | true =>
      by_cases before : i < s
      · have seen := flaggedSeen F P slots i fi step s before (by omega)
        have no := (step s inside).2
        rw [seen,chosen] at no
        contradiction
      · have seen := flaggedSeen F P slots s chosen step i (by omega) (by omega)
        have no := (step i hi).2
        rw [seen,fi] at no
        contradiction

theorem satIffRankOdd (slots steps : Nat) (c : Nat → Nat) (s j : Nat)
    (validEvent : ∀ i < steps, c i < slots) (validSlot : s < slots) (validTime : j ≤ steps) :
    (∃ v, Satisfies v (query slots steps c s j)) ↔ rank c s j % 2 = 1 := by
  constructor
  · rintro ⟨v,assignment⟩
    obtain ⟨⟨_,z⟩,⟨select,chain⟩,⟨chosen,accept⟩⟩ :=
      (querySpec v slots steps c s j).mp assignment
    have flags := onlyChosen (fun i => v (.flag i)) (fun i => v (.seen i))
      slots s validSlot chosen select
    have track (i : Nat) (hi : i ≤ steps) : v (.acc i) = parity (rank c s i) := by
      induction i with
      | zero => exact z
      | succ i ih =>
        rw [chain i (by omega),ih (by omega),parityStep]
        exact congrArg _ (flags (c i) (validEvent i (by omega)))
    exact of_decide_eq_true ((track j validTime).symm.trans accept)
  · intro odd
    let v : Variable → Bool
      | .flag k => decide (k=s)
      | .seen k => decide (s<k)
      | .acc i => parity (rank c s i)
    refine ⟨v,(querySpec v slots steps c s j).mpr ?_⟩
    refine ⟨⟨by simp [v],rfl⟩,⟨?_,fun i _ => parityStep c s i⟩,by simp [v,parity,odd]⟩
    intro i _
    by_cases lt : s < i
    · have ne : i ≠ s := by omega
      have next : s < i+1 := by omega
      simp [v,lt,ne,next]
    · by_cases eq : i = s
      · subst i; simp [v]
      · have next : ¬s < i+1 := by omega
        simp [v,lt,eq,next]

theorem clauseCount (slots steps : Nat) (c : Nat → Nat) (s j : Nat) :
    (query slots steps c s j).length = 4*(slots+steps)+4 := by
  have repeated (n : Nat) : ((List.range n).map (fun _ => 4)).sum = n*4 := by
    change ((List.range n).map (Function.const Nat 4)).sum = n*4
    rw [List.map_const,List.length_range,List.sum_replicate_nat]
  simp [query,body,List.length_flatMap,selector,accumulator,repeated]
  omega

end PrefixRankParity
