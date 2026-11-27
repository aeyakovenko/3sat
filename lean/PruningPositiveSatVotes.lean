import Std

/-! Positive vote recovery on arbitrary finite proof trees. A round follows
timely YES votes until a leaf or a node with two silent children. The recorded
receipts are a subset of the files actually queried, sufficient to witness
a common missed satisfiable file for any designated sound group. -/

namespace PruningPositiveSatVotes

inductive Tree (α : Type) where
  | leaf (name : α) (passes : Bool)
  | fork (name : α) (left right : Tree α)

def live : Tree α → Bool
  | .leaf _ p => p
  | .fork _ a b => live a || live b

def kids : Tree α → List (Tree α)
  | .leaf _ _ => []
  | .fork _ a b => [a,b]

def passes : Tree α → Bool
  | .leaf _ p => p
  | .fork .. => false

theorem live_child (t : Tree α) (h : live t = true) (no : passes t = false) :
    ∃ s ∈ kids t, live s = true := by
  cases t with
  | leaf _ _ => simp_all [live, passes]
  | fork _ a b =>
    simp only [live, Bool.or_eq_true] at h
    rcases h with ha | hb
    · exact ⟨a, by simp [kids], ha⟩
    · exact ⟨b, by simp [kids], hb⟩

def walk (vote : Tree α → Bool) : Tree α → Tree α
  | .leaf n p => .leaf n p
  | .fork n a b =>
      if vote a then walk vote a else if vote b then walk vote b else .fork n a b

theorem tip_facts (vote : Tree α → Bool) (root : Tree α) (yes : vote root = true) :
    vote (walk vote root) = true ∧ ∀ s ∈ kids (walk vote root), vote s = false := by
  induction root with
  | leaf n p => simp [walk, kids, yes]
  | fork n a b ia ib =>
    cases ha : vote a <;> cases hb : vote b <;>
      simp_all [walk, kids]

variable {ι α : Type}

def anyYes (vote : ι → Tree α → Bool) (pool : List ι) (t : Tree α) : Bool :=
  pool.any (fun i => vote i t)

def dropYes (vote : ι → Tree α → Bool) (pool : List ι) (t : Tree α) : List ι :=
  pool.filter (fun i => !(vote i t))

theorem drops_one (vote : ι → Tree α → Bool) (pool : List ι) (t : Tree α)
    (v : anyYes vote pool t = true) : (dropYes vote pool t).length < pool.length := by
  induction pool with
  | nil => simp [anyYes] at v
  | cons i tail ih =>
    cases h : vote i t with
    | false =>
      have hv : anyYes vote tail t = true := by simpa [anyYes, h] using v
      have shorter := ih hv
      simpa [dropYes, h] using Nat.succ_lt_succ shorter
    | true =>
      have le := List.length_filter_le (fun j => !(vote j t)) tail
      simpa [dropYes,h] using Nat.lt_succ_of_le le

structure Trace (α : Type) where
  recovered : Bool
  receipts : List (Tree α)

def run (vote : ι → Tree α → Bool) (root : Tree α) : Nat → List ι → Trace α
  | 0, _ => ⟨false, []⟩
  | fuel+1, pool =>
    if anyYes vote pool root then
      let tip := walk (anyYes vote pool) root
      let recorded := root :: tip :: kids tip
      if passes tip then ⟨true, recorded⟩
      else
        let tail := run vote root fuel (dropYes vote pool tip)
        ⟨tail.recovered, recorded ++ tail.receipts⟩
    else ⟨false, [root]⟩

def Miss (vote : ι → Tree α → Bool) (honest : ι → Prop) (rs : List (Tree α)) : Prop :=
  ∃ t ∈ rs, live t = true ∧ ∀ i, honest i → vote i t = false

theorem miss_mono {vote : ι → Tree α → Bool} {honest : ι → Prop} {a b : List (Tree α)}
    (inclusion : ∀ t ∈ a, t ∈ b) (m : Miss vote honest a) : Miss vote honest b := by
  obtain ⟨t,mem,ok,miss⟩ := m
  exact ⟨t,inclusion _ mem,ok,miss⟩

/-- All quantified voters may be wrong outside the designated group.
For the group, only the soundness of YES is assumed. -/
theorem recover_or_common_miss (vote : ι → Tree α → Bool) (honest : ι → Prop)
    (sound : ∀ i, honest i → ∀ t, vote i t = true → live t = true)
    (root : Tree α) (existsProof : live root = true)
    (fuel : Nat) (pool : List ι) (budget : pool.length < fuel)
    (present : ∀ i, honest i → i ∈ pool) :
    (run vote root fuel pool).recovered = true ∨
    Miss vote honest (run vote root fuel pool).receipts := by
  induction fuel generalizing pool with
  | zero => omega
  | succ fuel ih =>
    cases v : anyYes vote pool root with
    | false =>
      right
      simp only [run,v, Bool.false_eq_true, ↓reduceIte]
      refine ⟨root, by simp, existsProof, ?_⟩
      intro i hi
      cases vi : vote i root
      · rfl
      · have anyT : anyYes vote pool root = true :=
          List.any_eq_true.mpr ⟨i, present i hi, vi⟩
        simp_all
    | true =>
      let tip := walk (anyYes vote pool) root
      obtain ⟨tipYes, silent⟩ := tip_facts (anyYes vote pool) root v
      change anyYes vote pool tip = true at tipYes
      change ∀ s ∈ kids tip, anyYes vote pool s = false at silent
      cases done : passes tip with
      | true =>
        left
        simp [run,v,←show tip = walk (anyYes vote pool) root from rfl,done]
      | false =>
        let remaining := dropYes vote pool tip
        let more := run vote root fuel remaining
        have spec : run vote root (fuel+1) pool =
            ⟨more.recovered, (root :: tip :: kids tip) ++ more.receipts⟩ := by
          simp [run,v,←show tip = walk (anyYes vote pool) root from rfl,done,more,remaining]
        rw [spec]
        cases tipLive : live tip with
        | true =>
          obtain ⟨s, mem, ok⟩ := live_child tip tipLive done
          right
          refine ⟨s, by simp [mem], ok, ?_⟩
          intro i hi
          cases vi : vote i s
          · rfl
          · have anyT : anyYes vote pool s = true := List.any_eq_true.mpr ⟨i,present i hi,vi⟩
            have no := silent s mem
            simp_all
        | false =>
          have keep : ∀ i, honest i → i ∈ remaining := by
            intro i hi
            have no : vote i tip = false := by
              cases h : vote i tip
              · rfl
              · have := sound i hi tip h
                simp_all
            exact List.mem_filter.mpr ⟨present i hi, by simp [no]⟩
          have smaller := drops_one vote pool tip tipYes
          have enough : remaining.length < fuel := by
            change (dropYes vote pool tip).length < fuel
            omega
          rcases ih remaining enough keep with yes | lost
          · exact Or.inl yes
          · exact Or.inr (miss_mono (fun _ m => List.mem_append_right _ m) lost)

end PruningPositiveSatVotes
