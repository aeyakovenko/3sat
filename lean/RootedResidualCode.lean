import Std

/-! A fixed circuit supplies the predecessor addresses. The restricted code
contains only the two port flags at each fresh visited gate. The first lemma
recovers site names from this address-free code. The second proves agreement
of scoped semantics after each incoming edge either has an equal constant pin
or returns to the visited cone. -/
namespace RootedResidualCode

inductive Flag | zero | one | visit deriving DecidableEq
abbrev Frame := Flag × Flag
abbrev Shape := Nat → Option (Nat × Nat)

def push (f : Flag) (child : Nat) (rest : List Nat) : List Nat :=
  match f with
  | .visit => child :: rest
  | _ => rest

def walk (shape : Shape) (flags : Nat → Frame) :
    Nat → List Nat → List Nat → List (Nat × Frame)
  | 0, _, _ => []
  | _+1, [], _ => []
  | n+1, addr :: todo, seen =>
    if addr ∈ seen then walk shape flags n todo seen
    else match shape addr with
      | none => walk shape flags n todo seen
      | some (l, r) =>
        let frame := flags addr
        let more := push frame.1 l (push frame.2 r todo)
        (addr, frame) :: walk shape flags n more (addr :: seen)

theorem recover_sites (shape : Shape) (f g : Nat → Frame) (fuel : Nat)
    (todo seen : List Nat)
    (code : (walk shape f fuel todo seen).map Prod.snd =
      (walk shape g fuel todo seen).map Prod.snd) :
    walk shape f fuel todo seen = walk shape g fuel todo seen := by
  induction fuel generalizing todo seen with
  | zero => rfl
  | succ fuel ih =>
    cases todo with
    | nil => rfl
    | cons a todo =>
      by_cases old : a ∈ seen
      · simp only [walk, if_pos old] at code ⊢
        exact ih todo seen code
      · cases sh : shape a with
        | none =>
          simp only [walk, if_neg old, sh] at code ⊢
          exact ih todo seen code
        | some lr =>
          rcases lr with ⟨l, r⟩
          simp only [walk, if_neg old, sh, List.map_cons, List.cons.injEq] at code
          obtain ⟨sameFrame, rest⟩ := code
          simp only [walk, if_neg old, sh, sameFrame, List.cons.injEq, true_and]
          rw [sameFrame] at rest
          exact ih _ _ rest

theorem unique_sites (shape : Shape) (flags : Nat → Frame) (fuel : Nat)
    (todo seen : List Nat) :
    ((walk shape flags fuel todo seen).map Prod.fst).Nodup ∧
      ∀ i ∈ (walk shape flags fuel todo seen).map Prod.fst, i ∉ seen := by
  induction fuel generalizing todo seen with
  | zero => simp [walk]
  | succ n ih =>
    cases todo with
    | nil => simp [walk]
    | cons a todo =>
      by_cases old : a ∈ seen
      · simpa only [walk, if_pos old] using ih todo seen
      · cases sh : shape a with
        | none => simpa only [walk, if_neg old, sh] using ih todo seen
        | some lr =>
          rcases lr with ⟨l,r⟩
          let more := push (flags a).1 l (push (flags a).2 r todo)
          obtain ⟨distinct, outside⟩ := ih more (a :: seen)
          simp only [walk, if_neg old, sh, List.map_cons]
          constructor
          · refine List.nodup_cons.mpr ⟨?_, distinct⟩
            intro appears
            exact outside a appears List.mem_cons_self
          · intro i appears
            rcases List.mem_cons.mp appears with eq | tail
            · exact eq ▸ old
            · exact fun inSeen => outside i tail (List.mem_cons_of_mem _ inSeen)

def explains (retained : Nat → Prop) (u v : Nat → Bool) (child : Nat) : Flag → Prop
  | .visit => retained child
  | .zero => u child = false ∧ v child = false
  | .one => u child = true ∧ v child = true

private theorem decoded_port {retained : Nat → Prop} {u v : Nat → Bool}
    {child : Nat} (f : Flag) (explained : explains retained u v child f)
    (recurse : retained child → u child = v child) : u child = v child := by
  cases f with
  | visit => exact recurse explained
  | zero => exact explained.1.trans explained.2.symm
  | one => exact explained.1.trans explained.2.symm

theorem same_residual_value (shape : Shape) (combine : Nat → Bool → Bool → Bool)
    (retained : Nat → Prop) (flags : Nat → Frame) (u v : Nat → Bool)
    (inputs : ∀ a, retained a → shape a = none → u a = v a)
    (valid : ∀ a l r, retained a → shape a = some (l,r) →
      l < a ∧ r < a ∧ u a = combine a (u l) (u r) ∧ v a = combine a (v l) (v r))
    (records : ∀ a l r, retained a → shape a = some (l,r) →
      explains retained u v l (flags a).1 ∧ explains retained u v r (flags a).2) :
    ∀ a, retained a → u a = v a := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a earlier =>
    intro live
    cases sh : shape a with
    | none => exact inputs a live sh
    | some lr =>
      rcases lr with ⟨l,r⟩
      obtain ⟨hl, hr, hu, hv⟩ := valid a l r live sh
      obtain ⟨pl, pr⟩ := records a l r live sh
      rw [hu, hv, decoded_port _ pl (earlier l hl), decoded_port _ pr (earlier r hr)]

end RootedResidualCode
