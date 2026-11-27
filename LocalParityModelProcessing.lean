import Std

namespace LocalParityModelProcessing

inductive Decision (ι : Type) where
  | leaf (answer : Bool)
  | ask (address : ι) (next : Bool → Decision ι)

def run {ι : Type} (bits : ι → Bool) : Decision ι → Bool
  | .leaf answer => answer
  | .ask address next => run bits (next (bits address))

def touches {ι : Type} (bits hidden : ι → Bool) : Decision ι → Bool
  | .leaf _ => false
  | .ask address next => hidden address || touches bits hidden (next (bits address))

/-- Test whether the adaptive path on the original source touches any erased
coordinate. If it does not, changing the erased bits leaves all branch choices intact. -/
theorem no_change_off_path {ι : Type} (bits patched hidden : ι → Bool)
    (agree : ∀ i, hidden i = false → bits i = patched i) (tree : Decision ι) :
    touches bits hidden tree = false → run bits tree = run patched tree := by
  induction tree with
  | leaf => intro _; rfl
  | ask i next ih =>
    simp only [touches, Bool.or_eq_false_iff, run]
    rintro ⟨atHead, later⟩
    have head := agree i atHead
    rw [← head]
    exact ih (bits i) later

def parity : List Bool → Bool
  | [] => false
  | x :: xs => xor x (parity xs)

theorem parity_append (xs ys : List Bool) : parity (xs ++ ys) = xor (parity xs) (parity ys) := by
  induction xs with
  | nil => simp [parity]
  | cons x xs ih => simp only [List.cons_append,parity,ih]; cases x <;> cases parity xs <;> cases parity ys <;> rfl

theorem parity_perm {xs ys : List Bool} (h : xs.Perm ys) : parity xs = parity ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [parity,ih]
  | swap x y xs => cases x <;> cases y <;> cases hh : parity xs <;> simp [parity,hh]
  | trans _ _ ih jh => exact ih.trans jh

def endpointBits {ι : Type} (value : ι → Bool) : List (ι × ι) → List Bool
  | [] => []
  | (u,v)::rest => value u :: value v :: endpointBits value rest

theorem edge_gates {ι : Type} (value : ι → Bool) (edges : List (ι × ι)) :
    parity (edges.map (fun e => xor (value e.1) (value e.2))) = parity (endpointBits value edges) := by
  induction edges with
  | nil => rfl
  | cons e edges ih =>
    rcases e with ⟨u,v⟩
    simp only [List.map_cons, parity, endpointBits, ih]
    cases value u <;> cases value v <;> cases parity (endpointBits value edges) <;> rfl

theorem odd_copies (a : Bool) (n : Nat) : parity (List.replicate (2*n+1) a) = a := by
  induction n with
  | zero => cases a <;> rfl
  | succ n ih =>
    rw [show 2*(n+1)+1 = (2*n+1)+1+1 by omega]
    change xor a (xor a (parity (List.replicate (2*n+1) a))) = a
    rw [ih]
    cases a <;> rfl

end LocalParityModelProcessing

#print axioms LocalParityModelProcessing.no_change_off_path
#print axioms LocalParityModelProcessing.edge_gates
#print axioms LocalParityModelProcessing.parity_perm
#print axioms LocalParityModelProcessing.odd_copies
