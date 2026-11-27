import Std

namespace CirculationCutBudget

private def excess (degrees : List Nat) := (degrees.map (fun d => d - 2)).sum
private def highMass (degrees : List Nat) := (degrees.map (fun d => if 3 ≤ d then d else 0)).sum

private theorem highMass_le (degrees : List Nat) : highMass degrees ≤ 3 * excess degrees := by
  induction degrees with
  | nil => simp [excess, highMass]
  | cons d ds ih =>
    have hd : (if 3 ≤ d then d else 0) ≤ 3 * (d - 2) := by split <;> omega
    simpa [highMass, excess, Nat.mul_add] using Nat.add_le_add hd ih

private theorem degree_sum (degrees : List Nat) (mindeg : ∀ d ∈ degrees, 2 ≤ d) :
    degrees.sum = excess degrees + 2 * degrees.length := by
  induction degrees with
  | nil => simp [excess]
  | cons d ds ih =>
    have hd := mindeg d List.mem_cons_self
    have hs := ih (fun x hx => mindeg x (List.mem_cons_of_mem _ hx))
    simp only [List.sum_cons, excess, List.map_cons, List.length_cons, List.map] at *
    omega

/-- If every one of b incidences touches a component of degree at least three,
    there is at least b/6 excess in the bipartite component graph's cycle rank. -/
theorem shared_edges_force_rank (degrees : List Nat) (b l : Nat)
    (mindeg : ∀ d ∈ degrees, 2 ≤ d)
    (incident : b ≤ highMass degrees) (handshake : degrees.sum = 2*b)
    (rank : l + degrees.length = b + 1) : b + 6 ≤ 6*l := by
  have sharp := highMass_le degrees
  have total := degree_sum degrees mindeg
  omega

/-- Any binary grouping, allowing arbitrary labels and a measure on every subtree. -/
inductive Partition (α : Type) where
  | leaf : α → Partition α
  | split : Partition α → Partition α → Partition α

def atLeaves (g : Partition α → Int) : Partition α → Int
  | .leaf x => g (.leaf x)
  | .split l r => atLeaves g l + atLeaves g r

def totalGain (g : Partition α → Int) : Partition α → Int
  | .leaf _ => 0
  | .split l r =>
      g (.split l r) - g l - g r + totalGain g l + totalGain g r

/-- Apply to shortened-code dimensions, including partitions chosen from a trace. -/
theorem telescope (g : Partition α → Int) (t : Partition α) :
    totalGain g t = g t - atLeaves g t := by
  induction t with
  | leaf x => simp [totalGain, atLeaves]
  | split l r il ir => simp only [totalGain, atLeaves, il, ir]; omega

end CirculationCutBudget
