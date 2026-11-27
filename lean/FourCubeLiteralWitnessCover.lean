import Std

/-!
A separate finite proof of the four-auxiliary, seven-unguarded-row exclusion.
For each of the seven edges select one private endpoint at the all-false
boundary. Its other endpoint must be outside this seven-point list and outside
the three markers. All six remaining vertices must be hit. The finite check
below rules out such a surjective neighbor map. Native evaluation of the one
closed enumeration is the only use of `native_decide`.
-/
namespace FourCubeLiteralWitnessCover

abbrev Vertex := Fin 16
abbrev Face := List Vertex

def vertices : List Vertex := List.finRange 16

@[simp] theorem all_vertices : ∀ v : Vertex, v ∈ vertices := by decide

/-- All square faces by fixing two distinct coordinates and their values. -/
def faces : List Face :=
  (List.range 4).flatMap fun i => (List.range 4).flatMap fun j =>
    if i < j then
      [false, true].flatMap fun a => [false, true].map fun b =>
        vertices.filter fun v => v.val.testBit i == a && v.val.testBit j == b
    else []

def neighbors (x y : Vertex) : Bool := [1,2,4,8].contains (x.val ^^^ y.val)

def select : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _+1, [] => []
  | k+1, x::xs => (select k xs).map (x :: ·) ++ select (k+1) xs

/-- The search includes precisely the ordered sublists of the selected size. -/
theorem mem_select_iff {k : Nat} {xs ys : List α} :
    ys ∈ select k xs ↔ ys.Sublist xs ∧ ys.length = k := by
  induction xs generalizing k ys with
  | nil =>
    cases k <;> cases ys <;> simp [select]
  | cons x xs ih =>
    cases k with
    | zero => cases ys <;> simp [select]
    | succ k =>
      simp only [select, List.mem_append, List.mem_map, ih]
      constructor
      · rintro (⟨zs, ⟨hs, hl⟩, rfl⟩ | ⟨hs, hl⟩)
        · exact ⟨hs.cons₂ x, by simp [hl]⟩
        · exact ⟨hs.cons x, hl⟩
      · rintro ⟨hs, hl⟩
        cases hs with
        | cons _ hs => exact Or.inr ⟨hs, hl⟩
        | cons₂ _ hs =>
          exact Or.inl ⟨_, ⟨hs, by simpa using hl⟩, rfl⟩

def exclusive (f g h : Face) : List Vertex := f.filter fun v => !g.contains v && !h.contains v

def outside (f g h : Face) : List Vertex :=
  vertices.filter fun v => !f.contains v && !g.contains v && !h.contains v

def remaining (p : List Vertex) (x y z : Vertex) : List Vertex :=
  vertices.filter fun v => v != x && v != y && v != z && !p.contains v

/-- Every triple of different targets has three distinct private neighbors. -/
def tripleTest (p r : List Vertex) : Bool :=
  r.all fun x => r.all fun y => r.all fun z =>
    x == y || x == z || y == z ||
      p.any fun a => neighbors x a &&
        p.any fun b => a != b && neighbors y b &&
          p.any fun c => a != c && b != c && neighbors z c

def tests (p r : List Vertex) : Bool :=
  (r.all fun x => p.any fun a => neighbors x a) &&
  (p.all fun a => r.any fun x => neighbors x a) &&
  tripleTest p r

/-- Surjectivity of the edge partner map implies the checked Hall conditions. -/
theorem tests_of_partner {p r : List Vertex} (partner : Vertex → Vertex)
    (hee : ∀ a ∈ p, partner a ∈ r ∧ neighbors (partner a) a = true)
    (onto : ∀ x ∈ r, ∃ a ∈ p, partner a = x) : tests p r = true := by
  simp only [tests, tripleTest, Bool.and_eq_true, List.all_eq_true, List.any_eq_true]
  constructor
  · constructor
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := onto x hx
      exact ⟨a, ha, (hee a ha).2⟩
    · intro a ha
      exact ⟨partner a, (hee a ha).1, (hee a ha).2⟩
  · intro x hx y hy z hz
    by_cases hxy : x = y
    · simp [hxy]
    by_cases hxz : x = z
    · simp [hxz]
    by_cases hyz : y = z
    · simp [hyz]
    obtain ⟨a, ha, rfl⟩ := onto x hx
    obtain ⟨b, hb, rfl⟩ := onto y hy
    obtain ⟨c, hc, rfl⟩ := onto z hz
    have hab : a ≠ b := fun e => hxy (congrArg partner e)
    have hac : a ≠ c := fun e => hxz (congrArg partner e)
    have hbc : b ≠ c := fun e => hyz (congrArg partner e)
    simp only [beq_iff_eq, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
      bne_iff_ne]
    exact Or.inr ⟨a, ha, (hee a ha).2, b, hb, ⟨hab, (hee b hb).2⟩, c, hc,
      ⟨hac, hbc⟩, (hee c hc).2⟩

def rejected (f g h : Face) : Bool :=
  (select 7 (outside f g h)).all fun p =>
    (exclusive f g h).all fun x =>
      (exclusive g f h).all fun y =>
        (exclusive h f g).all fun z =>
          !(tests p (remaining p x y z))

/-- Ordered face triples include repetitions and all permutations. -/
theorem all_rejected :
    (faces.all fun f => faces.all fun g => faces.all fun h => rejected f g h) = true := by
  native_decide

theorem no_seven_private_edges {f g h : Face} {p : List Vertex} {x y z : Vertex}
    (hf : f ∈ faces) (hg : g ∈ faces) (hh : h ∈ faces)
    (hx : x ∈ exclusive f g h) (hy : y ∈ exclusive g f h) (hz : z ∈ exclusive h f g)
    (hpriv : p.Sublist (outside f g h)) (hsize : p.length = 7) :
    ¬ ∃ partner : Vertex → Vertex,
      (∀ a ∈ p, partner a ∈ remaining p x y z ∧ neighbors (partner a) a = true) ∧
      (∀ q ∈ remaining p x y z, ∃ a ∈ p, partner a = q) := by
  have hcheck := all_rejected
  simp only [List.all_eq_true, rejected] at hcheck
  have hbad := hcheck f hf g hg h hh p (mem_select_iff.mpr ⟨hpriv, hsize⟩) x hx y hy z hz
  rintro ⟨partner, hee, onto⟩
  simp [tests_of_partner partner hee onto] at hbad

/-- Semantic form: index each row by a chosen private witness, in cube order.
The row's set of forbidden assignments is an undirected cube edge. Private
witnesses cannot be covered by a different row. These rows cannot cover
precisely the complement of the three markers. -/
theorem no_seven_private_row_cover {f g h : Face} {p : List Vertex} {x y z : Vertex}
    (hf : f ∈ faces) (hg : g ∈ faces) (hh : h ∈ faces)
    (hx : x ∈ exclusive f g h) (hy : y ∈ exclusive g f h) (hz : z ∈ exclusive h f g)
    (hp : p.Sublist (outside f g h)) (hn : p.length = 7)
    (covered : Vertex → Vertex → Prop)
    (edge : ∀ a ∈ p, ∃ b, neighbors b a = true ∧
      ∀ q, covered a q ↔ q = a ∨ q = b)
    (privateRow : ∀ a ∈ p, ∀ b ∈ p, covered a b → a = b) :
    ¬ (∀ q, (∃ a ∈ p, covered a q) ↔ q ≠ x ∧ q ≠ y ∧ q ≠ z) := by
  classical
  intro cover
  let partner (a : Vertex) := if ha : a ∈ p then (edge a ha).choose else a
  have hr (a : Vertex) (ha : a ∈ p) :
      neighbors (partner a) a = true ∧
      ∀ q, covered a q ↔ q = a ∨ q = partner a := by
    simpa only [partner, dif_pos ha] using (edge a ha).choose_spec
  apply no_seven_private_edges hf hg hh hx hy hz hp hn
  refine ⟨partner, ?_, ?_⟩
  · intro a ha
    obtain ⟨adj, row⟩ := hr a ha
    have hits := (row (partner a)).mpr (Or.inr rfl)
    obtain ⟨h1, h2, h3⟩ := (cover (partner a)).mp ⟨a, ha, hits⟩
    have hout : partner a ∉ p := by
      intro hmem
      have same := privateRow a ha (partner a) hmem hits
      rw [← same] at adj
      simp [neighbors] at adj
    exact ⟨by simp [remaining, h1, h2, h3, hout], adj⟩
  · intro q hq
    have hq' : q ≠ x ∧ q ≠ y ∧ q ≠ z ∧ q ∉ p := by
      simpa [remaining, and_assoc] using hq
    obtain ⟨h1, h2, h3, hout⟩ := hq'
    obtain ⟨a, ha, hits⟩ := (cover q).mpr ⟨h1, h2, h3⟩
    refine ⟨a, ha, ?_⟩
    rcases ((hr a ha).2 q).mp hits with e | e
    · exact False.elim (hout (e ▸ ha))
    · exact e.symm

end FourCubeLiteralWitnessCover
