import Std

/-! Abstract stopped-query packet semantics and fork-private memory.
The native time and dynamic lower-bound arguments are separate. -/
namespace StoppedDisjointnessFork

section Selection
variable {B E Q I : Type} [DecidableEq B]

/-- Only insertion packets already observed by the master are present on a
stopped input. The active query and later dummy slots both use `none`. -/
def hit (sets : Q → E → Bool) (batch : B) (q : Q) (data : Option (B × E)) : Bool :=
  match data with
  | some (b, e) => decide (b = batch) && sets q e
  | none => false

theorem oracle_disjoint (sets : Q → E → Bool) (batch : B) (q : Q)
    (data : I → Option (B × E)) :
    (∀ i, hit sets batch q (data i) = false) ↔
      ∀ i e, data i = some (batch,e) → sets q e = false := by
  constructor
  · intro allFalse i e atSlot
    simpa [atSlot, hit] using allFalse i
  · intro avoids i
    cases h : data i with
    | none => rfl
    | some p =>
      obtain ⟨b, e⟩ := p
      by_cases same : b = batch
      · subst b
        simp [hit, avoids i e h]
      · simp [hit, same]

/-- For either signed verdict the modeled hit bits have at most one possible
full valuation. A satisfying valuation exists exactly for the indicated sign. -/
theorem stopped_verdict (sets : Q → E → Bool) (batch : B) (q : Q)
    (data : I → Option (B × E)) (tag : Bool) :
    (∃ z : I → Bool, (∀ i, z i = hit sets batch q (data i)) ∧
      (tag = true ↔ ∀ i, z i = false)) ↔
      (tag = true ↔ ∀ i e, data i = some (batch,e) → sets q e = false) := by
  constructor
  · rintro ⟨z, vals, sat⟩
    simpa only [vals, oracle_disjoint] using sat
  · intro verdict
    exact ⟨_, fun _ => rfl, verdict.trans (oracle_disjoint sets batch q data).symm⟩

theorem hit_valuation_unique (expected z z' : I → Bool)
    (h : ∀ i, z i = expected i) (h' : ∀ i, z' i = expected i) : z = z' :=
  funext fun i => (h i).trans (h' i).symm
end Selection

section DeliveredQuery
variable {I J B Q : Type}

/-- A delivered query carries only implications, conditional on its own
logical query ID. Equal set/batch requests may recur at other IDs. -/
def queryLinks (events : I → Option (J × B × Q)) (selected : J)
    (batch : B) (setName : Q) : Prop :=
  ∀ i b q, events i = some (selected,b,q) → b = batch ∧ q = setName

/-- The late signed stop pins the already delivered ID. Its batch/set pair
is forced, even with any number of repeated requests in the prefix. -/
theorem stop_after_delivery (events : I → Option (J × B × Q)) (selected : J)
    (slot : I) (b : B) (q : Q) (seen : events slot = some (selected,b,q))
    (uniqueId : ∀ i b' q', events i = some (selected,b',q') → i = slot)
    (batch : B) (setName : Q) :
    queryLinks events selected batch setName ↔ b = batch ∧ q = setName := by
  constructor
  · intro pins
    exact pins slot b q seen
  · rintro ⟨rfl, rfl⟩ i b' q' here
    obtain rfl := uniqueId i b' q' here
    rw [seen] at here
    simpa using (Option.some.inj here).symm

end DeliveredQuery

section CertifiedStream
variable {I B E Q : Type} [DecidableEq B]

def timedHit (sets : Q → E → Bool) (round : Nat) (batch : B) (q : Q) :
    Option (Nat × B × E) → Bool
  | none => false
  | some (t,b,e) => decide (t ≤ round) && decide (b = batch) && sets q e

/-- The chronological cutoff and batch selector enforce exactly the intended
answer in the full file with all future insertions still present. -/
theorem no_timed_hits (sets : Q → E → Bool) (round : Nat) (batch : B) (q : Q)
    (records : I → Option (Nat × B × E)) :
    (∀ i, timedHit sets round batch q (records i) = false) ↔
      ∀ i t e, records i = some (t,batch,e) → t ≤ round → sets q e = false := by
  constructor
  · intro no i t e atSlot earlier
    simpa [timedHit, atSlot, earlier] using no i
  · intro avoids i
    cases eq : records i with
    | none => rfl
    | some record =>
      obtain ⟨t,b,e⟩ := record
      by_cases earlier : t ≤ round
      · by_cases same : b = batch
        · subst b
          simp [timedHit, earlier, avoids i t e eq earlier]
        · simp [timedHit, earlier, same]
      · simp [timedHit, earlier]

/-- Once an ID is selected, gate equivalences determine all other wires.
Here `other` abstracts that entire uniquely determined auxiliary valuation. -/
structure FullVal (J Aux : Type) where
  id : J
  annotation : Bool
  actual : Bool
  other : Aux

variable {J Aux : Type} (report actual : J → Bool) (other : J → Aux)

def NormalValid (v : FullVal J Aux) : Prop :=
  v.annotation = report v.id ∧ v.actual = actual v.id ∧
  v.other = other v.id ∧ v.annotation ≠ v.actual

def fromError (j : {i : J // report i ≠ actual i}) :
    {v : FullVal J Aux // NormalValid report actual other v} :=
  ⟨⟨j.val, report j.val, actual j.val, other j.val⟩, rfl, rfl, rfl, j.property⟩

def toError (v : {v : FullVal J Aux // NormalValid report actual other v}) :
    {i : J // report i ≠ actual i} :=
  ⟨v.val.id, by obtain ⟨a,b,_,ne⟩ := v.property; simpa [← a, ← b] using ne⟩

/-- Two inverse maps give the exact normal-mode model count for finite J. -/
theorem error_then_id (j : {i : J // report i ≠ actual i}) :
    toError report actual other (fromError report actual other j) = j := by
  apply Subtype.ext
  rfl

theorem id_then_error (v : {v : FullVal J Aux // NormalValid report actual other v}) :
    fromError report actual other (toError report actual other v) = v := by
  rcases v with ⟨⟨j,a,d,u⟩, h⟩
  obtain ⟨ha,hd,hu,_⟩ := h
  apply Subtype.ext
  change FullVal.mk j (report j) (actual j) (other j) = FullVal.mk j a d u
  simp_all

/-- A physical request slot supplies the receipt for its logical ID; all
other slot types have no request ID and their receipt is false. -/
theorem receipt_exact (packet : I → Option J) (selected : J) (h : I → Prop)
    (rows : ∀ i, h i ↔ packet i = some selected) :
    (∃ i, h i) ↔ ∃ i, packet i = some selected := by
  constructor <;> rintro ⟨i,hi⟩
  · exact ⟨i,(rows i).mp hi⟩
  · exact ⟨i,(rows i).mpr hi⟩

/-- Adding the receipt to the global assertion restricts the established
model/error bijection exactly to already delivered IDs. -/
def fromDeliveredError (packet : I → Option J)
    (j : {i : J // (∃ k, packet k = some i) ∧ report i ≠ actual i}) :
    {v : FullVal J Aux // (∃ k, packet k = some v.id) ∧ NormalValid report actual other v} :=
  let n := fromError report actual other ⟨j.val,j.property.2⟩
  ⟨n.val, j.property.1, n.property⟩

def toDeliveredError (packet : I → Option J)
    (v : {v : FullVal J Aux // (∃ k, packet k = some v.id) ∧ NormalValid report actual other v}) :
    {i : J // (∃ k, packet k = some i) ∧ report i ≠ actual i} :=
  let j := toError report actual other ⟨v.val,v.property.2⟩
  ⟨j.val, v.property.1, j.property⟩

theorem delivered_id_roundtrip (packet : I → Option J)
    (j : {i : J // (∃ k, packet k = some i) ∧ report i ≠ actual i}) :
    toDeliveredError report actual other packet
      (fromDeliveredError report actual other packet j) = j := by
  apply Subtype.ext
  rfl

theorem delivered_model_roundtrip (packet : I → Option J)
    (v : {v : FullVal J Aux // (∃ k, packet k = some v.id) ∧ NormalValid report actual other v}) :
    fromDeliveredError report actual other packet
      (toDeliveredError report actual other packet v) = v := by
  apply Subtype.ext
  have same := id_then_error report actual other ⟨v.val,v.property.2⟩
  exact congrArg (fun n : {n : FullVal J Aux // NormalValid report actual other n} => n.val) same

end CertifiedStream

/-- A deterministic predictor on a recorded view is exact on a class of
honest histories precisely when all histories sharing that view agree. -/
theorem predictor_iff {History View : Type} (obs : History → View) (ans : History → Bool)
    (honest : History → Prop) :
    (∃ predict : View → Bool, ∀ h, honest h → predict (obs h) = ans h) ↔
      ∀ h k, honest h → honest k → obs h = obs k → ans h = ans k := by
  classical
  constructor
  · rintro ⟨p,good⟩ h k hh hk same
    exact (good h hh).symm.trans ((congrArg p same).trans (good k hk))
  · intro mono
    refine ⟨fun v => decide (∃ h, honest h ∧ obs h = v ∧ ans h = true), ?_⟩
    intro h hh
    cases value : ans h with
    | true =>
      have witness : ∃ k, honest k ∧ obs k = obs h ∧ ans k = true := ⟨h,hh,rfl,value⟩
      simp [witness]
    | false =>
      have no : ¬∃ k, honest k ∧ obs k = obs h ∧ ans k = true := by
        rintro ⟨k,hk,view,yes⟩
        have same := mono k h hk hh view
        simp [value,yes] at same
      simp [no]

section Work
variable {A W : Type} [DecidableEq A]

def put {V : Type} (f : A → V) (a : A) (v : V) (i : A) : V :=
  if i = a then v else f i

def realize (old : A → W) (privateWords : A → Option W) (i : A) : W :=
  (privateWords i).getD (old i)

theorem realize_put (old : A → W) (p : A → Option W) (a : A) (v : W) :
    realize old (put p a (some v)) = put (realize old p) a v := by
  funext i
  by_cases eq : i = a <;> simp [put, realize, eq]

inductive Event (A W : Type) where
  | read (addr : A) (reply : W)
  | write (addr : A) (value : W)

/-- A transcript is genuine if each read has the current value, including after writes. -/
def trueTrace (mem : A → W) : List (Event A W) → Prop
  | [] => True
  | .read a v :: rest => mem a = v ∧ trueTrace mem rest
  | .write a v :: rest => trueTrace (put mem a v) rest

/-- Write and read results stay local to this fork. Only an absent private
word requires a read of the frozen master. -/
def cachedTrace (old : A → W) (p : A → Option W) : List (Event A W) → Prop
  | [] => True
  | .read a v :: rest => realize old p a = v ∧ cachedTrace old (put p a (some v)) rest
  | .write a v :: rest => cachedTrace old (put p a (some v)) rest

theorem fork_exact (old : A → W) (p : A → Option W) (events : List (Event A W)) :
    cachedTrace old p events ↔ trueTrace (realize old p) events := by
  induction events generalizing p with
  | nil => rfl
  | cons ev rest ih =>
    cases ev with
    | write a v => simp only [cachedTrace, trueTrace, ih, realize_put]
    | read a v =>
      simp only [cachedTrace, trueTrace, ih, realize_put]
      apply and_congr_right
      intro value
      have keep : put (realize old p) a v = realize old p := by
        funext i
        by_cases same : i = a <;> simp [put, same, value]
      rw [keep]

def charges (p : A → Option W) : List (Event A W) → List A
  | [] => []
  | .read a v :: rest =>
    let later := charges (put p a (some v)) rest
    if (p a).isNone then a :: later else later
  | .write a v :: rest => charges (put p a (some v)) rest

theorem already_private (p : A → Option W) (events : List (Event A W))
    {a : A} (present : (p a).isSome) : a ∉ charges p events := by
  induction events generalizing p with
  | nil => simp [charges]
  | cons ev rest ih =>
    have after (i : A) (v : W) : ((put p i (some v)) a).isSome := by
      by_cases same : a = i <;> simp [put, same, present]
    cases ev with
    | write i v => exact ih _ (after i v)
    | read i v =>
      simp only [charges]
      split <;> rename_i h
      · have diff : a ≠ i := by
          intro eq
          subst i
          cases ea : p a <;> simp [ea] at present h
        simpa [diff] using ih _ (after i v)
      · exact ih _ (after i v)

theorem charges_distinct (p : A → Option W) (events : List (Event A W)) :
    (charges p events).Nodup := by
  induction events generalizing p with
  | nil => simp [charges]
  | cons ev rest ih =>
    cases ev with
    | write i v => exact ih _
    | read i v =>
      simp only [charges]
      split
      · exact List.nodup_cons.mpr ⟨already_private _ _ (by simp [put]), ih _⟩
      · exact ih _
end Work
end StoppedDisjointnessFork
