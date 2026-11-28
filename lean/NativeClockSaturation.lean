import Std

/-! The compact finite censuses in upstream-checks/cycle-clock/SevenImageDefs.lean,
SevenImageVerify.lean and SevenImageCompact.lean use the pruning criterion below.
The mathematical statement is proved in an abstract writable-memory tree model.
The correspondence between the packed 21-lane Boolean test and the hypotheses
of this theorem is justified separately in the census manuscript. -/

namespace SaturationTree

variable {Addr Word Reg : Type} [DecidableEq Addr]

/-- Unrolled computations with arbitrary pure register updates and predicates
    and writable memory. The verdict at every terminal is fixed. -/
inductive Program (Addr Word Reg : Type) where
  | stop (verdict : Bool)
  | pureStep (f : Reg → Reg) (next : Program Addr Word Reg)
  | load (a : Reg → Addr) (k : Reg → Word → Reg) (next : Program Addr Word Reg)
  | store (a : Reg → Addr) (v : Reg → Word) (next : Program Addr Word Reg)
  | branch (g : Reg → Bool) (t e : Program Addr Word Reg)

local notation "Prog" => Program Addr Word Reg

structure Trace (Addr : Type) where
  verdict : Bool
  guarded : Bool
  reads : List Addr

def overwrite (mem : Addr → Word) (a : Addr) (v : Word) (b : Addr) : Word :=
  if b = a then v else mem b

/-- The recorded reads are precisely those before the last executed guard. -/
def run : Prog → Reg → (Addr → Word) → Trace Addr
  | .stop b, _, _ => ⟨b, false, []⟩
  | .pureStep f p, s, m => run p (f s) m
  | .store a v p, s, m => run p s (overwrite m (a s) (v s))
  | .load a k p, s, m =>
      let t := run p (k s (m (a s))) m
      if t.guarded then {t with reads := a s :: t.reads} else t
  | .branch g t e, s, m =>
      let r := if g s then run t s m else run e s m
      {r with guarded := true}

/-- Unguarded suffixes can never change a terminal, even if all registers and
    all cells change. -/
theorem no_guard (p : Prog) (s : Reg) (m : Addr → Word) :
    (run p s m).guarded = false →
    ∀ (r : Reg) (n : Addr → Word), run p r n = run p s m := by
  induction p generalizing s m with
  | stop v => intros; rfl
  | pureStep f p ih => exact fun h r n => ih _ _ h _ _
  | store a v p ih => exact fun h r n => ih _ _ h _ _
  | branch g t e it ie => simp [run]
  | load a k p ih =>
    intro h r n
    simp only [run] at h ⊢
    generalize eq : run p (k s (m (a s))) m = w at h ⊢
    cases hguard : w.guarded with
    | true => simp [hguard] at h
    | false =>
      have u := ih _ _ (by rw [eq]; exact hguard) (k r (n (a r))) n
      rw [eq] at u
      simp [u,hguard]

/-- An opponent agreeing on the listed old cells and initial registers
    reaches the same verdict, also after indirect probes and stores. -/
theorem agreement (p : Prog) (s : Reg) (m n : Addr → Word) :
    (∀ a ∈ (run p s m).reads, m a = n a) → run p s m = run p s n := by
  induction p generalizing s m n with
  | stop v => intros; rfl
  | pureStep f p ih => exact ih _ _ _
  | store a v p ih =>
    intro h
    apply ih
    intro b hb
    by_cases eq : b = a s
    · simp [overwrite, eq]
    · simp [overwrite, eq, h b hb]
  | branch g t e it ie =>
    intro h
    cases hg : g s <;> simp only [run,hg,Bool.false_eq_true,ite_false,ite_true] at h ⊢
    · rw [ie _ _ _ h]
    · rw [it _ _ _ h]
  | load a k p ih =>
    intro h
    let r := run p (k s (m (a s))) m
    have hr : run p (k s (m (a s))) m = r := rfl
    cases hg : r.guarded with
    | false =>
      have hu := no_guard p _ _ (hr ▸ hg) (k s (n (a s))) n
      simp [run, hu, hr, hg]
    | true =>
      have hs : m (a s) = n (a s) := h _ (by simp [run,hr,hg])
      have tail := ih (k s (m (a s))) m n
        (fun b hb => h b (by simpa [run,hr,hg] using List.mem_cons_of_mem (a s) hb))
      simp [run,← hs,tail]

def height : Prog → Nat
  | .stop _ => 0
  | .pureStep _ p | .store _ _ p | .load _ _ p => height p + 1
  | .branch _ p q => max (height p) (height q) + 1

def isLoad : Prog → Bool
  | .load .. => true
  | _ => false

/-- Any guarded path reserves a tick for its last guard. -/
theorem count_bound (p : Prog) (s : Reg) (m : Addr → Word) :
    (run p s m).reads.length + (if (run p s m).guarded then 1 else 0) ≤ height p := by
  induction p generalizing s m with
  | stop v => simp [run,height]
  | pureStep f p ih => exact Nat.le_succ_of_le (ih _ _)
  | store a v p ih => exact Nat.le_succ_of_le (ih _ _)
  | load a k p ih =>
    have h := ih (k s (m (a s))) m
    cases hg : (run p (k s (m (a s))) m).guarded <;> simp [run,height,hg] at * <;> omega
  | branch g t e it ie =>
    have ht := it s m
    have he := ie s m
    cases hg : g s <;> simp [run,height,hg] <;> omega

theorem unguarded_reads (p : Prog) (s : Reg) (m : Addr → Word)
    (h : (run p s m).guarded = false) : (run p s m).reads = [] := by
  induction p generalizing s m with
  | stop v => rfl
  | pureStep f p ih => exact ih _ _ h
  | store a v p ih => exact ih _ _ h
  | branch g t e it ie => simp [run] at h
  | load a k p ih =>
    have hg : (run p (k s (m (a s))) m).guarded = false := by
      cases hx : (run p (k s (m (a s))) m).guarded <;> simp [run,hx] at h ⊢
    simp [run,hg,ih _ _ hg]

theorem positive_bound (p : Prog) (s : Reg) (m : Addr → Word)
    (h : 0 < (run p s m).reads.length) : (run p s m).reads.length + 1 ≤ height p := by
  have hx := count_bound p s m
  cases hg : (run p s m).guarded
  · simp [unguarded_reads p s m hg] at h
  · simpa [hg] using hx

theorem nonload_cost (p : Prog) (s : Reg) (m : Addr → Word) (hn : isLoad p = false)
    (h : 0 < (run p s m).reads.length) : (run p s m).reads.length + 2 ≤ height p := by
  cases p with
  | stop v => simp [run] at h
  | load a k p => simp [isLoad] at hn
  | pureStep f p => exact Nat.succ_le_succ (positive_bound p _ _ h)
  | store a v p => exact Nat.succ_le_succ (positive_bound p _ _ h)
  | branch g t e =>
    cases hg : g s <;> simp [run,height,hg] at h ⊢
    · have he := positive_bound e s m h; omega
    · have ht := positive_bound t s m h; omega

/-- The universal old-cell test justifies searching only successor LOADs at a
    saturated node, including for computations that overwrite the input. -/
theorem saturated_forces_load (p : Prog) (s : Reg) (m : Addr → Word) (k : Nat)
    (rivals : (Addr → Word) → Prop)
    (hard : ∀ cells : List Addr, cells.length ≤ k →
      ∃ n, rivals n ∧ ∀ a ∈ cells, m a = n a)
    (correct : ∀ n, rivals n → (run p s m).verdict ≠ (run p s n).verdict)
    (clock : height p ≤ k+2) : isLoad p = true := by
  have more : k < (run p s m).reads.length := by
    apply Nat.lt_of_not_ge
    intro short
    obtain ⟨n,hr,agree⟩ := hard (run p s m).reads short
    exact correct n hr (congrArg Trace.verdict (agreement p s m n agree))
  cases h : isLoad p with
  | true => rfl
  | false =>
    have cost := nonload_cost p s m h (by omega)
    omega

end SaturationTree
