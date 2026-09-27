import Lax253009Proofs.RegisteredBridge.SingleTapeRuntime
import Lax253009Proofs.RegisteredBridge.FairExecution
import Lax253009Proofs.RegisteredBridge.SupportedProbabilisticMachine

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax253009Proofs.RegisteredBridge.RandomSingleTape

open Turing FairExecution SingleTapeRuntime
open scoped BigOperators Classical

variable {Γ Λ σ : Type}

/-- A ready state draws the next source coin. Execution of the selected
statement is deterministic until the next ready state. -/
def State (Γ Λ σ : Type) := (Option Λ ⊕ TM1.Stmt Γ Λ σ) × σ

instance [Inhabited Λ] [Inhabited σ] : Inhabited (State Γ Λ σ) :=
  ⟨(.inl (some default), default)⟩

def bodyTransition (a : Γ) : TM1.Stmt Γ Λ σ → σ → State Γ Λ σ × TM0.Stmt Γ
  | .move d q, v => ((.inr q, v), .move d)
  | .write f q, v => ((.inr q, v), .write (f a v))
  | .load f q, v => bodyTransition a q (f a v)
  | .branch p q r, v => if p a v then bodyTransition a q v else bodyTransition a r v
  | .goto l, v => ((.inl (some (l a v)), v), .write a)
  | .halt, v => ((.inl none, v), .write a)

variable [Inhabited Λ] [Inhabited σ]

def transition (M : Bool → Λ → TM1.Stmt Γ Λ σ) (bit : Bool) :
    TM0.Machine Γ (State Γ Λ σ)
  | (.inl none, _), _ => none
  | (.inl (some l), v), a => some ((.inr (M bit l), v), .write a)
  | (.inr q, v), a => some (bodyTransition a q v)

variable [Inhabited Γ]

def advance (M : Bool → Λ → TM1.Stmt Γ Λ σ)
    (c : TM0.Cfg Γ (State Γ Λ σ)) (bit : Bool) :=
  (TM0.step (transition M bit) c).getD c

def config (c : TM1.Cfg Γ Λ σ) : TM0.Cfg Γ (State Γ Λ σ) :=
  ⟨(.inl c.l, c.var), c.Tape⟩

theorem body_run (M : Bool → Λ → TM1.Stmt Γ Λ σ) (q : TM1.Stmt Γ Λ σ)
    (v : σ) (T : Tape Γ) :
    ∃ n, 0 < n ∧ n ≤ blockCost q ∧
      DeterministicRun (advance M) n ⟨(.inr q, v), T⟩
        (config (TM1.stepAux q v T)) := by
  induction q generalizing v T with
  | move d q ih =>
    obtain ⟨n, hn, hc, hr⟩ := ih v (T.move d)
    exact ⟨n + 1, by omega, by simpa [blockCost] using Nat.add_le_add_right hc 1,
      .cons (fun _ ↦ rfl) hr⟩
  | write f q ih =>
    obtain ⟨n, hn, hc, hr⟩ := ih v (T.write (f T.head v))
    exact ⟨n + 1, by omega, by simpa [blockCost] using Nat.add_le_add_right hc 1,
      .cons (fun _ ↦ rfl) hr⟩
  | load f q ih =>
    obtain ⟨n, hn, hc, hr⟩ := ih (f T.head v) T
    exact ⟨n, hn, hc, hr.of_step_eq hn (fun _ ↦ rfl)⟩
  | branch p q r ihq ihr =>
    cases hp : p T.head v
    · obtain ⟨n, hn, hc, hr⟩ := ihr v T
      refine ⟨n, hn, hc.trans (Nat.le_max_right _ _), ?_⟩
      simp only [TM1.stepAux, hp, Bool.cond_false]
      exact hr.of_step_eq hn (fun bit ↦ by
        simp [advance, TM0.step, transition, bodyTransition, hp])
    · obtain ⟨n, hn, hc, hr⟩ := ihq v T
      refine ⟨n, hn, hc.trans (Nat.le_max_left _ _), ?_⟩
      simp only [TM1.stepAux, hp, Bool.cond_true]
      exact hr.of_step_eq hn (fun bit ↦ by
        simp [advance, TM0.step, transition, bodyTransition, hp])
  | goto l =>
    refine ⟨1, by decide, le_rfl, .one (fun bit ↦ ?_)⟩
    simp [advance, TM0.step, transition, bodyTransition, config, TM1.stepAux, Tape.write_self]
  | halt =>
    refine ⟨1, by decide, le_rfl, .one (fun bit ↦ ?_)⟩
    simp [advance, TM0.step, transition, bodyTransition, config, TM1.stepAux, Tape.write_self]

def sourceAdvance (M : Bool → Λ → TM1.Stmt Γ Λ σ) (c : TM1.Cfg Γ Λ σ) (bit : Bool) :=
  (TM1.step (M bit) c).getD c

noncomputable def cost (M : Bool → Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) : ℕ :=
  machineCost (M false) S + machineCost (M true) S + 1

theorem cost_pos (M : Bool → Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) : 0 < cost M S :=
  Nat.zero_lt_succ _

theorem step_simulation (M : Bool → Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (a : TM1.Cfg Γ Λ σ) (ha : a.l ∈ Finset.insertNone S) (bit : Bool) :
    ∃ n, n < cost M S ∧ DeterministicRun (advance M) n
      (advance M (config a) bit) (config (sourceAdvance M a bit)) := by
  rcases a with ⟨l, v, T⟩
  cases l with
  | none => exact ⟨0, cost_pos M S, .zero _⟩
  | some l =>
    have hl := Finset.some_mem_insertNone.mp ha
    obtain ⟨n, hn, hc, hr⟩ := body_run M (M bit l) v T
    have hsum : blockCost (M bit l) ≤ machineCost (M bit) S :=
      Finset.single_le_sum (f := fun j ↦ blockCost (M bit j))
        (fun _ _ ↦ Nat.zero_le _) hl
    refine ⟨n, ?_, ?_⟩
    · cases bit <;> simp only [cost] <;> omega
    · simpa [advance, config, TM0.step, transition, Tape.write_self,
        sourceAdvance, TM1.step] using hr

noncomputable def commands (M : Bool → Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) :
    Finset (TM1.Stmt Γ Λ σ) :=
  (S.biUnion fun l ↦ TM1.stmts₁ (M false l)) ∪
  (S.biUnion fun l ↦ TM1.stmts₁ (M true l))

theorem command_mem (M : Bool → Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (bit : Bool) (l : Λ) (hl : l ∈ S) : M bit l ∈ commands M S := by
  cases bit <;> simp only [commands, Finset.mem_union, Finset.mem_biUnion]
  · exact Or.inl ⟨l, hl, TM1.stmts₁_self⟩
  · exact Or.inr ⟨l, hl, TM1.stmts₁_self⟩

theorem commands_closed {M : Bool → Λ → TM1.Stmt Γ Λ σ} {S : Finset Λ}
    {q r : TM1.Stmt Γ Λ σ} (hq : q ∈ commands M S) (hr : r ∈ TM1.stmts₁ q) :
    r ∈ commands M S := by
  simp only [commands, Finset.mem_union, Finset.mem_biUnion] at hq ⊢
  rcases hq with ⟨l, hl, hq⟩ | ⟨l, hl, hq⟩
  · exact Or.inl ⟨l, hl, TM1.stmts₁_trans hq hr⟩
  · exact Or.inr ⟨l, hl, TM1.stmts₁_trans hq hr⟩

theorem commands_support {M : Bool → Λ → TM1.Stmt Γ Λ σ} {S : Finset Λ}
    (hM : ∀ bit, TM1.Supports (M bit) S) {q : TM1.Stmt Γ Λ σ}
    (hq : q ∈ commands M S) : TM1.SupportsStmt S q := by
  simp only [commands, Finset.mem_union, Finset.mem_biUnion] at hq
  rcases hq with ⟨l, hl, hq⟩ | ⟨l, hl, hq⟩
  · exact TM1.stmts₁_supportsStmt_mono hq ((hM false).2 l hl)
  · exact TM1.stmts₁_supportsStmt_mono hq ((hM true).2 l hl)

noncomputable def controls (M : Bool → Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) :
    Finset (Option Λ ⊕ TM1.Stmt Γ Λ σ) :=
  (Finset.insertNone S).image Sum.inl ∪ (commands M S).image Sum.inr

theorem ready_mem (M : Bool → Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (l : Option Λ) (hl : l ∈ Finset.insertNone S) : Sum.inl l ∈ controls M S :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨l, hl, rfl⟩)

theorem body_mem {M : Bool → Λ → TM1.Stmt Γ Λ σ} {S : Finset Λ}
    {q : TM1.Stmt Γ Λ σ} (hq : q ∈ commands M S) : Sum.inr q ∈ controls M S :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)

theorem body_support {M : Bool → Λ → TM1.Stmt Γ Λ σ} {S : Finset Λ}
    (hM : ∀ bit, TM1.Supports (M bit) S) (a : Γ) (q : TM1.Stmt Γ Λ σ)
    (hq : q ∈ commands M S) (v : σ) : (bodyTransition a q v).1.1 ∈ controls M S := by
  induction q generalizing v with
  | move d q =>
    exact body_mem (commands_closed hq (Finset.mem_insert_of_mem TM1.stmts₁_self))
  | write f q =>
    exact body_mem (commands_closed hq (Finset.mem_insert_of_mem TM1.stmts₁_self))
  | load f q ih =>
    exact ih (commands_closed hq (Finset.mem_insert_of_mem TM1.stmts₁_self)) (f a v)
  | branch p q r ihq ihr =>
    cases hp : p a v
    · simp only [bodyTransition, hp, Bool.false_eq_true, ↓reduceIte]
      exact ihr (commands_closed hq (Finset.mem_insert_of_mem
        (Finset.mem_union_right _ TM1.stmts₁_self))) v
    · simp only [bodyTransition, hp, ↓reduceIte]
      exact ihq (commands_closed hq (Finset.mem_insert_of_mem
        (Finset.mem_union_left _ TM1.stmts₁_self))) v
  | goto l =>
    exact ready_mem M S _ (Finset.some_mem_insertNone.mpr (commands_support hM hq a v))
  | halt => exact ready_mem M S none (by simp)

variable [Fintype σ]

noncomputable def states (M : Bool → Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) :
    Finset (State Γ Λ σ) := controls M S ×ˢ Finset.univ

theorem supports (M : Bool → Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (hM : ∀ bit, TM1.Supports (M bit) S) (bit : Bool) :
    TM0.Supports (transition M bit) (states M S : Set (State Γ Λ σ)) := by
  constructor
  · exact Finset.mem_product.mpr ⟨ready_mem M S _
      (Finset.some_mem_insertNone.mpr (hM false).1), Finset.mem_univ _⟩
  · intro q a q' s ht hq
    rcases q with ⟨l | q, v⟩
    · cases l with
      | none => cases ht
      | some l =>
        cases ht
        have hqc := (Finset.mem_product.mp hq).1
        have hl : l ∈ S := by simpa [controls] using hqc
        exact Finset.mem_product.mpr ⟨body_mem (command_mem M S bit l hl), Finset.mem_univ _⟩
    · have he : bodyTransition a q v = (q', s) := Option.some.inj ht
      have hqc := (Finset.mem_product.mp hq).1
      have hc : q ∈ commands M S := by simpa [controls] using hqc
      have hh := Finset.mem_product.mpr ⟨body_support hM a q hc v,
        Finset.mem_univ (bodyTransition a q v).1.2⟩
      simpa only [he, states, Finset.mem_coe] using hh

theorem same_halts (M : Bool → Λ → TM1.Stmt Γ Λ σ) (q : State Γ Λ σ) (a : Γ) :
    transition M false q a = none ↔ transition M true q a = none := by
  rcases q with ⟨l | q, v⟩
  · cases l <;> simp [transition]
  · simp [transition]

variable [Fintype Γ]

noncomputable def machine (M : Bool → Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (hM : ∀ bit, TM1.Supports (M bit) S)
    (input : Bool ↪ Γ) (hi : ∀ b, input b ≠ default) :
    SupportedProbabilisticMachine.Supported where
  Γ := Γ
  Q := State Γ Λ σ
  input := input
  input_ne_blank := hi
  transition := transition M
  same_halts := same_halts M
  support := states M S
  supports := supports M S hM

/-- The instruction compiler preserves the full output distribution and
every-path termination, with a fixed multiplicative time overhead. -/
theorem uniform_simulation {α : Type}
    (M : Bool → Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (hM : ∀ bit, TM1.Supports (M bit) S) (out : σ → α)
    (a : TM1.Cfg Γ Λ σ) (ha : a.l ∈ Finset.insertNone S) (n k : ℕ)
    (hk : cost M S * n ≤ k)
    (hn : ∀ r : Fin n → Bool, ((List.ofFn r).foldl (sourceAdvance M) a).l = none) :
    (∀ r : Fin k → Bool,
      TM0.step (transition M false) ((List.ofFn r).foldl (advance M) (config a)) = none) ∧
    (∀ P : α → Prop,
      Lax253009.FiniteProbability.probability (fun r : Fin k → Bool ↦
        P (out ((List.ofFn r).foldl (advance M) (config a)).q.2)) =
      Lax253009.FiniteProbability.probability (fun r : Fin n → Bool ↦
        P (out ((List.ofFn r).foldl (sourceAdvance M) a).var))) := by
  let R (b : TM1.Cfg Γ Λ σ) (c : TM0.Cfg Γ (State Γ Λ σ)) :=
    b.l ∈ Finset.insertNone S ∧ config b = c
  apply FairExecution.uniform_simulation (sourceAdvance M) (advance M)
    (fun b ↦ out b.var) (fun c ↦ out c.q.2) (fun b ↦ b.l = none)
    (fun c ↦ TM0.step (transition M false) c = none) R (cost M S)
    ?_ ?_ ?_ a (config a) ⟨ha, rfl⟩ n k hk hn
  · intro b hb bit
    cases b
    simp_all [sourceAdvance, TM1.step]
  · intro b c hbc hb
    rcases hbc with ⟨_, rfl⟩
    rcases b with ⟨l, v, T⟩
    dsimp at hb
    subst l
    exact ⟨rfl, fun _ ↦ rfl, rfl⟩
  · intro b c hbc bit
    rcases hbc with ⟨hb, rfl⟩
    obtain ⟨m, hm, hr⟩ := step_simulation M S b hb bit
    refine ⟨config (sourceAdvance M b bit), m, hm, hr, ?_, rfl⟩
    unfold sourceAdvance
    cases hs : TM1.step (M bit) b with
    | none => exact hb
    | some b' => exact TM1.step_supports (M bit) (hM bit) hs hb

end Lax253009Proofs.RegisteredBridge.RandomSingleTape
