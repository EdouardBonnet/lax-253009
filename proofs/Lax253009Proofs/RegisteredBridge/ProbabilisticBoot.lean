import Lax253009Proofs.RegisteredBridge.SupportedProbabilisticMachine
import Lax253009Proofs.RegisteredBridge.FairExecution

set_option backward.isDefEq.respectTransparency false

namespace Lax253009Proofs.RegisteredBridge.ProbabilisticBoot

open Turing SupportedProbabilisticMachine FairExecution
open scoped Classical

variable (M : Supported) (mark : M.Γ → M.Γ)

noncomputable def transition (bit : Bool) : TM0.Machine M.Γ (Option M.Q)
  | none, a => some (some default, .write (mark a))
  | some q, a => (M.transition bit q a).map (fun r ↦ (some r.1, r.2))

/-- A single deterministic initialization write precedes the simulated
machine. Its new initial state is outside the machine's old control. -/
noncomputable def machine : Supported where
  Γ := M.Γ
  Q := Option M.Q
  input := M.input
  input_ne_blank := M.input_ne_blank
  transition := transition M mark
  same_halts := by
    intro q a
    cases q
    · simp [transition]
    · simpa only [transition, Option.map_eq_none_iff] using M.same_halts _ a
  support := Finset.insertNone M.support
  supports := by
    intro bit
    constructor
    · exact Finset.none_mem_insertNone
    · intro q a q' s ht hq
      cases q with
      | none =>
        cases ht
        exact Finset.some_mem_insertNone.mpr (M.supports bit).1
      | some q =>
        obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp ht
        cases he
        exact Finset.some_mem_insertNone.mpr
          ((M.supports bit).2 hr (Finset.some_mem_insertNone.mp hq))

def lift (c : TM0.Cfg M.Γ M.Q) : TM0.Cfg M.Γ (Option M.Q) := ⟨some c.q, c.Tape⟩

theorem step_lift (c : TM0.Cfg M.Γ M.Q) (bit : Bool) :
    TM0.step ((machine M mark).transition bit) (lift M c) =
      (TM0.step (M.transition bit) c).map (lift M) := by
  cases c
  simp only [TM0.step, machine, transition, lift, Option.map_map]
  rfl

theorem advance_lift (c : TM0.Cfg M.Γ M.Q) (bit : Bool) :
    advance (machine M mark) (lift M c) bit = lift M (advance M c bit) := by
  unfold advance
  rw [step_lift]
  cases TM0.step (M.transition bit) c <;> rfl

theorem fold_lift (c : TM0.Cfg M.Γ M.Q) (coins : List Bool) :
    coins.foldl (advance (machine M mark)) (lift M c) =
      lift M (coins.foldl (advance M) c) := by
  induction coins generalizing c with
  | nil => rfl
  | cons bit coins ih => simp only [List.foldl_cons, advance_lift, ih]

def initial (x : List Bool) : TM0.Cfg M.Γ M.Q :=
  let T := Tape.mk₁ (x.map M.input)
  ⟨default, T.write (mark T.head)⟩

theorem first (x : List Bool) (bit : Bool) :
    advance (machine M mark) (TM0.init (x.map (machine M mark).input)) bit =
      lift M (initial M mark x) := rfl

theorem run_cons (x coins : List Bool) (bit : Bool) :
    run (machine M mark) x (bit :: coins) =
      lift M (coins.foldl (advance M) (initial M mark x)) := by
  unfold run
  rw [List.foldl_cons, first, fold_lift]

theorem halts (x : List Bool) (n : ℕ)
    (hn : ∀ r : Fin n → Bool,
      TM0.step (M.transition false) ((List.ofFn r).foldl (advance M) (initial M mark x)) = none) :
    ∀ r : Fin (n + 1) → Bool,
      TM0.step ((machine M mark).transition false)
        (run (machine M mark) x (List.ofFn r)) = none := by
  intro r
  rw [List.ofFn_succ, run_cons, step_lift]
  exact congrArg (Option.map (lift M)) (hn (fun i ↦ r i.succ))

theorem average_lift {α : Type} (out : M.Q → α) (value : α → ℝ)
    (n : ℕ) (c : TM0.Cfg M.Γ M.Q) :
    average (advance (machine M mark)) (fun d ↦ value (out (d.q.getD default))) n (lift M c) =
      average (advance M) (fun d ↦ value (out d.q)) n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [average, advance_lift, ih]

theorem probability {α : Type} (out : M.Q → α) (P : α → Prop) (x : List Bool) (n : ℕ) :
    Lax253009.FiniteProbability.probability (fun r : Fin (n + 1) → Bool ↦
      P (out ((run (machine M mark) x (List.ofFn r)).q.getD default))) =
    Lax253009.FiniteProbability.probability (fun r : Fin n → Bool ↦
      P (out ((List.ofFn r).foldl (advance M) (initial M mark x)).q)) := by
  calc
    _ = average (advance (machine M mark))
        (fun d ↦ if P (out (d.q.getD default)) then 1 else 0) (n + 1)
        (TM0.init (x.map (machine M mark).input)) :=
      (average_indicator (advance (machine M mark))
        (fun d ↦ P (out (d.q.getD default))) (n + 1) _).symm
    _ = average (advance M) (fun d ↦ if P (out d.q) then 1 else 0) n
        (initial M mark x) := by
      rw [average, first, first]
      have h := average_lift M mark out (fun a ↦ if P a then 1 else 0) n (initial M mark x)
      change (_ + _) / 2 = _
      rw [h]
      ring
    _ = _ := average_indicator (advance M) (fun d ↦ P (out d.q)) n (initial M mark x)

end Lax253009Proofs.RegisteredBridge.ProbabilisticBoot
