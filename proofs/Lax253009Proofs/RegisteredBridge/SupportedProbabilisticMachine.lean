import Lax666725.ProbabilisticMachines
import Lax253009Proofs.RegisteredBridge.Time

set_option backward.isDefEq.respectTransparency false

namespace Lax253009Proofs.RegisteredBridge.SupportedProbabilisticMachine

open Turing Lax666725.ProbabilisticMachines

/-- An intermediate compiler output may use an infinite syntactic control
type, provided one fixed finite set contains every reachable state. -/
structure Supported where
  Γ : Type
  Q : Type
  [alphabet : Fintype Γ]
  [blank : Inhabited Γ]
  [initial : Inhabited Q]
  input : Bool ↪ Γ
  input_ne_blank : ∀ b, input b ≠ default
  transition : Bool → TM0.Machine Γ Q
  same_halts : ∀ q a, transition false q a = none ↔ transition true q a = none
  support : Finset Q
  supports : ∀ b, TM0.Supports (transition b) (support : Set Q)

attribute [instance] Supported.alphabet Supported.blank Supported.initial

variable (M : Supported)

instance controlInhabited : Inhabited {q : M.Q // q ∈ M.support} :=
  ⟨⟨default, (M.supports false).1⟩⟩

noncomputable def transition (b : Bool) (q : {q : M.Q // q ∈ M.support}) (a : M.Γ) :
    Option ({q : M.Q // q ∈ M.support} × TM0.Stmt M.Γ) :=
  match h : M.transition b q.val a with
  | none => none
  | some r => some (⟨r.1, (M.supports b).2 h q.property⟩, r.2)

theorem transition_decode (b : Bool) (q : {q : M.Q // q ∈ M.support}) (a : M.Γ) :
    (transition M b q a).map (fun r ↦ (r.1.val, r.2)) = M.transition b q.val a := by
  unfold transition
  split <;> simp_all

noncomputable def restrict : Machine where
  Γ := M.Γ
  Q := {q : M.Q // q ∈ M.support}
  control := Fintype.ofFinite _
  input := M.input
  input_ne_blank := M.input_ne_blank
  transition := transition M
  same_halts := by
    intro q a
    rw [← Option.map_eq_none_iff (f := fun r : {q : M.Q // q ∈ M.support} × TM0.Stmt M.Γ ↦ (r.1.val, r.2)),
      transition_decode, M.same_halts]
    rw [← transition_decode M true q a, Option.map_eq_none_iff]

def decode (c : TM0.Cfg M.Γ {q : M.Q // q ∈ M.support}) : TM0.Cfg M.Γ M.Q :=
  ⟨c.q.val, c.Tape⟩

theorem step_decode (b : Bool) (c : TM0.Cfg M.Γ {q : M.Q // q ∈ M.support}) :
    (TM0.step ((restrict M).transition b) c).map (decode M) =
      TM0.step (M.transition b) (decode M c) := by
  rcases c with ⟨q, T⟩
  change (TM0.step (transition M b) ⟨q, T⟩).map (decode M) =
    TM0.step (M.transition b) ⟨q.val, T⟩
  simp only [TM0.step]
  rw [← transition_decode M b q T.head]
  simp only [Option.map_map]
  rfl

def advance (c : TM0.Cfg M.Γ M.Q) (b : Bool) : TM0.Cfg M.Γ M.Q :=
  (TM0.step (M.transition b) c).getD c

theorem advance_decode (c : TM0.Cfg M.Γ {q : M.Q // q ∈ M.support}) (b : Bool) :
    decode M ((restrict M).advance c b) = advance M (decode M c) b := by
  unfold Machine.advance advance
  rw [← step_decode M b c]
  cases TM0.step ((restrict M).transition b) c <;> rfl

theorem fold_decode (coins : List Bool) (c : TM0.Cfg M.Γ {q : M.Q // q ∈ M.support}) :
    decode M (coins.foldl (restrict M).advance c) = coins.foldl (advance M) (decode M c) := by
  induction coins generalizing c with
  | nil => rfl
  | cons b coins ih => simp only [List.foldl_cons, ih, advance_decode]

def run (x coins : List Bool) : TM0.Cfg M.Γ M.Q :=
  coins.foldl (advance M) (TM0.init (x.map M.input))

theorem run_decode (x coins : List Bool) :
    decode M ((restrict M).run x coins) = run M x coins :=
  fold_decode M coins (TM0.init (x.map M.input))

noncomputable def procedure {α : Type} (time : Polynomial ℕ) (output : M.Q → α)
    (halts : ∀ (x : List Bool) (r : Fin (time.eval x.length) → Bool),
      TM0.step (M.transition false) (run M x (List.ofFn r)) = none) : Procedure α where
  machine := restrict M
  time := time
  output q := output q.val
  halts := by
    intro x r
    have h := step_decode M false ((restrict M).run x (List.ofFn r))
    rw [run_decode, halts] at h
    exact Option.map_eq_none_iff.mp h

theorem procedure_eval {α : Type} (time : Polynomial ℕ) (output : M.Q → α)
    (halts : ∀ (x : List Bool) (r : Fin (time.eval x.length) → Bool),
      TM0.step (M.transition false) (run M x (List.ofFn r)) = none)
    (x : List Bool) (r : Fin (time.eval x.length) → Bool) :
    (procedure M time output halts).eval x r = output (run M x (List.ofFn r)).q := by
  have h := congrArg TM0.Cfg.q (run_decode M x (List.ofFn r))
  exact congrArg output h

end Lax253009Proofs.RegisteredBridge.SupportedProbabilisticMachine
