import Lax323828Proofs.RegisteredBridge.StackSubroutine
import Lax323828Proofs.RegisteredBridge.FairExecution

set_option backward.isDefEq.respectTransparency false

namespace Lax323828Proofs.RegisteredBridge.StackSubroutine

open Turing Time FairExecution

variable {K J Λ Λ' σ τ : Type} {Γ : K → Type} {Δ : J → Type}
variable [DecidableEq K] [DecidableEq J]

theorem deterministic_run (v : Lens σ τ) (label : Λ → Λ') (exit : Λ')
    (M : Λ → TM2.Stmt Γ Λ σ) (N : Bool → Λ' → TM2.Stmt (Alphabet Γ Δ) Λ' τ)
    (hN : ∀ bit l, N bit (label l) = lift v label exit (M l))
    (t : τ) (T : ∀ j, List (Δ j)) {n : ℕ} {a b : TM2.Cfg Γ Λ σ}
    (h : Run (TM2.step M) n a b) :
    DeterministicRun (fun c bit ↦ (TM2.step (N bit) c).getD c) n
      (config v label exit t T a) (config v label exit t T b) := by
  induction h with
  | zero => exact .zero _
  | @cons n a b c hs h ih =>
    refine .cons (fun bit ↦ ?_) ih
    have hr := run v label exit M (N bit) (hN bit) t T (Run.one hs)
    have he : TM2.step (N bit) (config v label exit t T a) = some (config v label exit t T b) := by
      cases hr with
      | cons hstep htail => cases htail; exact hstep
    simp only [he, Option.getD_some]

theorem deterministic_run_right (v : Lens σ τ) (label : Λ → Λ') (exit : Λ')
    (M : Λ → TM2.Stmt Γ Λ σ) (N : Bool → Λ' → TM2.Stmt (Alphabet Δ Γ) Λ' τ)
    (hN : ∀ bit l, N bit (label l) = liftRight v label exit (M l))
    (t : τ) (T : ∀ j, List (Δ j)) {n : ℕ} {a b : TM2.Cfg Γ Λ σ}
    (h : Run (TM2.step M) n a b) :
    DeterministicRun (fun c bit ↦ (TM2.step (N bit) c).getD c) n
      (configRight v label exit t T a) (configRight v label exit t T b) := by
  induction h with
  | zero => exact .zero _
  | @cons n a b c hs h ih =>
    refine .cons (fun bit ↦ ?_) ih
    have hr := runRight v label exit M (N bit) (hN bit) t T (Run.one hs)
    have he : TM2.step (N bit) (configRight v label exit t T a) =
        some (configRight v label exit t T b) := by
      cases hr with
      | cons hstep htail => cases htail; exact hstep
    simp only [he, Option.getD_some]

end Lax323828Proofs.RegisteredBridge.StackSubroutine
