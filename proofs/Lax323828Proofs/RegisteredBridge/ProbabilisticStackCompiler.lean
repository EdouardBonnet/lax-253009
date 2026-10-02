import Lax323828Proofs.RegisteredBridge.RandomSingleTape
import Lax323828Proofs.RegisteredBridge.RandomStackTape
import Lax323828Proofs.RegisteredBridge.ProbabilisticBoot

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax323828Proofs.RegisteredBridge.ProbabilisticStackCompiler

open Turing SupportedProbabilisticMachine
open scoped Classical

variable {K Λ σ : Type} {Γ : K → Type}
variable [Fintype K] [DecidableEq K] [∀ k, Fintype (Γ k)]
variable [Fintype Λ] [Inhabited Λ] [Fintype σ] [Inhabited σ]
variable (M : Bool → Λ → TM2.Stmt Γ Λ σ) (inputStack : K) (input : Bool ↪ Γ inputStack)

/-- Raw input occupies the input track without a bottom marker; the boot
transition inserts that marker in one deterministic write. -/
def rawInput : Bool ↪ TM2to1.Γ' K Γ where
  toFun b := (false, Function.update (fun _ ↦ none) inputStack (some (input b)))
  inj' := by
    intro b c h
    have h' := congrArg (fun a : TM2to1.Γ' K Γ ↦ a.2 inputStack) h
    simp only [Function.update_self, Option.some.injEq] at h'
    exact input.injective h'

theorem rawInput_ne_blank (b : Bool) : rawInput inputStack input b ≠ default := by
  intro h
  have h' := congrArg (fun a : TM2to1.Γ' K Γ ↦ a.2 inputStack) h
  simp [rawInput] at h'

def mark (a : TM2to1.Γ' K Γ) : TM2to1.Γ' K Γ := (true, a.2)

noncomputable def core : Supported :=
  RandomSingleTape.machine (fun bit ↦ TM2to1.tr (M bit)) (RandomStackTape.support M)
    (RandomStackTape.supports M) (rawInput inputStack input) (rawInput_ne_blank inputStack input)

noncomputable def machine : Supported := ProbabilisticBoot.machine (core M inputStack input) mark

def sourceInitial (x : List Bool) : TM2.Cfg Γ Λ σ :=
  TM2.init inputStack (x.reverse.map input)

def tapeInitial (x : List Bool) : TM1.Cfg (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ :=
  TM1.init (TM2to1.trInit inputStack (x.reverse.map input))

theorem initial_config (x : List Bool) :
    ProbabilisticBoot.initial (core M inputStack input) mark x =
      RandomSingleTape.config (tapeInitial inputStack input x) := by
  change TM0.Cfg.mk _ ((Tape.mk₁ (x.map (rawInput inputStack input))).write
      (mark (Tape.mk₁ (x.map (rawInput inputStack input))).head)) =
    TM0.Cfg.mk _ (Tape.mk₁ (TM2to1.trInit inputStack (x.reverse.map input)))
  congr 1
  simp only [TM2to1.trInit, ← List.map_reverse, List.reverse_reverse, List.map_map]
  cases x with
  | nil => rfl
  | cons b x =>
    simp only [List.map_cons, List.headI_cons, List.tail_cons]
    rfl

noncomputable def tapeClock (p : Polynomial ℕ) : Polynomial ℕ :=
  p * (1 + Polynomial.C (RandomStackTape.growth M) *
    (2 * (Polynomial.X + Polynomial.C (RandomStackTape.growth M) * (p + 1)) + 2))

noncomputable def clock (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (RandomSingleTape.cost (fun bit ↦ TM2to1.tr (M bit))
    (RandomStackTape.support M)) * tapeClock M p + 1

theorem tapeClock_eval (p : Polynomial ℕ) (n : ℕ) :
    (tapeClock M p).eval n =
      (1 + RandomStackTape.growth M * (2 * (n + RandomStackTape.growth M * (p.eval n + 1)) + 2)) *
        p.eval n := by
  simp [tapeClock, Nat.mul_comm]

theorem clock_eval (p : Polynomial ℕ) (n : ℕ) :
    (clock M p).eval n = RandomSingleTape.cost (fun bit ↦ TM2to1.tr (M bit))
      (RandomStackTape.support M) * (tapeClock M p).eval n + 1 := by simp [clock]

theorem initial_bound (x : List Bool) (k : K) :
    ((sourceInitial inputStack input x : TM2.Cfg Γ Λ σ).stk k).length ≤ x.length := by
  by_cases h : k = inputStack
  · subst k; simp [sourceInitial, TM2.init]
  · simp [sourceInitial, TM2.init, Function.update_of_ne h]

theorem core_simulation {α : Type} (out : σ → α) (p : Polynomial ℕ) (x : List Bool)
    (hn : ∀ r : Fin (p.eval x.length) → Bool,
      ((List.ofFn r).foldl (RandomStackTape.sourceAdvance M) (sourceInitial inputStack input x)).l = none) :
    (∀ r : Fin (RandomSingleTape.cost (fun bit ↦ TM2to1.tr (M bit)) (RandomStackTape.support M) * (tapeClock M p).eval x.length) → Bool,
      TM0.step ((core M inputStack input).transition false)
        ((List.ofFn r).foldl (advance (core M inputStack input))
          (ProbabilisticBoot.initial (core M inputStack input) mark x)) = none) ∧
    (∀ P : α → Prop,
      Lax323828.FiniteProbability.probability (fun r : Fin (RandomSingleTape.cost (fun bit ↦ TM2to1.tr (M bit)) (RandomStackTape.support M) * (tapeClock M p).eval x.length) → Bool ↦
        P (out ((List.ofFn r).foldl (advance (core M inputStack input))
          (ProbabilisticBoot.initial (core M inputStack input) mark x)).q.2)) =
      Lax323828.FiniteProbability.probability (fun r : Fin (p.eval x.length) → Bool ↦
        P (out ((List.ofFn r).foldl (RandomStackTape.sourceAdvance M)
          (sourceInitial inputStack input x)).var))) := by
  have hs := RandomStackTape.uniform_simulation M out (sourceInitial inputStack input x)
    (tapeInitial inputStack input x) (TM2to1.trCfg_init inputStack (x.reverse.map input))
    x.length (p.eval x.length) ((tapeClock M p).eval x.length)
    (initial_bound inputStack input x) (by rw [tapeClock_eval]) hn
  have ht := RandomSingleTape.uniform_simulation (fun bit ↦ TM2to1.tr (M bit))
    (RandomStackTape.support M) (RandomStackTape.supports M) out
    (tapeInitial inputStack input x)
    (Finset.some_mem_insertNone.mpr (RandomStackTape.supports M false).1)
    ((tapeClock M p).eval x.length) (RandomSingleTape.cost (fun bit ↦ TM2to1.tr (M bit)) (RandomStackTape.support M) * (tapeClock M p).eval x.length)
    le_rfl hs.1
  rw [initial_config]
  exact ⟨ht.1, fun P ↦ (ht.2 P).trans (hs.2 P)⟩

theorem halts (p : Polynomial ℕ)
    (hn : ∀ (x : List Bool) (r : Fin (p.eval x.length) → Bool),
      ((List.ofFn r).foldl (RandomStackTape.sourceAdvance M) (sourceInitial inputStack input x)).l = none) :
    ∀ (x : List Bool) (r : Fin ((clock M p).eval x.length) → Bool),
      TM0.step ((machine M inputStack input).transition false)
        (run (machine M inputStack input) x (List.ofFn r)) = none := by
  intro x
  have hh := ProbabilisticBoot.halts (core M inputStack input) mark x
    (RandomSingleTape.cost (fun bit ↦ TM2to1.tr (M bit)) (RandomStackTape.support M) * (tapeClock M p).eval x.length)
    (core_simulation M inputStack input (fun _ ↦ ()) p x (hn x)).1
  rw [clock_eval]
  exact hh

noncomputable def procedure {α : Type} (out : σ → α) (p : Polynomial ℕ)
    (hn : ∀ (x : List Bool) (r : Fin (p.eval x.length) → Bool),
      ((List.ofFn r).foldl (RandomStackTape.sourceAdvance M) (sourceInitial inputStack input x)).l = none) :
    Lax666725.ProbabilisticMachines.Procedure α :=
  SupportedProbabilisticMachine.procedure (machine M inputStack input) (clock M p)
    (fun q ↦ out (q.getD default).2) (halts M inputStack input p hn)

theorem probability_real {α : Type} (A : Lax666725.ProbabilisticMachines.Procedure α)
    (x : List Bool) (P : α → Prop) :
    (A.probability x P : ℝ) =
      Lax323828.FiniteProbability.probability (fun r : A.Coins x ↦ P (A.eval x r)) := by
  simp only [Lax666725.ProbabilisticMachines.Procedure.probability,
    Lax323828.FiniteProbability.probability, Rat.cast_div, Rat.cast_natCast]

theorem procedure_probability {α : Type} (out : σ → α) (p : Polynomial ℕ)
    (hn : ∀ (x : List Bool) (r : Fin (p.eval x.length) → Bool),
      ((List.ofFn r).foldl (RandomStackTape.sourceAdvance M) (sourceInitial inputStack input x)).l = none)
    (x : List Bool) (P : α → Prop) :
    ((procedure M inputStack input out p hn).probability x P : ℝ) =
      Lax323828.FiniteProbability.probability (fun r : Fin (p.eval x.length) → Bool ↦
        P (out ((List.ofFn r).foldl (RandomStackTape.sourceAdvance M)
          (sourceInitial inputStack input x)).var)) := by
  rw [probability_real]
  change Lax323828.FiniteProbability.probability (fun r : Fin ((clock M p).eval x.length) → Bool ↦
    P ((procedure M inputStack input out p hn).eval x r)) = _
  simp only [procedure, SupportedProbabilisticMachine.procedure_eval]
  rw [clock_eval]
  have hp := ProbabilisticBoot.probability (core M inputStack input) mark
    (fun q ↦ out q.2) P x (RandomSingleTape.cost (fun bit ↦ TM2to1.tr (M bit)) (RandomStackTape.support M) * (tapeClock M p).eval x.length)
  exact hp.trans ((core_simulation M inputStack input out p x (hn x)).2 P)

end Lax323828Proofs.RegisteredBridge.ProbabilisticStackCompiler
