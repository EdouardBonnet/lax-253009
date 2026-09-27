import Lax253009Proofs.RegisteredBridge.TM2Runtime
import Lax434930.PolynomialTime
import Lax253009Proofs.RegisteredBridge.FiniteAlphabet
import Lax253009Proofs.PCPFoundation.Classes.P.DecisionFn

set_option backward.isDefEq.respectTransparency false

namespace Lax253009Proofs.RegisteredBridge

open PCPFoundation.Complexity Turing
open scoped BigOperators

namespace FiniteEncoding

theorem flatMap_length_bound (f : Bool → List Bool) (z : List Bool) :
    (z.flatMap f).length ≤ ((f false).length + (f true).length) * z.length := by
  induction z with
  | nil => simp
  | cons b z ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
    cases b <;> omega

/-- Replacing each input bit by a fixed word takes polynomial time. -/
theorem flatMap_mem_FP (f : Bool → List Bool) : (fun z ↦ z.flatMap f) ∈ FP := by
  let state := pairSnd ∘ pairFst
  have hstate : state ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  refine recFold_mem_FP_of_bound
    (g := fun _ t ↦ t.flatMap f)
    (Cobham.appendFn_mem_FP (constFn_mem_FP (f false)) hstate)
    (Cobham.appendFn_mem_FP (constFn_mem_FP (f true)) hstate)
    (constFn_mem_FP []) (constFn_mem_FP [])
    (CobhamFP_subset_FP (Cobham.proj (0 : Fin 1)))
    (fun _ ↦ rfl) ?_ ?_
    ((PolyBound.const ((f false).length + (f true).length)).mul PolyBound.id) ?_
  · intro z t
    simp only [state, Function.comp_apply, pairFst_pair, pairSnd_pair, List.flatMap_cons]
  · intro z t
    simp only [state, Function.comp_apply, pairFst_pair, pairSnd_pair, List.flatMap_cons]
  · intro z t ht
    exact (flatMap_length_bound f t).trans (Nat.mul_le_mul_left _ ht.length_le)

theorem packets_map_mem_FP {A : Type} [Fintype A] (f : Bool → A) :
    (fun z ↦ packets (z.map f)) ∈ FP := by
  simpa only [packets, List.flatMap_map, Function.comp_def] using flatMap_mem_FP (packet ∘ f)

end FiniteEncoding

namespace StackEncoding

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

theorem total_step_of_step (M : Λ → TM2.Stmt Γ Λ σ) {c d : TM2.Cfg Γ Λ σ}
    (h : TM2.step M c = some d) : totalStep M c = d := by
  cases c with
  | mk l v s =>
    cases l with
    | none => simp [TM2.step] at h
    | some l => exact Option.some.inj h

theorem total_run_of_run (M : Λ → TM2.Stmt Γ Λ σ) (t : ℕ) {c d : TM2.Cfg Γ Λ σ}
    (h : (fun x : Option (TM2.Cfg Γ Λ σ) ↦ x.bind (TM2.step M))^[t] (some c) = some d) :
    (totalStep M)^[t] c = d := by
  induction t generalizing c with
  | zero => exact Option.some.inj h
  | succ t ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    cases he : TM2.step M c with
    | none =>
      have hn : (fun x : Option (TM2.Cfg Γ Λ σ) ↦ x.bind (TM2.step M))^[t] none = none :=
        Function.iterate_fixed rfl t
      simp only [Option.bind_some, he, hn, reduceCtorEq] at h
    | some e =>
      rw [total_step_of_step M he]
      exact ih (by simpa only [Option.bind_some, he] using h)

theorem total_run_after_halt (M : Λ → TM2.Stmt Γ Λ σ) {c d : TM2.Cfg Γ Λ σ}
    {t m : ℕ}
    (h : (fun x : Option (TM2.Cfg Γ Λ σ) ↦ x.bind (TM2.step M))^[t] (some c) = some d)
    (hd : d.l = none) (ht : t ≤ m) : (totalStep M)^[m] c = d := by
  rw [show m = (m - t) + t from (Nat.sub_add_cancel ht).symm, Function.iterate_add_apply,
    total_run_of_run M t h]
  exact Function.iterate_fixed (by simp [totalStep, hd]) _

end StackEncoding

section FinTM2

open FiniteEncoding StackEncoding

variable (tm : FinTM2)
local instance : Fintype tm.K := tm.kFin
local instance : Fintype tm.Λ := tm.ΛFin
local instance : Fintype tm.σ := tm.σFin
variable [∀ k, Fintype (tm.Γ k)]

theorem init_encode_mem_FP (input : Bool → tm.Γ tm.k₀) :
    (fun z ↦ encode (initList tm (z.map input))) ∈ FP := by
  change (fun z ↦ pair (code (some tm.main, tm.initialState))
    (Cobham.encodeVec fun i : Fin (Fintype.card tm.K) ↦
      packets ((initList tm (z.map input)).stk ((Fintype.equivFin tm.K).symm i)))) ∈ FP
  apply mem_FP_pair (constFn_mem_FP _)
  apply encodeVec_mem_FP
  intro i
  let k := (Fintype.equivFin tm.K).symm i
  change (fun z ↦ packets ((initList tm (z.map input)).stk k)) ∈ FP
  by_cases hk : k = tm.k₀
  · have he := congrArg (fun j : tm.K ↦ fun z : List Bool ↦
        packets ((initList tm (z.map input)).stk j)) hk
    rw [he]
    simpa [initList] using packets_map_mem_FP input
  · simpa only [initList, dif_neg hk, packets_nil] using constFn_mem_FP []

theorem init_stack_length (input : Bool → tm.Γ tm.k₀) (z : List Bool) (k : tm.K) :
    ((initList tm (z.map input)).stk k).length ≤ z.length := by
  by_cases hk : k = tm.k₀
  · subst k; simp [initList]
  · simp [initList, hk]

theorem output_bit_mem_FP (output : tm.Γ tm.k₁ → Bool) :
    (fun z ↦ [(readHead ((stack z tm.k₁).take (Fintype.card (tm.Γ tm.k₁) + 1))).map output
      |>.getD false]) ∈ FP := by
  exact bounded_read_mem_FP (stack_mem_FP tm.k₁) _
    (fun key ↦ [((readHead key).map output).getD false])

theorem output_bit_halt (output : tm.Γ tm.k₁ ≃ Bool) (b : Bool) :
    ((readHead ((stack (encode (haltList tm [output.symm b])) tm.k₁).take
      (Fintype.card (tm.Γ tm.k₁) + 1))).map output).getD false = b := by
  rw [stack_encode, read_head_packets]
  simp [haltList]

end FinTM2

/-- Registered deciders on finite stack alphabets compute an `FP` Boolean flag. -/
theorem flag_mem_FP_of_finite_stack {f : List Bool → Bool}
    (M : TM2ComputableInPolyTime id Computability.encodeBool f)
    (hfinite : ∀ k, Finite (M.tm.Γ k)) : (fun z ↦ [f z]) ∈ FP := by
  classical
  letI : Fintype M.tm.K := M.tm.kFin
  letI : Fintype M.tm.Λ := M.tm.ΛFin
  letI : Fintype M.tm.σ := M.tm.σFin
  letI (k : M.tm.K) : Fintype (M.tm.Γ k) := Fintype.ofFinite (M.tm.Γ k)
  obtain ⟨ruler, hruler, hrlen⟩ := Cobham.exists_ruler M.time
  have hrun := StackEncoding.compile_run M.tm.m
    (fun z ↦ initList M.tm (z.map M.inputAlphabet.symm)) ruler
    (init_encode_mem_FP M.tm M.inputAlphabet.symm) hruler
    (init_stack_length M.tm M.inputAlphabet.symm)
  have hout := mem_FP_comp hrun (output_bit_mem_FP M.tm M.outputAlphabet)
  apply mem_FP_of_eq hout
  intro z
  have h := M.outputsFun z
  have hs : (StackEncoding.totalStep M.tm.m)^[(ruler z).length]
      (initList M.tm (z.map M.inputAlphabet.symm)) =
      haltList M.tm [M.outputAlphabet.symm (f z)] :=
    StackEncoding.total_run_after_halt M.tm.m h.evals_in_steps rfl
      (h.steps_le_m.trans (hrlen z))
  dsimp only [Function.comp_apply]
  rw [hs, output_bit_halt]

/-- The archive's registered deterministic polynomial-time class has `FP` membership flags. -/
theorem registered_P_pred {L : Lax434930.PolynomialTime.Language}
    (hL : L ∈ Lax434930.PolynomialTime.P) : FPPred (fun z ↦ z ∈ L) := by
  obtain ⟨f, hf, ⟨M⟩⟩ := hL
  obtain ⟨N, _, hfinite⟩ := FiniteAlphabet.binary_computer M
  have hp := FPPred.of_flag (flag_mem_FP_of_finite_stack N hfinite)
  exact hp.of_iff hf

/-- The archive's registered deterministic polynomial-time class embeds in the ported model. -/
theorem registered_P_subset : Lax434930.PolynomialTime.P ⊆ PCPFoundation.Complexity.P :=
  fun _ hL ↦ (registered_P_pred hL).mem_P

end Lax253009Proofs.RegisteredBridge
