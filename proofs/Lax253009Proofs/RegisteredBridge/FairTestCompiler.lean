import Lax253009Proofs.RegisteredBridge.FairTestExecution
import Lax253009Proofs.RegisteredBridge.ProbabilisticStackCompiler
import Lax253009Proofs.RegisteredBridge.RandomizedContainments
import Lax253009Proofs.PCPFoundation.Classes.PCP.Internal.FamilyFin

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Lax253009Proofs.RegisteredBridge.FairTestCompiler

open PCPFoundation.Complexity FairExecution Turing
open scoped Classical

/-- Every polynomial-time finite fair-tape test has a registered
probabilistic procedure with exactly the same output distribution. -/
theorem compile (bits : List Bool → ℕ) (hbits : UnaryFn bits)
    (result : List Bool → Option Bool)
    (hresult : (fun z ↦ FiniteEncoding.code (result z)) ∈ FP) :
    ∃ C : Lax666725.ProbabilisticMachines.Procedure (Option Bool),
      ∀ (x : List Bool) (P : Option Bool → Prop),
        (C.probability x P : ℝ) =
        Lax253009.FiniteProbability.probability (fun r : Fin (bits x) → Bool ↦
          P (result (pair x (List.ofFn r)))) := by
  have hprep : (fun z ↦ pair (List.replicate (bits z.reverse) false) z.reverse) ∈ FP :=
    mem_FP_pair ((hbits.comp reverse_mem_FP).replicate_mem_FP false) reverse_mem_FP
  have hcheck : (fun z ↦ FiniteEncoding.code (result (pair (pairSnd z) (pairFst z)))) ∈ FP := by
    simpa only [Function.comp_def] using
      mem_FP_comp (mem_FP_pair pairSnd_mem_FP pairFst_mem_FP) hresult
  obtain ⟨d₀, m, A, T₀, hA, hT₀⟩ := hprep
  obtain ⟨d₁, n, B, T₁, hB, hT₁⟩ := hcheck
  obtain ⟨p₀, hp₀⟩ := BigO.pow_polynomial_bound hT₀
  obtain ⟨p₁, hp₁⟩ := BigO.pow_polynomial_bound hT₁
  obtain ⟨pb, hpb⟩ := Cobham.output_length_poly_of_mem_FP hbits.mem_FP
  have hb (x : List Bool) : bits x ≤ pb.eval x.length := by simpa using hpb x
  let size : Polynomial ℕ := 2 * pb + 2 + Polynomial.X
  let time : Polynomial ℕ :=
    8 * (Polynomial.X + p₀ + 1) + 3 * pb + 2 * Polynomial.X + 6 +
      8 * (size + p₁.comp size + 1)
  have htime (x : List Bool) :
      8 * (x.length + T₀ x.length + 1) + FairTestMachine.sampleBound T₁ x (bits x) (bits x) ≤
        time.eval x.length := by
    have hb' := hb x
    have h₀ := hp₀ x.length
    have h₁ := (hp₁ (2 * bits x + 2 + x.length)).trans
      (polynomial_eval_mono_nat p₁ (show 2 * bits x + 2 + x.length ≤ size.eval x.length by
        simp only [size, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
          Polynomial.eval_X]
        omega))
    simp only [time, FairTestMachine.sampleBound, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_comp]
    simp only [size, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] at h₁ ⊢
    omega
  have hex (x : List Bool) :
      ∃ t, t ≤ time.eval x.length ∧
        Executes (FairTestMachine.advance A B) (fun c ↦ FairTestMachine.output A B c.var)
          (fun c ↦ c.l = none) (TM2.init FairTestMachine.buffer x.reverse)
          (CoinTree.sample (bits x) (fun r ↦ result (pair x r))) t := by
    obtain ⟨t, ht, he⟩ := FairTestMachine.execution A B bits result hA hB x
    exact ⟨t, ht.trans (htime x), he⟩
  have hi (x : List Bool) :
      ProbabilisticStackCompiler.sourceInitial FairTestMachine.buffer (Function.Embedding.refl Bool) x =
        (TM2.init FairTestMachine.buffer x.reverse :
          TM2.Cfg (FairTestMachine.Alphabet (m := m) (n := n)) FairTestMachine.Label
            (FairTestMachine.Register A B)) := by
    unfold ProbabilisticStackCompiler.sourceInitial
    congr 1
    exact List.map_id x.reverse
  have hstep : RandomStackTape.sourceAdvance (FairTestMachine.program A B) =
      FairTestMachine.advance A B := rfl
  have hh : ∀ (x : List Bool) (r : Fin (time.eval x.length) → Bool),
      ((List.ofFn r).foldl (RandomStackTape.sourceAdvance (FairTestMachine.program A B))
        (ProbabilisticStackCompiler.sourceInitial FairTestMachine.buffer (Function.Embedding.refl Bool) x)).l =
          none := by
    intro x r
    obtain ⟨t, ht, he⟩ := hex x
    rw [hi, hstep]
    exact he.halts (time.eval x.length) ht r
  let C := ProbabilisticStackCompiler.procedure (FairTestMachine.program A B)
    FairTestMachine.buffer (Function.Embedding.refl Bool) (FairTestMachine.output A B) time hh
  refine ⟨C, fun x P ↦ ?_⟩
  have hC := ProbabilisticStackCompiler.procedure_probability (FairTestMachine.program A B)
    FairTestMachine.buffer (Function.Embedding.refl Bool) (FairTestMachine.output A B) time hh x P
  obtain ⟨t, ht, he⟩ := hex x
  refine hC.trans ?_
  rw [hi, hstep]
  calc
    _ = average (FairTestMachine.advance A B)
        (fun c ↦ if P (FairTestMachine.output A B c.var) then 1 else 0)
        (time.eval x.length) (TM2.init FairTestMachine.buffer x.reverse) :=
      (average_indicator (FairTestMachine.advance A B)
        (fun c ↦ P (FairTestMachine.output A B c.var)) (time.eval x.length) _).symm
    _ = (CoinTree.sample (bits x) (fun r ↦ result (pair x r))).mean (fun a ↦ if P a then 1 else 0) :=
      he.average_eq (fun a ↦ if P a then 1 else 0) (time.eval x.length) ht
    _ = _ := CoinTree.indicator (bits x) (fun r ↦ result (pair x r)) P

theorem zero_probability_no_event {α : Type} [Fintype α] [Nonempty α] (P : α → Prop)
    (h : Lax253009.FiniteProbability.probability P = 0) : ∀ a, ¬ P a := by
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hz : (Finset.univ.filter P).card = 0 := by
    unfold Lax253009.FiniteProbability.probability at h
    have hh := (div_eq_zero_iff).mp h
    exact_mod_cast hh.resolve_right hcard
  intro a ha
  have he := Finset.card_eq_zero.mp hz
  have hm : a ∈ Finset.univ.filter P := Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩
  rw [he] at hm
  exact Finset.notMem_empty a hm

/-- Transfer the finite zero-error construction into the exact registered
ZPP class, with correctness on every branch and success at least two thirds. -/
theorem zeroTest_in_ZPP {L : Language} (A : FairTests.ZeroTest L) :
    L ∈ Lax666725.ZeroError.ZPP := by
  obtain ⟨C, hC⟩ := compile A.bits A.bits_poly A.result A.result_poly
  refine ⟨C, fun x ↦ ⟨?_, ?_⟩⟩
  · intro r b hr
    by_contra hb
    have hz : Lax253009.FiniteProbability.probability
        (fun s : Fin (A.bits x) → Bool ↦ A.result (pair x (List.ofFn s)) = some b) = 0 := by
      have hnone (s : Fin (A.bits x) → Bool) : A.result (pair x (List.ofFn s)) ≠ some b :=
        fun hs ↦ hb (A.correct x s b hs)
      simp [finite_probability_indicator, hnone]
    have hc : Lax253009.FiniteProbability.probability
        (fun s : C.Coins x ↦ C.eval x s = some b) = 0 := by
      exact (ProbabilisticStackCompiler.probability_real C x (fun a ↦ a = some b)).symm.trans
        ((hC x (fun a ↦ a = some b)).trans hz)
    exact zero_probability_no_event _ hc r hr
  · have hs := A.success x
    rw [← hC x (fun a ↦ a.isSome = true)] at hs
    exact (Rat.cast_le (K := ℝ)).mp (by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using hs)

end Lax253009Proofs.RegisteredBridge.FairTestCompiler
