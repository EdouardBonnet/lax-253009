import Lax323828Proofs.RegisteredBridge.ComputableSampledGraph

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax323828Proofs.RegisteredBridge.SampledGraphDecision

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding ComputableNumbering
open Lax323828 LocalTests SamplingParameters FreshBitSampling FiniteProbability TestSampling TestRepetition
open ComputableSampledGraph
open scoped Classical

variable {r m : Word → ℕ} {C : ∀ x, LocalTests.System (r x) (m x)} {f : ℕ}

def coinCount (r m t c : ℕ) : ℕ :=
  sampleCount t (repetitions c m) m * repetitions c m *
    bitsPerDraw (sampleCount t (repetitions c m) m * repetitions c m) r

theorem coinCount_poly (hr : UnaryFn r) (hm : UnaryFn m) (t c : ℕ) :
    UnaryFn (fun x ↦ coinCount (r x) (m x) t c) := by
  have hN := SamplingAlgorithms.sampleCount_poly hm c t
  have hk := SamplingAlgorithms.repetitions_poly hm c
  exact (hN.mul hk).mul (SamplingAlgorithms.bitsPerDraw_poly (hN.mul hk) hr)

theorem perfect (E : ∀ x, SlotGraph.Enumeration (C x) (2 ^ f)) (hr : ∀ x, 0 < r x)
    (t c : ℕ) (x coins : Word) (hC : Complete (C x)) :
    sampleCount t (repetitions c (m x)) (m x) ≤ (graph E hr t c x coins).cliqueNumber := by
  let k := repetitions c (m x)
  let N := sampleCount t k (m x)
  let seed : Fin N → Fin k → Fin (r x) := fun i j ↦
    ⟨SamplingAlgorithms.draw (N * k) (r x) coins (i.val * k + j.val), Nat.mod_lt _ (hr x)⟩
  have h := (SlotGraph.optimum_bounds (RepeatedSlotViews.repeatedEnumeration (E x) k N seed)).1
  have hcomp := Lax323828.TestSampling.perfect_completeness (repeated (C x) k)
    (Lax323828.TestRepetition.perfect_completeness (C x) k hC) (fun i ↦ seedEquiv (r x) k (seed i))
  rw [Lax323828.EncodedReduction.cliqueNumber_output] at hcomp
  rw [hcomp] at h
  exact h

theorem sound (E : ∀ x, SlotGraph.Enumeration (C x) (2 ^ f)) (hr : ∀ x, 0 < r x)
    (t c : ℕ) (hc : 0 < c) (x : Word) (hC : Sound (C x) ((1 / 2 : ℝ) ^ t)) :
    probability (fun coins : Fin (coinCount (r x) (m x) t c) → Bool ↦
      threshold (m x) ≤ (graph E hr t c x (List.ofFn coins)).cliqueNumber) ≤ 1 / 3 := by
  have hk : 0 < repetitions c (m x) := Nat.mul_pos hc (by omega)
  have hN : 0 < sampleCount t (repetitions c (m x)) (m x) := by unfold sampleCount; positivity
  have hh := MatrixSampling.one_third hN hk (hr x) _ (Lax323828.RandomizedReduction.soundness (hr x) (C x) t _ hC)
  apply le_trans (Lax323828.FiniteProbability.monotone _ _ ?_) hh
  intro coins hg
  rw [graph_of_coins] at hg
  have hu := (SlotGraph.optimum_bounds
    (RepeatedSlotViews.repeatedEnumeration (E x) (repetitions c (m x))
      (sampleCount t (repetitions c (m x)) (m x)) (MatrixSampling.sample (hr x) coins))).2
  change threshold (m x) ≤
    (EncodedReduction.output (sampled (repeated (C x) (repetitions c (m x)))
      (fun i ↦ seedEquiv (r x) _ (MatrixSampling.sample (hr x) coins i)))).cliqueNumber
  rw [Lax323828.EncodedReduction.cliqueNumber_output]
  have ht : 1 < threshold (m x) := by unfold threshold; omega
  omega

theorem decision_mem_FP (E : ∀ x, SlotGraph.Enumeration (C x) (2 ^ f))
    (hr : ∀ x, 0 < r x) (hE : SlotGraphAlgorithms.Algorithms E)
    (hrpoly : UnaryFn r) (hmpoly : UnaryFn m) (t c : ℕ) {estimate : Word → ℕ}
    (M : Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate) :
    FPPred (fun z ↦ threshold (m (pairFst z)) < estimate (graph E hr t c (pairFst z) (pairSnd z)).encode) := by
  have hg := ComputableSampledGraph.encode_mem_FP E hr hE hrpoly hmpoly t c
  have he := mem_FP_comp hg (encoded_mem_FP M)
  have ht := (UnaryFn.const 4).mul ((hmpoly.comp pairFst_mem_FP).add (UnaryFn.const 2))
  have hv := UnaryFn.fromBitsLE_min he (ht.add (UnaryFn.const 1))
  apply (FPPred.lt ht hv).of_iff
  intro z
  simp only [Function.comp_apply, from_bits_encode_nat, lt_min_iff, Nat.lt_succ_self, and_true, threshold]

theorem approximation_decision (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (happrox : Approximation.Approximable ε) :
    ∃ estimate : Word → ℕ, Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate) ∧
      ∀ (f t c : ℕ), 0 < c →
      1 ≤ (c : ℝ) * ((t : ℝ) * ε - (f : ℝ) * (1 - ε)) →
      ∀ {r m : Word → ℕ} {C : ∀ x, LocalTests.System (r x) (m x)},
      ∀ E : ∀ x, SlotGraph.Enumeration (C x) (2 ^ f), ∀ hr : ∀ x, 0 < r x,
      ∀ x : Word,
      (Complete (C x) → ∀ coins, threshold (m x) < estimate (graph E hr t c x coins).encode) ∧
      (Sound (C x) ((1 / 2 : ℝ) ^ t) →
        probability (fun coins : Fin (coinCount (r x) (m x) t c) → Bool ↦
          threshold (m x) < estimate (graph E hr t c x (List.ofFn coins)).encode) ≤ 1 / 3) := by
  obtain ⟨estimate, hpoly, he⟩ := happrox
  refine ⟨estimate, hpoly, fun f t c hc hmargin r m C E hr x ↦ ?_⟩
  constructor
  · intro hC coins
    have hlarge := perfect E hr t c x coins hC
    have hhi := (he _ (size_pos f t c (m x)) (graph E hr t c x coins)).2
    have hgap := Lax323828.SamplingParameters.approximation_gap ε hε hε1 f t c hmargin (m x)
    rw [← size_eq] at hgap
    by_contra hn
    have hn' : (estimate (graph E hr t c x coins).encode : ℝ) ≤ threshold (m x) := by
      exact_mod_cast Nat.le_of_not_gt hn
    have hprod := mul_le_mul_of_nonneg_left hn'
      (Real.rpow_nonneg (Nat.cast_nonneg (size f t c (m x))) (1 - ε))
    have hlarge' : (sampleCount t (repetitions c (m x)) (m x) : ℝ) ≤
        (graph E hr t c x coins).cliqueNumber := by exact_mod_cast hlarge
    exact (not_lt_of_ge (hlarge'.trans (hhi.trans hprod))) hgap
  · intro hC
    apply le_trans (Lax323828.FiniteProbability.monotone _ _ ?_) (sound E hr t c hc x hC)
    intro coins hcoin
    exact (Nat.le_of_lt hcoin).trans (he _ (size_pos f t c (m x))
      (graph E hr t c x (List.ofFn coins))).1

end Lax323828Proofs.RegisteredBridge.SampledGraphDecision
