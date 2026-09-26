import Lax253009.RandomizedReduction
import Lax253009Proofs.SamplingParameters
import Lax253009Proofs.TestSampling
import Lax253009Proofs.TestRepetition

namespace Lax253009Proofs

open Lax253009 Lax253009.LocalTests Lax253009.ConsistencyGraph
open Lax253009.TestSampling Lax253009.TestRepetition Lax253009.SamplingParameters
open Lax253009.RandomizedReduction Lax253009.FiniteProbability Lax253009.EncodedReduction
open Lax434930.PolynomialTime
open scoped Classical

theorem sampling_expected_count (t k m : ℕ) :
    (sampleCount t k m : ℝ) * (1 / 2 : ℝ) ^ (t * k) = (m : ℝ) + 2 := by
  simp [sampleCount]

/--
---
conclusion: Lax253009.RandomizedReduction.vertex_bound
---
Multiply the sample count by the accepting-view bound after repetition.
-/
theorem randomized_vertex_bound {r m : ℕ} (C : System r m) (f t k : ℕ)
    (hfree : ∀ seed, (C.accepting seed).card ≤ 2 ^ f)
    (z : Fin (sampleCount t k m) → Fin (r ^ k)) :
    Fintype.card (Vertex (tests C t k z)) ≤ vertexBound f t k m := by
  have h := sampled_vertex_bound (repeated C k) z ((2 ^ f) ^ k)
    (repeated_free_bits C k (2 ^ f) hfree)
  apply h.trans_eq
  simp only [sampleCount, vertexBound, ← pow_mul, mul_assoc, ← pow_add]
  congr 2
  ring

/--
---
conclusion: Lax253009.RandomizedReduction.soundness
---
The expected sampled acceptance count is m+2. The multiplicative tail
bound applies simultaneously to all 2^m possible proofs.
-/
theorem randomized_soundness {r m : ℕ} (hr : 0 < r) (C : System r m) (t k : ℕ)
    (hsound : Sound C ((1 / 2 : ℝ) ^ t)) :
    probability (fun z : Fin (sampleCount t k m) → Fin (r ^ k) ↦
      threshold m ≤ (output (tests C t k z)).cliqueNumber) ≤ 1 / 4 := by
  have hs := repeated_soundness C k ((1 / 2 : ℝ) ^ t) (by positivity) hsound
  rw [← pow_mul] at hs
  have h := sampled_soundness (pow_pos hr k) (repeated C k)
    ((1 / 2 : ℝ) ^ (t * k)) (by positivity) hs
    (show (m : ℝ) + 2 ≤ (sampleCount t k m : ℝ) * (1 / 2 : ℝ) ^ (t * k) by
      rw [sampling_expected_count])
  apply le_trans (finite_probability_mono _ _ ?_) h
  intro z hz
  rw [mul_assoc, sampling_expected_count]
  exact_mod_cast hz

theorem randomized_perfect_completeness {r m : ℕ} (C : System r m) (t k : ℕ)
    (hC : Complete C) (z : Fin (sampleCount t k m) → Fin (r ^ k)) :
    0 < Fintype.card (Vertex (tests C t k z)) ∧
      (output (tests C t k z)).cliqueNumber = sampleCount t k m := by
  have hN : 0 < sampleCount t k m := by unfold sampleCount; positivity
  have hcomp := repeated_perfect_completeness C k hC
  refine ⟨?_, sampled_perfect_completeness (repeated C k) hcomp z⟩
  obtain ⟨π, hπ⟩ := hcomp
  obtain ⟨a, ha, _⟩ := hπ (z ⟨0, hN⟩)
  have : Nonempty (Vertex (tests C t k z)) := ⟨⟨⟨0, hN⟩, a, ha⟩⟩
  exact Fintype.card_pos

/--
---
conclusion: Lax253009.RandomizedReduction.approximation_decision
---
The explicit gap forces every complete sampled instance to be accepted.
On a sound instance, acceptance forces the clique number into the bad
event already bounded by the sampling theorem.
-/
theorem randomized_approximation_decision (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (happrox : Approximation.Approximable ε) :
    ∃ estimate : Word → ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate) ∧
      ∀ (f t c : ℕ), 1 ≤ (c : ℝ) * ((t : ℝ) * ε - (f : ℝ) * (1 - ε)) →
      ∀ (r m : ℕ), 0 < r → ∀ C : System r m,
        (∀ seed, (C.accepting seed).card ≤ 2 ^ f) →
        (Complete C → ∀ z, Accept estimate C t (repetitions c m) z) ∧
        (Sound C ((1 / 2 : ℝ) ^ t) →
          probability (Accept estimate C t (repetitions c m)) ≤ 1 / 4) := by
  obtain ⟨estimate, hpoly, hestimate⟩ := happrox
  refine ⟨estimate, hpoly, fun f t c hmargin r m hr C hfree ↦ ?_⟩
  constructor
  · intro hcomp z
    obtain ⟨hN, hclique⟩ := randomized_perfect_completeness C t (repetitions c m) hcomp z
    refine ⟨hN, ?_⟩
    have hg := sampling_approximation_gap ε hε hε1 f t c hmargin m
    have hsize := randomized_vertex_bound C f t (repetitions c m) hfree z
    obtain ⟨_, hupper⟩ := hestimate _ hN (output (tests C t (repetitions c m) z))
    rw [hclique] at hupper
    by_contra hnot
    have hle : estimate (output (tests C t (repetitions c m) z)).encode ≤ threshold m :=
      Nat.le_of_not_gt hnot
    have hbase : Real.rpow (Fintype.card (Vertex (tests C t (repetitions c m) z)) : ℝ) (1 - ε) ≤
        Real.rpow (vertexBound f t (repetitions c m) m : ℝ) (1 - ε) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hsize) (by linarith)
    have hprod := mul_le_mul hbase (show (estimate (output (tests C t (repetitions c m) z)).encode : ℝ) ≤
        threshold m by exact_mod_cast hle) (Nat.cast_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact (not_lt_of_ge (hupper.trans hprod)) hg
  · intro hs
    apply le_trans (finite_probability_mono _ _ ?_) (randomized_soundness hr C t _ hs)
    intro z hz
    have hlo := (hestimate _ hz.1 (output (tests C t (repetitions c m) z))).1
    exact (Nat.le_of_lt hz.2).trans hlo

end Lax253009Proofs
