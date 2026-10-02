import Lax323828.FAFComposition
import Lax323828Proofs.FAFParameters

namespace Lax323828Proofs

open Lax323828.LongCode Lax323828.FiniteProbability Lax323828.FAFStrategyExtraction
open Lax323828.FAFComposition Filter

/--
---
conclusion: Lax323828.FAFComposition.threshold_positive
---
Every factor is positive, so game soundness tending to zero can meet this
threshold for each fixed choice of the verifier parameters.
-/
theorem faf_game_threshold_pos (l s : ℕ) : 0 < gameThreshold l s := by
  unfold gameThreshold
  positivity

/--
---
conclusion: Lax323828.FAFComposition.soundness
---
The explicit finite FAF error decays faster than 2^(-20*l*l*s).
Acceptance above that target would therefore produce prover strategies
exceeding the stated game threshold, contradicting game soundness.
-/
theorem faf_composition_soundness (l : ℕ) (hl : 0 < l) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w →
      ∀ {U Ω W : Type} [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
        [Fintype W] [DecidableEq W],
      ∀ u : ℕ, ∀ (question : U → Ω → W)
        (ρ : U → Ω → Word w → Word u) (valid : U → Ω → Coordinate w)
        (R : U → Table u) (A : W → Table w),
        (∀ (P : W → Option (Word w)) (Q : U → Option (Word u)),
          probability (Lax323828.DecodedStrategies.Wins question (Relation ρ valid) P Q) < gameThreshold l s) →
        probability (Lax323828.FAFStrategyExtraction.Accepts (n := 10 * l) (s := s) (q := 10 * l * s)
          question ρ valid R A) < (1 / 2 : ℝ) ^ (20 * l * l * s) := by
  obtain ⟨s₁, hs₁⟩ := Lax323828.FAFStrategyExtraction.uniform_extraction (40 * l * l) (by positivity)
  obtain ⟨s₂, hs₂⟩ := eventually_atTop.mp (faf_parameter_bounds l hl)
  refine ⟨max s₁ s₂, fun s hs ↦ ?_⟩
  obtain ⟨w₀, hw₀⟩ := hs₁ s ((le_max_left _ _).trans hs)
  obtain ⟨hsmall, herror⟩ := hs₂ s ((le_max_right _ _).trans hs)
  refine ⟨w₀, fun w hw ↦ ?_⟩
  intro U Ω W _ _ _ _ _ _ u question ρ valid R A hgame
  by_contra hacc
  have hacc' := le_of_not_gt hacc
  obtain ⟨P, Q, hPQ⟩ := hw₀ w hw u (10 * l) (10 * l * s) (5 * l)
    question ρ valid R A ((1 / 2 : ℝ) ^ (20 * l * s)) (by positivity) hsmall
  rw [dyadic_negative_rpow] at hPQ
  have hbound : gameThreshold l s ≤ probability
      (Lax323828.DecodedStrategies.Wins question (Relation ρ valid) P Q) := by
    apply le_trans ?_ hPQ
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  exact (not_lt_of_ge hbound) (hgame P Q)

end Lax323828Proofs
