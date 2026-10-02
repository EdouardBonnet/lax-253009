import Lax323828.GameToClique
import Lax323828Proofs.FAFLocalTests
import Lax323828Proofs.RandomizedReduction
import Lax323828Proofs.FreshBitSampling

namespace Lax323828Proofs

open Lax323828 Lax323828.LocalTests Lax323828.ConsistencyGraph
open Lax323828.TestSampling Lax323828.SamplingParameters Lax323828.FiniteProbability
open Lax434930.PolynomialTime

theorem approximation_weaken {ε θ : ℝ} (hθ : θ ≤ ε)
    (happrox : Approximation.Approximable ε) : Approximation.Approximable θ := by
  obtain ⟨estimate, hpoly, he⟩ := happrox
  refine ⟨estimate, hpoly, fun n hn G ↦ ?_⟩
  obtain ⟨hlo, hhi⟩ := he n hn G
  refine ⟨hlo, hhi.trans ?_⟩
  apply mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

/--
---
conclusion: Lax323828.GameToClique.reduction
---
Choose l so that l*epsilon exceeds one, then choose the uniform CNA/FAF
parameters and a sampling multiplier. The local-test verifier has
free-bit/soundness ratio 1/l. Apply the proved randomized transfer, retaining
its explicit polynomial vertex bound.
-/
theorem game_to_clique_reduction (ε : ℝ) (hε : 0 < ε) (happrox : Approximation.Approximable ε) :
    ∃ estimate : Word → ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate) ∧
      ∃ l s c w₀ : ℕ, 0 < l ∧ 0 < s ∧ 0 < c ∧
      ∀ w : ℕ, w₀ ≤ w →
      ∀ {U Ω W : Type} [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
        [Fintype W] [DecidableEq W],
      ∀ u : ℕ, ∀ (question : U → Ω → W)
        (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → LongCode.Coordinate w),
        let C := FAFLocalTests.system (n := 10 * l) (s := s) (q := 10 * l * s) question ρ valid
        let m := Fintype.card (FAFLocalTests.Index U W u w)
        let k := repetitions c m
        (∀ (P : W → LongCode.Word w) (Q : U → LongCode.Word u),
          (∀ v ω, valid v ω (P (question v ω)) = true) →
          (∀ v ω, ρ v ω (P (question v ω)) = Q v) →
          ∀ coins, RandomizedReduction.CoinAccept estimate C (by exact Fintype.card_pos)
            (20 * l * l * s) k coins) ∧
        ((∀ (P : W → Option (LongCode.Word w)) (Q : U → Option (LongCode.Word u)),
          probability (DecodedStrategies.Wins question (FAFStrategyExtraction.Relation ρ valid) P Q) <
            FAFComposition.gameThreshold l s) →
          probability (RandomizedReduction.CoinAccept estimate C (by exact Fintype.card_pos)
            (20 * l * l * s) k) ≤ 1 / 3) ∧
        (∀ z, Fintype.card (Vertex (RandomizedReduction.tests C (20 * l * l * s) k z)) ≤
          16 ^ ((20 * l * l * s + 20 * l * s) * c) *
            (m + 2) ^ ((20 * l * l * s + 20 * l * s) * c + 1)) := by
  let θ := min ε 1
  have hθ : 0 < θ := lt_min hε zero_lt_one
  obtain ⟨estimate, hpoly, hdec⟩ := Lax323828.RandomizedReduction.approximation_decision θ hθ (min_le_right _ _)
    (approximation_weaken (min_le_left _ _) happrox)
  obtain ⟨l, hl⟩ := exists_nat_gt (1 / θ)
  have hlpos : 0 < l := by exact_mod_cast (div_pos zero_lt_one hθ).trans hl
  have hlθ : 1 < (l : ℝ) * θ := (div_lt_iff₀ hθ).mp hl
  obtain ⟨s₀, hs₀⟩ := Lax323828.FAFLocalTests.soundness l hlpos
  let s := max s₀ 1
  have hspos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  obtain ⟨w₀, hw₀⟩ := hs₀ s (le_max_left _ _)
  have hmargin : 0 < (20 * l * l * s : ℕ) * θ - (20 * l * s : ℕ) * (1 - θ) := by
    push_cast
    have hp : 0 < (20 : ℝ) * l * s := by positivity
    have hm : 0 < (l : ℝ) * θ - (1 - θ) := by linarith
    nlinarith [mul_pos hp hm]
  obtain ⟨c, hc, hcmargin⟩ := Lax323828.SamplingParameters.choose_multiplier θ (20 * l * s) (20 * l * l * s) hmargin
  refine ⟨estimate, hpoly, l, s, c, w₀, hlpos, hspos, hc, ?_⟩
  intro w hw U Ω W _ _ _ _ _ _ u question ρ valid
  dsimp only
  let C := FAFLocalTests.system (n := 10 * l) (s := s) (q := 10 * l * s) question ρ valid
  have hfree : ∀ seed, (C.accepting seed).card ≤ 2 ^ (20 * l * s) := by
    intro seed
    have h := Lax323828.FAFLocalTests.free_bits (n := 10 * l) (s := s) (q := 10 * l * s) question ρ valid seed
    convert h using 1
    congr 1
    ring
  have hr : 0 < Fintype.card (FAFLocalTests.Randomness U Ω u w (10 * l) s (10 * l * s)) :=
    Fintype.card_pos
  obtain ⟨hyes, hno⟩ := hdec (20 * l * s) (20 * l * l * s) c hcmargin _ _ hr C hfree
  refine ⟨fun P Q hv hp coins ↦ hyes (Lax323828.FAFLocalTests.perfect_completeness question ρ valid P Q hv hp)
    (FreshBitSampling.sampleFlat (pow_pos hr _) coins), ?_, ?_⟩
  · intro hgame
    exact Lax323828.FreshBitSampling.flat_one_third_error (by unfold sampleCount; positivity) (pow_pos hr _) _
      (hno (hw₀ w hw u question ρ valid hgame))
  · intro z
    exact (Lax323828.RandomizedReduction.vertex_bound C _ _ _ hfree z).trans (Lax323828.SamplingParameters.polynomial_bound _ _ _ _)

end Lax323828Proofs
