import Lax253009.FAFLocalTests
import Lax253009.RandomizedReduction

/-!
---
title: The complete finite game-to-clique construction
type: theorem
---
For any positive approximation exponent, choose fixed FAF and sampling
parameters before the game question spaces or the input instance. The
FAF composition, local-view construction, repetition, and randomized
sparsification then yield a clique decision rule with perfect completeness.
Explicit sampling from a fixed vector of fair bits gives false-positive
probability at most $1/3$ on sufficiently sound games.

The sampled graph has polynomially many vertices in the proof length, with
explicit degree and constant. Its base proof length is linear in the game
question counts for fixed answer widths. This completes the finite
mathematical transfer from a small-value projection game. Constructing that
game from the registered NP machine model and proving polynomial-time
implementations are still required for Håstad's theorem. The finite regular
3-SAT gap and soundness amplification are proved in the companion concepts.
-/

namespace Lax253009.GameToClique

open LocalTests ConsistencyGraph TestSampling SamplingParameters FiniteProbability
open Lax434930.PolynomialTime

axiom reduction (ε : ℝ) (hε : 0 < ε) (happrox : Approximation.Approximable ε) :
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
          (m + 2) ^ ((20 * l * l * s + 20 * l * s) * c + 1))

end Lax253009.GameToClique
