import Lax253009.FAFStrategyExtraction
import Lax253009.FAFPatterns

/-!
---
title: Soundness of the finite FAF composition
type: theorem
---
For each positive integer $\ell$, sufficiently large $s$ and then $w$
give a finite FAF verifier with soundness below $2^{-20\ell^2s}$ whenever
the underlying two-prover game has sufficiently small positive soundness.
The test uses $n=10\ell$ larger tables and $q=10\ell s$ reference queries.
Its proved free-bit bound is $q+ns=20\ell s$.

This is the finite composition underlying Theorem 5.1. The game threshold
is stated explicitly and is positive; exponentially decreasing game
soundness is more than sufficient. The theorem does not provide the
bounded-occurrence gap reduction, parallel repetition, logarithmic random
bit implementation, or polynomial-time verifier construction.
-/

namespace Lax253009.FAFComposition

open LongCode FiniteProbability FAFStrategyExtraction

noncomputable def gameThreshold (l s : ℕ) : ℝ :=
  ((1 / 2 : ℝ) ^ (20 * l * l * s) / 2) * (1 / 2 : ℝ) ^ (20 * l * s) /
    ((2 : ℝ) ^ s + 1)

axiom threshold_positive (l s : ℕ) : 0 < gameThreshold l s

axiom soundness (l : ℕ) (hl : 0 < l) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w →
      ∀ {U Ω W : Type} [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
        [Fintype W] [DecidableEq W],
      ∀ u : ℕ, ∀ (question : U → Ω → W)
        (ρ : U → Ω → Word w → Word u) (valid : U → Ω → Coordinate w)
        (R : U → Table u) (A : W → Table w),
        (∀ (P : W → Option (Word w)) (Q : U → Option (Word u)),
          probability (DecodedStrategies.Wins question (Relation ρ valid) P Q) < gameThreshold l s) →
        probability (FAFStrategyExtraction.Accepts (n := 10 * l) (s := s) (q := 10 * l * s)
          question ρ valid R A) < (1 / 2 : ℝ) ^ (20 * l * l * s)

end Lax253009.FAFComposition
