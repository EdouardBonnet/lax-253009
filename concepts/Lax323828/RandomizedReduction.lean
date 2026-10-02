import Lax323828.SamplingParameters
import Lax323828.FreshBitSampling

/-!
---
title: The finite randomized PCP-to-clique transfer
type: theorem
---
Repeat the local tests and sample their random choices independently. With
$2^f$ accepting views per choice and soundness $2^{-t}$, the graph size is
bounded by the explicit polynomial in SamplingParameters, and its clique
number is below $4(m+2)$ except on an event of probability at most $1/4$.
Perfect completeness holds for every sample.

Consequently an $n^{1-\varepsilon}$ approximation yields a decision rule
with perfect completeness and false-positive probability at most $1/4$
whenever $\varepsilon t>(1-\varepsilon)f$. Empty graphs are rejected.
The estimator is the given polynomial-time estimator. This finite theorem
does not assert a machine implementation of graph construction or sampling.
-/

namespace Lax323828.RandomizedReduction

open LocalTests ConsistencyGraph TestSampling TestRepetition SamplingParameters FiniteProbability
open Lax434930.PolynomialTime

noncomputable def tests {r m : ℕ} (C : System r m) (t k : ℕ)
    (z : Fin (sampleCount t k m) → Fin (r ^ k)) : System (sampleCount t k m) m :=
  sampled (repeated C k) z

def Accept {r m : ℕ} (estimate : Word → ℕ) (C : System r m) (t k : ℕ)
    (z : Fin (sampleCount t k m) → Fin (r ^ k)) : Prop :=
  0 < Fintype.card (Vertex (tests C t k z)) ∧
    threshold m < estimate (EncodedReduction.output (tests C t k z)).encode

def CoinAccept {r m : ℕ} (estimate : Word → ℕ) (C : System r m) (hr : 0 < r) (t k : ℕ)
    (coins : Fin (sampleCount t k m * FreshBitSampling.bitsPerDraw (sampleCount t k m) (r ^ k)) → Bool) :
    Prop := Accept estimate C t k (FreshBitSampling.sampleFlat (pow_pos hr k) coins)

axiom vertex_bound {r m : ℕ} (C : System r m) (f t k : ℕ)
    (hfree : ∀ seed, (C.accepting seed).card ≤ 2 ^ f)
    (z : Fin (sampleCount t k m) → Fin (r ^ k)) :
  Fintype.card (Vertex (tests C t k z)) ≤ vertexBound f t k m

axiom soundness {r m : ℕ} (hr : 0 < r) (C : System r m) (t k : ℕ)
    (hsound : Sound C ((1 / 2 : ℝ) ^ t)) :
  probability (fun z : Fin (sampleCount t k m) → Fin (r ^ k) ↦
    threshold m ≤ (EncodedReduction.output (tests C t k z)).cliqueNumber) ≤ 1 / 4

axiom approximation_decision (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (happrox : Approximation.Approximable ε) :
  ∃ estimate : Word → ℕ,
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate) ∧
    ∀ (f t c : ℕ), 1 ≤ (c : ℝ) * ((t : ℝ) * ε - (f : ℝ) * (1 - ε)) →
    ∀ (r m : ℕ), 0 < r → ∀ C : System r m,
      (∀ seed, (C.accepting seed).card ≤ 2 ^ f) →
      (Complete C → ∀ z, Accept estimate C t (repetitions c m) z) ∧
      (Sound C ((1 / 2 : ℝ) ^ t) →
        probability (Accept estimate C t (repetitions c m)) ≤ 1 / 4)

end Lax323828.RandomizedReduction
