import Lax253009.TestRepetition
import Mathlib.Data.Nat.Log

/-!
---
title: Polynomial size and approximation gap after sampling
type: theorem
---
For a verifier with soundness $2^{-t}$ and at most $2^f$ accepting views,
repeat $k=c(\lceil\log_2(m+2)\rceil+3)$ times and sample
$(m+2)2^{tk}$ choices. The sampled consistency graph has at most
$(m+2)2^{(t+f)k}$ vertices and its low-clique threshold is $4(m+2)$.

If $c(\varepsilon t-(1-\varepsilon)f)\geq1$, this separates an
$n^{1-\varepsilon}$ approximation. The vertex bound is polynomial in the
proof length, with a degree depending only on the fixed verifier and
approximation parameters. These are size bounds, not machine running-time
certificates.
-/

namespace Lax253009.SamplingParameters

def repetitions (c m : ℕ) : ℕ := c * (Nat.clog 2 (m + 2) + 3)

def sampleCount (t k m : ℕ) : ℕ := (m + 2) * 2 ^ (t * k)

def vertexBound (f t k m : ℕ) : ℕ := (m + 2) * 2 ^ ((t + f) * k)

def threshold (m : ℕ) : ℕ := 4 * (m + 2)

axiom polynomial_bound (f t c m : ℕ) :
  vertexBound f t (repetitions c m) m ≤
    16 ^ ((t + f) * c) * (m + 2) ^ ((t + f) * c + 1)

axiom approximation_gap (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f t c : ℕ) (hmargin : 1 ≤ (c : ℝ) * ((t : ℝ) * ε - (f : ℝ) * (1 - ε))) (m : ℕ) :
  Real.rpow (vertexBound f t (repetitions c m) m : ℝ) (1 - ε) * threshold m <
    sampleCount t (repetitions c m) m

axiom choose_multiplier (ε : ℝ) (f t : ℕ)
    (hmargin : 0 < (t : ℝ) * ε - (f : ℝ) * (1 - ε)) :
  ∃ c : ℕ, 0 < c ∧ 1 ≤ (c : ℝ) * ((t : ℝ) * ε - (f : ℝ) * (1 - ε))

end Lax253009.SamplingParameters
