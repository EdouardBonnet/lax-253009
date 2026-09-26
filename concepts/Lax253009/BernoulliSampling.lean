import Lax253009.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Pi

/-!
---
title: Multiplicative soundness bounds for sampled tests
type: theorem
---
If a test accepts with probability at most $p$, the probability that at
least $4Np$ of $N$ independent samples accept is at most $e^{-Np}$.
The exponent is linear in $p$, which is essential for the randomized
PCP-to-clique reduction: an additive bound with exponent $Np^2$ gives
a weaker approximation exponent.

For a family of at most $2^m$ tests, a union bound gives failure probability
at most $2^m e^{-Np}$. If $Np\geq m+2$, this is at most $1/4$.
-/

namespace Lax253009.BernoulliSampling

open FiniteProbability

noncomputable def count {Ω : Type} [Fintype Ω] (N : ℕ) (P : Ω → Prop)
    (z : Fin N → Ω) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i ↦ P (z i))).card

axiom upper_tail {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (N : ℕ) (P : Ω → Prop) (p : ℝ) (hp : 0 ≤ p) (hP : probability P ≤ p) :
    probability (fun z : Fin N → Ω ↦ 4 * N * p ≤ (count N P z : ℝ)) ≤
      Real.exp (-(N : ℝ) * p)

axiom uniform_upper_tail {Ω I : Type} [Fintype Ω] [Nonempty Ω] [Fintype I]
    (N m : ℕ) (P : I → Ω → Prop) (p : ℝ) (hp : 0 ≤ p)
    (hI : Fintype.card I ≤ 2 ^ m) (hP : ∀ i, probability (P i) ≤ p)
    (hN : (m : ℝ) + 2 ≤ N * p) :
    probability (fun z : Fin N → Ω ↦ ∃ i, 4 * N * p ≤ (count N (P i) z : ℝ)) ≤ 1 / 4

end Lax253009.BernoulliSampling
