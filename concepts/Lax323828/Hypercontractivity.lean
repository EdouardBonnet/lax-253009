import Lax323828.BooleanFourier
import Mathlib.Algebra.BigOperators.Expect

/-!
---
title: Dimension-independent moments of low-degree Boolean polynomials
type: theorem
---
For a Boolean polynomial with coefficients $c_S$ supported on sets of size
at most $\ell$, its fourth moment satisfies
$\mathbb E P^4\leq 3^{2\ell}(\sum_S c_S^2)^2$.
Equivalently, for a real function of Fourier degree at most $\ell$,
$\mathbb E F^4\leq 3^{2\ell}(\mathbb E F^2)^2$.

The proof is a coordinate induction with Cauchy–Schwarz. Its constant is
independent of the number of coordinates. This is the fourth-moment case
of the hypercontractive estimate used in Lemma 4.13. Multiplication adds
Fourier degrees, so iteration gives dyadic moment bounds. Comparing a
general power with a higher even power then bounds every moment in terms
of degree and second moment, with explicit nonoptimal constants.
-/

namespace Lax323828.Hypercontractivity

open BooleanFourier
open scoped BigOperators

axiom fourth_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (l : ℕ) (hdegree : ∀ S, l < S.card → c S = 0) :
  (𝔼 x : Cube ι, (∑ S, c S * character S x) ^ 4) ≤
    ((3 : ℝ) ^ l * ∑ S, c S ^ 2) ^ 2

axiom fourier_fourth_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (l : ℕ) (hdegree : ∀ S, l < S.card → coefficient F S = 0) :
  (𝔼 x, F x ^ 4) ≤ ((3 : ℝ) ^ l * (𝔼 x, F x ^ 2)) ^ 2

axiom product_degree {ι : Type} [Fintype ι] [DecidableEq ι]
    (F G : Cube ι → ℝ) (l k : ℕ)
    (hF : ∀ S, l < S.card → coefficient F S = 0)
    (hG : ∀ S, k < S.card → coefficient G S = 0) :
  ∀ S, l + k < S.card → coefficient (fun x ↦ F x * G x) S = 0

axiom dyadic_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (l k : ℕ) (hdegree : ∀ S, l < S.card → coefficient F S = 0) :
  (𝔼 x, F x ^ (2 ^ (k + 1))) ≤
    (3 : ℝ) ^ (l * k * 2 ^ k) * (𝔼 x, F x ^ 2) ^ (2 ^ k)

axiom bounded_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (l m : ℕ) (V : ℝ)
    (hdegree : ∀ S, l < S.card → coefficient F S = 0)
    (hvariance : (𝔼 x, F x ^ 2) ≤ V) :
  (𝔼 x, F x ^ m) ≤ 1 + (3 : ℝ) ^ (l * m * 2 ^ m) * V ^ (2 ^ m)

end Lax323828.Hypercontractivity
