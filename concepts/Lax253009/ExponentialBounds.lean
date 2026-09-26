import Lax253009.BooleanFourier
import Lax253009.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
---
title: Exponential concentration on finite product spaces
type: theorem
---
For a finite random variable, exponential Markov bounds its upper tail by
$e^{-ut}\mathbb E e^{uX}$ for $u\geq0$.
A centered variable in $[-1,1]$ has exponential moment at most $e^{u^2/2}$.
Independence multiplies these bounds on a uniform finite product space.

For independent uniform signs and real coefficients $a_i$ with
$\sum_i a_i^2\leq v$, $v>0$, the upper tail at $t\geq0$ is at most
$e^{-t^2/(2v)}$, and the absolute tail is at most twice this quantity.
These finite concentration estimates supply the Chernoff step in the
soundness analysis.
-/

namespace Lax253009.ExponentialBounds

open BooleanFourier FiniteProbability
open scoped BigOperators

axiom exponential_markov {α : Type} [Fintype α] [Nonempty α]
    (X : α → ℝ) (t u : ℝ) (hu : 0 ≤ u) :
  probability (fun x ↦ t ≤ X x) ≤ Real.exp (-u * t) * (𝔼 x, Real.exp (u * X x))

axiom bounded_mgf {α : Type} [Fintype α] [Nonempty α]
    (X : α → ℝ) (hX : ∀ x, |X x| ≤ 1) (hmean : (𝔼 x, X x) = 0) (u : ℝ) :
  (𝔼 x, Real.exp (u * X x)) ≤ Real.exp (u ^ 2 / 2)

axiom independent_bounded_upper_tail {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (F : ι → κ → ℝ)
    (hF : ∀ i z, |F i z| ≤ 1) (hmean : ∀ i, (𝔼 z, F i z) = 0)
    (hN : 0 < Fintype.card ι) (t : ℝ) (ht : 0 ≤ t) :
  probability (fun x : ι → κ ↦ t ≤ ∑ i, F i (x i)) ≤
    Real.exp (-t ^ 2 / (2 * Fintype.card ι))

axiom rademacher_mgf {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (u : ℝ) :
  (𝔼 x : Cube ι, Real.exp (u * ∑ i, a i * sign (x i))) ≤
    Real.exp (u ^ 2 / 2 * ∑ i, a i ^ 2)

axiom rademacher_upper_tail {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (v : ℝ) (hv : 0 < v) (hvar : ∑ i, a i ^ 2 ≤ v)
    (t : ℝ) (ht : 0 ≤ t) :
  probability (fun x : Cube ι ↦ t ≤ ∑ i, a i * sign (x i)) ≤
    Real.exp (-t ^ 2 / (2 * v))

axiom rademacher_abs_tail {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (v : ℝ) (hv : 0 < v) (hvar : ∑ i, a i ^ 2 ≤ v)
    (t : ℝ) (ht : 0 ≤ t) :
  probability (fun x : Cube ι ↦ t ≤ |∑ i, a i * sign (x i)|) ≤
    2 * Real.exp (-t ^ 2 / (2 * v))

end Lax253009.ExponentialBounds
