import Lax323828.ExponentialBounds
import Lax323828Proofs.ProductMoments
import Lax323828Proofs.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Lax323828Proofs

open Lax323828.BooleanFourier Lax323828.FiniteProbability
open scoped BigOperators

/--
---
conclusion: Lax323828.ExponentialBounds.exponential_markov
---
Each tail point contributes at least exp(u t) to a nonnegative exponential sum.
-/
theorem finite_exponential_markov {α : Type} [Fintype α] [Nonempty α]
    (X : α → ℝ) (t u : ℝ) (hu : 0 ≤ u) :
    probability (fun x ↦ t ≤ X x) ≤ Real.exp (-u * t) * (𝔼 x, Real.exp (u * X x)) := by
  classical
  let bad := Finset.univ.filter fun x ↦ t ≤ X x
  have hs : (bad.card : ℝ) * Real.exp (u * t) ≤ ∑ x, Real.exp (u * X x) := by
    calc
      _ = ∑ _x ∈ bad, Real.exp (u * t) := by simp
      _ ≤ ∑ x ∈ bad, Real.exp (u * X x) := Finset.sum_le_sum fun x hx ↦
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hx).2 hu)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _ _ ↦ (Real.exp_pos _).le)
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hb : probability (fun x ↦ t ≤ X x) ≤
      (𝔼 x, Real.exp (u * X x)) / Real.exp (u * t) := by
    unfold probability
    rw [Fintype.expect_eq_sum_div_card, le_div_iff₀ (Real.exp_pos _), div_mul_eq_mul_div]
    exact (div_le_div_iff_of_pos_right hN).mpr hs
  convert hb using 1
  rw [neg_mul, Real.exp_neg, div_eq_mul_inv, mul_comm]

/--
---
conclusion: Lax323828.ExponentialBounds.bounded_mgf
---
Convexity bounds the exponential by its chord between -u and u. The mean
zero assumption cancels the linear part, leaving cosh(u) ≤ exp(u²/2).
-/
theorem finite_bounded_mgf {α : Type} [Fintype α] [Nonempty α]
    (X : α → ℝ) (hX : ∀ x, |X x| ≤ 1) (hmean : (𝔼 x, X x) = 0) (u : ℝ) :
    (𝔼 x, Real.exp (u * X x)) ≤ Real.exp (u ^ 2 / 2) := by
  have hc (x : α) : Real.exp (u * X x) ≤
      ((1 + X x) / 2) * Real.exp u + ((1 - X x) / 2) * Real.exp (-u) := by
    have hx := abs_le.mp (hX x)
    have h := convexOn_exp.2 (Set.mem_univ u) (Set.mem_univ (-u))
      (show 0 ≤ (1 + X x) / 2 by linarith)
      (show 0 ≤ (1 - X x) / 2 by linarith)
      (show (1 + X x) / 2 + (1 - X x) / 2 = 1 by ring)
    simp only [smul_eq_mul] at h
    have heq : u * X x = (1 + X x) / 2 * u + (1 - X x) / 2 * (-u) := by ring
    rw [heq]
    exact h
  calc
    _ ≤ 𝔼 x, (((1 + X x) / 2) * Real.exp u + ((1 - X x) / 2) * Real.exp (-u)) :=
      Finset.expect_le_expect fun x _ ↦ hc x
    _ = Real.cosh u := by
      simp only [Finset.expect_add_distrib, ← Finset.expect_mul, ← Finset.expect_div,
        Finset.expect_sub_distrib, Fintype.expect_const, hmean, Real.cosh_eq]
      ring
    _ ≤ _ := Real.cosh_le_exp_half_sq u

theorem independent_bounded_mgf {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (F : ι → κ → ℝ)
    (hF : ∀ i z, |F i z| ≤ 1) (hmean : ∀ i, (𝔼 z, F i z) = 0) (u : ℝ) :
    (𝔼 x : ι → κ, Real.exp (u * ∑ i, F i (x i))) ≤
      Real.exp (u ^ 2 / 2 * Fintype.card ι) := by
  classical
  calc
    _ = ∏ i, (𝔼 z, Real.exp (u * F i z)) := by
      simp_rw [Finset.mul_sum, Real.exp_sum]
      exact independent_product_average (fun i z ↦ Real.exp (u * F i z))
    _ ≤ ∏ _i : ι, Real.exp (u ^ 2 / 2) := Finset.prod_le_prod
      (fun i _ ↦ Finset.expect_nonneg fun z _ ↦ (Real.exp_pos _).le)
      (fun i _ ↦ Lax323828.ExponentialBounds.bounded_mgf (F i) (hF i) (hmean i) u)
    _ = _ := by rw [← Real.exp_sum]; simp [mul_comm]

/--
---
conclusion: Lax323828.ExponentialBounds.independent_bounded_upper_tail
---
The coordinate exponential moments multiply; optimize exponential Markov
with u = t/N for N independent centered summands in [-1,1].
-/
theorem independent_bounded_upper_tail {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (F : ι → κ → ℝ)
    (hF : ∀ i z, |F i z| ≤ 1) (hmean : ∀ i, (𝔼 z, F i z) = 0)
    (hN : 0 < Fintype.card ι) (t : ℝ) (ht : 0 ≤ t) :
    probability (fun x : ι → κ ↦ t ≤ ∑ i, F i (x i)) ≤
      Real.exp (-t ^ 2 / (2 * Fintype.card ι)) := by
  have hv : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  calc
    _ ≤ Real.exp (-(t / Fintype.card ι) * t) *
        (𝔼 x : ι → κ, Real.exp ((t / Fintype.card ι) * ∑ i, F i (x i))) :=
      Lax323828.ExponentialBounds.exponential_markov _ _ _ (div_nonneg ht hv.le)
    _ ≤ Real.exp (-(t / Fintype.card ι) * t) *
        Real.exp ((t / Fintype.card ι) ^ 2 / 2 * Fintype.card ι) :=
      mul_le_mul_of_nonneg_left (independent_bounded_mgf F hF hmean _)
        (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring

/--
---
conclusion: Lax323828.ExponentialBounds.rademacher_mgf
---
Factor the exponential moment over independent signs and bound each cosh factor.
-/
theorem finite_rademacher_mgf {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (u : ℝ) :
    (𝔼 x : Cube ι, Real.exp (u * ∑ i, a i * sign (x i))) ≤
      Real.exp (u ^ 2 / 2 * ∑ i, a i ^ 2) := by
  classical
  have hc (i : ι) : (𝔼 b : Bool, Real.exp (u * (a i * sign b))) = Real.cosh (u * a i) := by
    rw [Fintype.expect_eq_sum_div_card]
    simp [sign, Real.cosh_eq, add_comm]
  calc
    _ = ∏ i, Real.cosh (u * a i) := by
      simp_rw [Finset.mul_sum, Real.exp_sum]
      rw [independent_product_average (fun (i : ι) (b : Bool) ↦ Real.exp (u * (a i * sign b)))]
      simp_rw [hc]
    _ ≤ ∏ i, Real.exp ((u * a i) ^ 2 / 2) := Finset.prod_le_prod
      (fun i _ ↦ (Real.cosh_pos _).le) (fun i _ ↦ Real.cosh_le_exp_half_sq _)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/--
---
conclusion: Lax323828.ExponentialBounds.rademacher_upper_tail
---
Apply exponential Markov with u = t/v and optimize the quadratic exponent.
-/
theorem finite_rademacher_upper_tail {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (v : ℝ) (hv : 0 < v) (hvar : ∑ i, a i ^ 2 ≤ v)
    (t : ℝ) (ht : 0 ≤ t) :
    probability (fun x : Cube ι ↦ t ≤ ∑ i, a i * sign (x i)) ≤
      Real.exp (-t ^ 2 / (2 * v)) := by
  calc
    _ ≤ Real.exp (-(t / v) * t) *
        (𝔼 x : Cube ι, Real.exp ((t / v) * ∑ i, a i * sign (x i))) :=
      Lax323828.ExponentialBounds.exponential_markov _ t (t / v) (div_nonneg ht hv.le)
    _ ≤ Real.exp (-(t / v) * t) * Real.exp ((t / v) ^ 2 / 2 * v) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact (Lax323828.ExponentialBounds.rademacher_mgf a _).trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hvar (by positivity)))
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring

/--
---
conclusion: Lax323828.ExponentialBounds.rademacher_abs_tail
---
The absolute tail is the union of the upper tails for a and -a.
-/
theorem finite_rademacher_abs_tail {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (v : ℝ) (hv : 0 < v) (hvar : ∑ i, a i ^ 2 ≤ v)
    (t : ℝ) (ht : 0 ≤ t) :
    probability (fun x : Cube ι ↦ t ≤ |∑ i, a i * sign (x i)|) ≤
      2 * Real.exp (-t ^ 2 / (2 * v)) := by
  have hneg : ∑ i, (-a i) ^ 2 ≤ v := by simpa using hvar
  have heq : (fun x : Cube ι ↦ t ≤ |∑ i, a i * sign (x i)|) =
      (fun x ↦ t ≤ ∑ i, a i * sign (x i) ∨ t ≤ ∑ i, (-a i) * sign (x i)) := by
    funext x
    simp [le_abs, neg_mul, Finset.sum_neg_distrib]
  rw [heq]
  calc
    _ ≤ _ := Lax323828.FiniteProbability.union_bound _ _
    _ ≤ Real.exp (-t ^ 2 / (2 * v)) + Real.exp (-t ^ 2 / (2 * v)) :=
      add_le_add (Lax323828.ExponentialBounds.rademacher_upper_tail a v hv hvar t ht)
        (Lax323828.ExponentialBounds.rademacher_upper_tail (fun i ↦ -a i) v hv hneg t ht)
    _ = _ := by ring

end Lax323828Proofs
