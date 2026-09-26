import Lax253009.BernoulliSampling
import Lax253009Proofs.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Lax253009Proofs

open Lax253009.FiniteProbability Lax253009.BernoulliSampling
open scoped BigOperators Classical

private theorem count_eq_sum {Ω : Type} [Fintype Ω] (N : ℕ) (P : Ω → Prop)
    (z : Fin N → Ω) : (count N P z : ℝ) = ∑ i, if P (z i) then (1 : ℝ) else 0 := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, count]

private theorem indicator_mgf {Ω : Type} [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) :
    (𝔼 z, Real.exp (Real.log 2 * if P z then (1 : ℝ) else 0)) = 1 + probability P := by
  have he (z : Ω) : Real.exp (Real.log 2 * if P z then (1 : ℝ) else 0) =
      1 + if P z then (1 : ℝ) else 0 := by
    by_cases hz : P z <;> norm_num [hz, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simp_rw [he]
  rw [Finset.expect_add_distrib, Fintype.expect_const, ← finite_probability_indicator]

/--
---
conclusion: Lax253009.BernoulliSampling.upper_tail
---
Exponential Markov with parameter log 2. A Bernoulli variable has moment
1+p at this parameter, bounded by exp p; the independent moments multiply.
-/
theorem bernoulli_sampling_tail {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (N : ℕ) (P : Ω → Prop) (p : ℝ) (hp : 0 ≤ p) (hP : probability P ≤ p) :
    probability (fun z : Fin N → Ω ↦ 4 * N * p ≤ (count N P z : ℝ)) ≤
      Real.exp (-(N : ℝ) * p) := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith
  have hmoment : (𝔼 z : Fin N → Ω, Real.exp (Real.log 2 * (count N P z : ℝ))) ≤
      Real.exp ((N : ℝ) * p) := by
    simp_rw [count_eq_sum, Finset.mul_sum, Real.exp_sum]
    rw [independent_product_average (fun (_ : Fin N) z ↦
      Real.exp (Real.log 2 * if P z then (1 : ℝ) else 0))]
    simp_rw [indicator_mgf]
    have hterm : 1 + probability P ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
    calc
      _ ≤ ∏ _i : Fin N, Real.exp p := Finset.prod_le_prod (f := fun _ : Fin N ↦ 1 + probability P)
        (fun _ _ ↦ by linarith [finite_probability_nonneg P])
        (fun _ _ ↦ hterm)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  calc
    _ ≤ Real.exp (-Real.log 2 * (4 * N * p)) *
        (𝔼 z : Fin N → Ω, Real.exp (Real.log 2 * (count N P z : ℝ))) :=
      finite_exponential_markov _ _ _ (by linarith)
    _ ≤ Real.exp (-Real.log 2 * (4 * N * p)) * Real.exp ((N : ℝ) * p) :=
      mul_le_mul_of_nonneg_left hmoment (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hlog (show 0 ≤ (N : ℝ) * p by positivity)
      nlinarith

private theorem sampling_union_budget (m N : ℕ) (p : ℝ)
    (hN : (m : ℝ) + 2 ≤ N * p) :
    (2 : ℝ) ^ m * Real.exp (-(N : ℝ) * p) ≤ 1 / 4 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hm : (2 : ℝ) ^ m ≤ Real.exp (m : ℝ) := by
    simpa only [← Real.exp_nat_mul, mul_one] using pow_le_pow_left₀ (by norm_num) h2 m
  have he : 4 ≤ Real.exp (2 : ℝ) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 2
    norm_num [← Real.exp_nat_mul] at h
    exact h
  calc
    _ ≤ Real.exp (m : ℝ) * Real.exp (-(N : ℝ) * p) :=
      mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
    _ = Real.exp ((m : ℝ) - N * p) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ 1 / 4 := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) he

/--
---
conclusion: Lax253009.BernoulliSampling.uniform_upper_tail
---
Union over every possible proof, then absorb the 2^m factor by choosing
the expected sample count at least m+2.
-/
theorem bernoulli_sampling_uniform {Ω I : Type} [Fintype Ω] [Nonempty Ω] [Fintype I]
    (N m : ℕ) (P : I → Ω → Prop) (p : ℝ) (hp : 0 ≤ p)
    (hI : Fintype.card I ≤ 2 ^ m) (hP : ∀ i, probability (P i) ≤ p)
    (hN : (m : ℝ) + 2 ≤ N * p) :
    probability (fun z : Fin N → Ω ↦ ∃ i, 4 * N * p ≤ (count N (P i) z : ℝ)) ≤ 1 / 4 := by
  calc
    _ ≤ ∑ i : I, probability (fun z : Fin N → Ω ↦ 4 * N * p ≤ (count N (P i) z : ℝ)) :=
      finite_probability_finite_union _
    _ ≤ ∑ _i : I, Real.exp (-(N : ℝ) * p) :=
      Finset.sum_le_sum (fun i _ ↦ bernoulli_sampling_tail N (P i) p hp (hP i))
    _ = (Fintype.card I : ℝ) * Real.exp (-(N : ℝ) * p) := by simp
    _ ≤ (2 : ℝ) ^ m * Real.exp (-(N : ℝ) * p) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hI) (Real.exp_pos _).le
    _ ≤ _ := sampling_union_budget m N p hN

end Lax253009Proofs
