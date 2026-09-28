import Lax253009.MajorityAmplification
import Lax253009Proofs.FiniteProbability

namespace Lax253009Proofs

open Lax253009.FiniteProbability Lax253009.MajorityAmplification
open scoped BigOperators

/--
---
conclusion: Lax253009.MajorityAmplification.majority_error
---
Expand the majority-error indicator and factor the three independent averages.
-/
theorem majority_error_formula {α : Type} [Fintype α] [Nonempty α]
    (answer : α → Bool) (b : Bool) :
    probability (fun r : α × α × α ↦
      vote (answer r.1) (answer r.2.1) (answer r.2.2) ≠ b) =
    errorMap (probability (fun r ↦ answer r ≠ b)) := by
  classical
  let f := fun r ↦ if answer r ≠ b then (1 : ℝ) else 0
  have hi (a c d : α) :
      (if vote (answer a) (answer c) (answer d) ≠ b then (1 : ℝ) else 0) =
        f a * f c + f a * f d + f c * f d - 2 * (f a * f c * f d) := by
    dsimp [f]
    cases answer a <;> cases answer c <;> cases answer d <;> cases b <;> norm_num [vote]
  have hprod {β γ : Type} [Fintype β] [Fintype γ] (g : β × γ → ℝ) :
      (𝔼 r, g r) = 𝔼 a, 𝔼 c, g (a, c) := by
    simpa only [Finset.univ_product_univ] using
      (Finset.expect_product (Finset.univ : Finset β) (Finset.univ : Finset γ) g)
  simp_rw [finite_probability_indicator, hprod, hi]
  simp only [Finset.expect_sub_distrib, Finset.expect_add_distrib,
    ← Finset.expect_mul, ← Finset.mul_expect, Fintype.expect_const, errorMap]
  change (𝔼 a, f a) * (𝔼 a, f a) + (𝔼 a, f a) * (𝔼 a, f a) +
    (𝔼 a, f a) * (𝔼 a, f a) - 2 * ((𝔼 a, f a) * (𝔼 a, f a) * (𝔼 a, f a)) = _
  ring

theorem errorMap_nonneg {p : ℝ} (_hp : 0 ≤ p) (hp' : p ≤ 1) : 0 ≤ errorMap p := by
  unfold errorMap
  nlinarith [mul_nonneg (sq_nonneg p) (show 0 ≤ 3 - 2 * p by linarith)]

theorem errorMap_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    errorMap p ≤ errorMap q := by
  have hq0 : 0 ≤ q := hp.trans hpq
  have hp1 : p ≤ 1 := hpq.trans hq
  have hf : 0 ≤ 3 * (p + q) - 2 * (p*p + p*q + q*q) := by
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hp1),
      mul_nonneg hq0 (sub_nonneg.mpr hq),
      mul_nonneg hp (sub_nonneg.mpr hq),
      mul_nonneg hq0 (sub_nonneg.mpr hp1)]
  unfold errorMap
  nlinarith [mul_nonneg (sub_nonneg.mpr hpq) hf]

/--
---
conclusion: Lax253009.MajorityAmplification.three_rounds
---
The cubic error transformation is increasing on [0,1]. Exact rational bounds
for the three stages are 7/27, 17/100, and 1/12.
-/
theorem majority_three_rounds (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1 / 3) :
    errorMap (errorMap (errorMap p)) ≤ 1 / 12 := by
  have h1 := errorMap_mono hp hp' (by norm_num : (1 / 3 : ℝ) ≤ 1)
  have h1' : errorMap p ≤ 7 / 27 := by norm_num [errorMap] at h1 ⊢; exact h1
  have hn1 := errorMap_nonneg hp (hp'.trans (by norm_num))
  have h2 := errorMap_mono hn1 h1' (by norm_num : (7 / 27 : ℝ) ≤ 1)
  have h2' : errorMap (errorMap p) ≤ 17 / 100 := by norm_num [errorMap] at h2 ⊢; linarith
  have hn2 := errorMap_nonneg hn1 (h1'.trans (by norm_num))
  have h3 := errorMap_mono hn2 h2' (by norm_num : (17 / 100 : ℝ) ≤ 1)
  norm_num [errorMap] at h3 ⊢
  linarith

end Lax253009Proofs
