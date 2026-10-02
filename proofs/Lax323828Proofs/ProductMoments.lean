import Lax323828.ProductMoments
import Mathlib.Tactic

namespace Lax323828Proofs

open scoped BigOperators
open Lax323828.ProductMoments

theorem independent_product_average {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (F : ι → κ → ℝ) :
    (𝔼 f : ι → κ, ∏ i, F i (f i)) = ∏ i, (𝔼 z, F i z) := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Nat.cast_pow,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.prod_sum]

/--
---
conclusion: Lax323828.ProductMoments.mixed_moment
---
Factor the expectation coordinate by coordinate. A coordinate in just one
support contributes a zero mean; coordinates in both contribute the correlation.
-/
theorem balanced_mixed_moment {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (B C : κ → ℝ)
    (hB : (𝔼 z, B z) = 0) (hC : (𝔼 z, C z) = 0) (S T : Finset ι) :
    (𝔼 f : ι → κ, (∏ i ∈ S, B (f i)) * (∏ i ∈ T, C (f i))) =
      if S = T then (𝔼 z, B z * C z) ^ S.card else 0 := by
  classical
  have hprod (f : ι → κ) : (∏ i ∈ S, B (f i)) * (∏ i ∈ T, C (f i)) =
      ∏ i, (if i ∈ S then B (f i) else 1) * (if i ∈ T then C (f i) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [hprod]
  rw [independent_product_average (fun (i : ι) (z : κ) ↦
    (if i ∈ S then B z else 1) * (if i ∈ T then C z else 1))]
  by_cases hST : S = T
  · subst T
    rw [if_pos rfl]
    have hi (i : ι) :
        (𝔼 z, (if i ∈ S then B z else 1) * (if i ∈ S then C z else 1)) =
          if i ∈ S then (𝔼 z, B z * C z) else 1 := by
      by_cases h : i ∈ S <;> simp [h]
    simp_rw [hi]
    simp
  · rw [if_neg hST]
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      by_contra hn
      push Not at hn
      exact hST (Finset.ext hn)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;> simp_all

theorem weighted_sum_second_moment {α X : Type} [Fintype X]
    (s : Finset α) (c : α → ℝ) (φ : α → X → ℝ) :
    (𝔼 x, (∑ i ∈ s, c i * φ i x) ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * (𝔼 x, φ i x * φ j x) := by
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum, Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro x _
  ring

/--
---
conclusion: Lax323828.ProductMoments.second_moment
---
Expand the square, interchange finite sums and expectations, and cancel
every pair of distinct supports using the balanced mixed-moment identity.
-/
theorem balanced_second_moment {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (supports : Finset (Finset ι))
    (c : Finset ι → ℝ) (predicates : Finset (κ → ℝ))
    (hbalanced : ∀ B ∈ predicates, (𝔼 z, B z) = 0) :
    (𝔼 f : ι → κ, weightedSum supports c predicates f ^ 2) =
      ∑ S ∈ supports, c S ^ 2 *
        ∑ B ∈ predicates, ∑ C ∈ predicates, (𝔼 z, B z * C z) ^ S.card := by
  classical
  have hfeatures (S T : Finset ι) :
      (𝔼 f : ι → κ, (∑ B ∈ predicates, ∏ i ∈ S, B (f i)) *
        (∑ C ∈ predicates, ∏ i ∈ T, C (f i))) =
      if S = T then
        (∑ B ∈ predicates, ∑ C ∈ predicates, (𝔼 z, B z * C z) ^ S.card) else 0 := by
    calc
      _ = ∑ B ∈ predicates, ∑ C ∈ predicates,
          if S = T then (𝔼 z, B z * C z) ^ S.card else 0 := by
        simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.expect_sum_comm]
        apply Finset.sum_congr rfl
        intro B hB
        apply Finset.sum_congr rfl
        intro C hC
        exact Lax323828.ProductMoments.mixed_moment B C (hbalanced B hB) (hbalanced C hC) S T
      _ = _ := by split_ifs <;> simp
  unfold weightedSum
  rw [weighted_sum_second_moment]
  simp_rw [hfeatures, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro S hS
  simp [hS, pow_two]

theorem correlation_abs_le_one {κ : Type} [Fintype κ] [Nonempty κ]
    (B C : κ → ℝ) (hB : ∀ z, |B z| ≤ 1) (hC : ∀ z, |C z| ≤ 1) :
    |𝔼 z, B z * C z| ≤ 1 := by
  calc
    _ ≤ 𝔼 z, |B z * C z| := Finset.abs_expect_le _ _
    _ ≤ 1 := Finset.expect_le Finset.univ_nonempty fun z _ ↦ by
      rw [abs_mul]
      exact (mul_le_mul (hB z) (hC z) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

/--
---
conclusion: Lax323828.ProductMoments.high_degree_bound
---
Absolute correlations are at most one, so increasing the support size can
only decrease their powers. Sum with nonnegative squared coefficients.
-/
theorem balanced_high_degree_bound {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (supports : Finset (Finset ι))
    (c : Finset ι → ℝ) (predicates : Finset (κ → ℝ)) (l : ℕ)
    (hbalanced : ∀ B ∈ predicates, (𝔼 z, B z) = 0)
    (hbounded : ∀ B ∈ predicates, ∀ z, |B z| ≤ 1)
    (hdegree : ∀ S ∈ supports, l ≤ S.card)
    (henergy : ∑ S ∈ supports, c S ^ 2 ≤ 1) :
    (𝔼 f : ι → κ, weightedSum supports c predicates f ^ 2) ≤
      ∑ B ∈ predicates, ∑ C ∈ predicates, |𝔼 z, B z * C z| ^ l := by
  classical
  let K := ∑ B ∈ predicates, ∑ C ∈ predicates, |𝔼 z, B z * C z| ^ l
  have hK : 0 ≤ K := Finset.sum_nonneg fun B _ ↦
    Finset.sum_nonneg fun C _ ↦ pow_nonneg (abs_nonneg _) _
  have hterm (S : Finset ι) (hS : S ∈ supports) :
      (∑ B ∈ predicates, ∑ C ∈ predicates, (𝔼 z, B z * C z) ^ S.card) ≤ K := by
    apply Finset.sum_le_sum
    intro B hB
    apply Finset.sum_le_sum
    intro C hC
    calc
      (𝔼 z, B z * C z) ^ S.card ≤ |𝔼 z, B z * C z| ^ S.card :=
        (le_abs_self _).trans_eq (abs_pow _ _)
      _ ≤ _ := pow_le_pow_of_le_one (abs_nonneg _)
        (correlation_abs_le_one B C (hbounded B hB) (hbounded C hC)) (hdegree S hS)
  rw [Lax323828.ProductMoments.second_moment supports c predicates hbalanced]
  calc
    _ ≤ ∑ S ∈ supports, c S ^ 2 * K :=
      Finset.sum_le_sum fun S hS ↦ mul_le_mul_of_nonneg_left (hterm S hS) (sq_nonneg _)
    _ = (∑ S ∈ supports, c S ^ 2) * K := (Finset.sum_mul ..).symm
    _ ≤ 1 * K := mul_le_mul_of_nonneg_right henergy hK
    _ = K := one_mul _

end Lax323828Proofs
