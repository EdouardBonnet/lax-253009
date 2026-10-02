import Lax323828.LargeCoefficientSoundness
import Lax323828Proofs.BalancedCancellation

namespace Lax323828Proofs

open Lax323828.BooleanFourier Lax323828.BalancedPredicates Lax323828.HighDegreeSoundness
open scoped BigOperators

private theorem isolated_label_correlation {ι κ : Type} [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (n : ℕ) (hN : Fintype.card κ = 2 * n)
    (S : Finset ι) (l : ℕ) (f : ι → κ) (y : ι) (hy : y ∈ S)
    (hsize : S.card ≤ l) (hl : l < Fintype.card κ)
    (hisolated : ∀ i ∈ S, i ≠ y → f i ≠ f y) :
    |𝔼 B : predicates κ n, ∏ i ∈ S, sign (B.val (f i))| ≤
      (l : ℝ) / ((Fintype.card κ : ℝ) - l) := by
  classical
  let U := (S.erase y).image f
  let F : Cube κ → ℝ := fun B ↦ ∏ i ∈ S.erase y, sign (B (f i))
  have hF (B : Cube κ) : |F B| ≤ 1 := by
    dsimp only [F]
    rw [Finset.abs_prod]
    have hs (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]
    simp [hs]
  have hdepends (B C : Cube κ) (h : ∀ z ∈ U, B z = C z) : F B = F C := by
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg sign (h (f i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  have hyU : f y ∉ U := by
    intro h
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
    exact hisolated i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1 he
  have hb := Lax323828.BalancedCancellation.bounded_support_correlation n hN U F hF hdepends (f y) hyU
  have he (B : predicates κ n) : (∏ i ∈ S, sign (B.val (f i))) = sign (B.val (f y)) * F B.val :=
    (Finset.mul_prod_erase S (fun i ↦ sign (B.val (f i))) hy).symm
  simp_rw [he]
  apply hb.trans
  have hU : U.card ≤ l := Finset.card_image_le.trans (Finset.card_erase_le.trans hsize)
  have hUr : (U.card : ℝ) ≤ l := by exact_mod_cast hU
  have hlr : (l : ℝ) < Fintype.card κ := by exact_mod_cast hl
  apply (div_le_div_iff₀ (by linarith : 0 < (Fintype.card κ : ℝ) - U.card)
    (by linarith : 0 < (Fintype.card κ : ℝ) - l)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card κ)]

/--
---
conclusion: Lax323828.LargeCoefficientSoundness.bound
---
Cancel each isolated distinguished label. The sum of coefficient magnitudes
is at most 1/δ because δ|c| ≤ c² on all retained supports.
-/
theorem large_coefficient_bound {ι κ : Type} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hN : Fintype.card κ = 2 * n)
    (supports : Finset (Finset ι)) (c : Finset ι → ℝ) (l : ℕ)
    (f : ι → κ) (y : ι) (δ : ℝ) (hδ : 0 < δ) (hl : l < Fintype.card κ)
    (hsupport : ∀ S ∈ supports, y ∈ S ∧ S.card ≤ l ∧ ∀ i ∈ S, i ≠ y → f i ≠ f y)
    (hlarge : ∀ S ∈ supports, δ ≤ |c S|) (henergy : ∑ S ∈ supports, c S ^ 2 ≤ 1) :
    |normalizedSum supports c n f| ≤ (l : ℝ) / ((Fintype.card κ : ℝ) - l) / δ := by
  classical
  let L := (l : ℝ) / ((Fintype.card κ : ℝ) - l)
  have hL : 0 ≤ L := div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hl.le))
  have hmass : ∑ S ∈ supports, |c S| ≤ 1 / δ := by
    apply (le_div_iff₀ hδ).mpr
    calc
      _ = ∑ S ∈ supports, |c S| * δ := Finset.sum_mul ..
      _ ≤ ∑ S ∈ supports, c S ^ 2 := by
        apply Finset.sum_le_sum
        intro S hS
        have h := mul_le_mul_of_nonneg_left (hlarge S hS) (abs_nonneg (c S))
        simpa only [← sq, sq_abs] using h
      _ ≤ 1 := henergy
  unfold normalizedSum
  calc
    _ ≤ ∑ S ∈ supports, |c S * (𝔼 B : predicates κ n, ∏ i ∈ S, sign (B.val (f i)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ supports, |c S| * L := by
      apply Finset.sum_le_sum
      intro S hS
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (isolated_label_correlation n hN S l f y (hsupport S hS).1
          (hsupport S hS).2.1 hl (hsupport S hS).2.2) (abs_nonneg _)
    _ = (∑ S ∈ supports, |c S|) * L := (Finset.sum_mul ..).symm
    _ ≤ (1 / δ) * L := mul_le_mul_of_nonneg_right hmass hL
    _ = _ := by dsimp [L]; ring

end Lax323828Proofs
