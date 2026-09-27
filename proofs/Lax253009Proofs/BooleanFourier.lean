import Lax253009.BooleanFourier
import Mathlib.Tactic

namespace Lax253009Proofs

open Lax253009.BooleanFourier

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sign_sq (b : Bool) : sign b * sign b = 1 := by cases b <;> norm_num [sign]

theorem character_univ (S : Finset ι) (x : Cube ι) :
    character S x = ∏ i, if i ∈ S then sign (x i) else 1 := by
  simp [character]

omit [DecidableEq ι] in
private theorem character_kernel (x y : Cube ι) :
    ∑ S : Finset ι, character S x * character S y =
      if x = y then (2 : ℝ) ^ Fintype.card ι else 0 := by
  classical
  have hprod : (∑ S : Finset ι, character S x * character S y) =
      ∏ i, (1 + sign (x i) * sign (y i)) := by
    simpa [character, Finset.prod_mul_distrib] using
      (Finset.prod_one_add (f := fun i ↦ sign (x i) * sign (y i)) Finset.univ).symm
  rw [hprod]
  by_cases hxy : x = y
  · subst y
    norm_num [sign_sq]
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hx : x i <;> cases hy : y i <;> simp_all [sign]

/--
---
conclusion: Lax253009.BooleanFourier.orthogonality
---
The sum factors coordinate by coordinate. A coordinate belonging to exactly
one support contributes zero, and otherwise every coordinate contributes two.
-/
theorem fourier_orthogonality (S T : Finset ι) :
    average (fun x ↦ character S x * character T x) = if S = T then 1 else 0 := by
  classical
  have hfactor : (∑ x : Cube ι, character S x * character T x) =
      ∏ i, ∑ b : Bool, (if i ∈ S then sign b else 1) *
        (if i ∈ T then sign b else 1) := by
    simp_rw [character_univ, ← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun (i : ι) (b : Bool) ↦
      (if i ∈ S then sign b else 1) * (if i ∈ T then sign b else 1))).symm
  unfold average
  rw [hfactor]
  by_cases hST : S = T
  · subst T
    simp only [ite_true]
    have hi (i : ι) : (∑ b : Bool, (if i ∈ S then sign b else 1) *
        (if i ∈ S then sign b else 1)) = 2 := by
      by_cases h : i ∈ S <;> norm_num [h, sign]
    simp_rw [hi]
    simp
  · rw [if_neg hST]
    have hz : (∏ i, ∑ b : Bool, (if i ∈ S then sign b else 1) *
        (if i ∈ T then sign b else 1)) = 0 := by
      obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
        by_contra h
        push Not at h
        exact hST (Finset.ext h)
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;>
        simp_all [sign]
    rw [hz, zero_div]

/--
---
conclusion: Lax253009.BooleanFourier.inversion
---
Expand the coefficients and interchange the two finite sums. The character
kernel vanishes away from x and equals the size of the cube at x.
-/
theorem fourier_inversion (F : Cube ι → ℝ) (x : Cube ι) :
    F x = ∑ S, coefficient F S * character S x := by
  classical
  have hN : (2 : ℝ) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (by norm_num)
  symm
  calc
    _ = (∑ S, ∑ y : Cube ι, F y * character S y * character S x) /
        (2 : ℝ) ^ Fintype.card ι := by
      simp only [coefficient, average, div_mul_eq_mul_div, Finset.sum_mul, Finset.sum_div]
    _ = (∑ y : Cube ι, F y * (∑ S : Finset ι, character S y * character S x)) /
        (2 : ℝ) ^ Fintype.card ι := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, mul_assoc]
    _ = F x := by
      simp_rw [character_kernel]
      simp [hN]

theorem fourier_inner (F G : Cube ι → ℝ) :
    ∑ S, coefficient F S * coefficient G S = average (fun x ↦ F x * G x) := by
  classical
  calc
    _ = (∑ S, ∑ x : Cube ι, F x * character S x * coefficient G S) /
        (2 : ℝ) ^ Fintype.card ι := by
      simp only [coefficient, average, div_mul_eq_mul_div, Finset.sum_mul, Finset.sum_div]
    _ = (∑ x : Cube ι, F x * (∑ S, coefficient G S * character S x)) /
        (2 : ℝ) ^ Fintype.card ι := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = _ := by simp_rw [← Lax253009.BooleanFourier.inversion]; rfl

/--
---
conclusion: Lax253009.BooleanFourier.parseval
---
Specialize preservation of the uniform inner product to F with itself.
-/
theorem fourier_parseval (F : Cube ι → ℝ) :
    ∑ S, coefficient F S ^ 2 = average (fun x ↦ F x ^ 2) := by
  simpa only [pow_two] using fourier_inner F F

/--
---
conclusion: Lax253009.BooleanFourier.boolean_energy
---
Apply Parseval and use that every sign has square one.
-/
theorem fourier_boolean_energy (A : Cube ι → Bool) :
    ∑ S, coefficient (fun x ↦ sign (A x)) S ^ 2 = 1 := by
  rw [Lax253009.BooleanFourier.parseval]
  simp [average, pow_two, sign_sq]

/--
---
conclusion: Lax253009.BooleanFourier.bounded_energy
---
Parseval also bounds the energy of the real-valued averaged tables used
for side conditions, since every pointwise square is at most one.
-/
theorem fourier_bounded_energy (F : Cube ι → ℝ) (hF : ∀ x, |F x| ≤ 1) :
    ∑ S, coefficient F S ^ 2 ≤ 1 := by
  rw [Lax253009.BooleanFourier.parseval]
  unfold average
  rw [div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)]
  calc
    ∑ x, F x ^ 2 ≤ ∑ _x : Cube ι, (1 : ℝ) :=
      Finset.sum_le_sum fun x _ ↦ (sq_le_one_iff_abs_le_one (F x)).mpr (hF x)
    _ = _ := by simp

end Lax253009Proofs
