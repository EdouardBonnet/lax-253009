import Lax323828.FourierProjection
import Lax323828Proofs.BooleanFourier

namespace Lax323828Proofs

open Lax323828.BooleanFourier Lax323828.FourierProjection

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem average_sum {κ : Type} [Fintype κ] (F : κ → Cube ι → ℝ) :
    average (fun x ↦ ∑ j, F j x) = ∑ j, average (F j) := by
  classical
  simp only [average, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem average_mul (c : ℝ) (F : Cube ι → ℝ) :
    average (fun x ↦ c * F x) = c * average F := by
  unfold average
  rw [← Finset.mul_sum]
  ring

theorem average_const (c : ℝ) : average (fun _ : Cube ι ↦ c) = c := by
  simp [average, mul_div_cancel_left₀]

theorem average_sub (F G : Cube ι → ℝ) :
    average (fun x ↦ F x - G x) = average F - average G := by
  unfold average
  rw [Finset.sum_sub_distrib]
  ring

theorem average_div (F : Cube ι → ℝ) (c : ℝ) :
    average (fun x ↦ F x / c) = average F / c := by
  unfold average
  rw [← Finset.sum_div]
  ring

omit [Fintype ι] in
private theorem character_splice (U S : Finset ι) (x y : Cube ι) :
    character S (splice U x y) = character (S ∩ U) x * character (S \ U) y := by
  simp only [character, splice]
  rw [Finset.prod_apply_ite]
  simp only [Finset.filter_mem_eq_inter, ← Finset.sdiff_eq_filter]

private theorem average_character (S : Finset ι) :
    average (character S) = if S = ∅ then 1 else 0 := by
  convert Lax323828.BooleanFourier.orthogonality S ∅ using 1
  congr 1
  funext x
  simp [character]

private theorem project_character (U S : Finset ι) (x : Cube ι) :
    project (character S) U x = if S ⊆ U then character S x else 0 := by
  unfold project
  simp_rw [character_splice]
  rw [average_mul, average_character]
  by_cases h : S ⊆ U
  · simp [h, Finset.sdiff_eq_empty_iff_subset.mpr h, Finset.inter_eq_left.mpr h]
  · simp [Finset.sdiff_eq_empty_iff_subset, h]

private theorem project_expansion (F : Cube ι → ℝ) (U : Finset ι) (x : Cube ι) :
    project F U x = ∑ S : Finset ι,
      (if S ⊆ U then coefficient F S else 0) * character S x := by
  classical
  unfold project
  conv_lhs => enter [1, y]; rw [Lax323828.BooleanFourier.inversion F]
  rw [average_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [average_mul]
  change coefficient F S * project (character S) U x = _
  rw [project_character]
  split_ifs <;> simp

/--
---
conclusion: Lax323828.FourierProjection.coefficient_project
---
Expand F in characters. Averaging kills a character with any coordinate
outside U; orthogonality then extracts the remaining coefficient.
-/
theorem fourier_projection (F : Cube ι → ℝ) (U S : Finset ι) :
    coefficient (project F U) S = if S ⊆ U then coefficient F S else 0 := by
  classical
  unfold coefficient
  simp_rw [project_expansion, Finset.sum_mul, mul_assoc]
  rw [average_sum]
  simp_rw [average_mul, Lax323828.BooleanFourier.orthogonality]
  simp [coefficient]

/--
---
conclusion: Lax323828.FourierProjection.bounded_project
---
Use the triangle inequality for a finite sum and divide by the cube's cardinality.
-/
theorem fourier_projection_bounded (F : Cube ι → ℝ) (hF : ∀ x, |F x| ≤ 1)
    (U : Finset ι) (x : Cube ι) : |project F U x| ≤ 1 := by
  classical
  have hN : (0 : ℝ) < 2 ^ Fintype.card ι := pow_pos (by norm_num) _
  unfold project average
  rw [abs_div, abs_of_pos hN]
  apply (div_le_iff₀ hN).mpr
  calc
    |∑ y : Cube ι, F (splice U x y)| ≤ ∑ y : Cube ι, |F (splice U x y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y : Cube ι, (1 : ℝ) := Finset.sum_le_sum fun y _ ↦ hF _
    _ = _ := by simp

/--
---
conclusion: Lax323828.FourierProjection.constant_fiber
---
Every term of the averaging sum has the same value.
-/
theorem fourier_projection_constant (F : Cube ι → ℝ) (U : Finset ι) (x : Cube ι)
    (hF : ∀ y, (∀ i ∈ U, y i = x i) → F y = F x) :
    project F U x = F x := by
  unfold project
  have h (y : Cube ι) : F (splice U x y) = F x :=
    hF _ (fun i hi ↦ by simp [splice, hi])
  simp_rw [h]
  exact average_const _

end Lax323828Proofs
