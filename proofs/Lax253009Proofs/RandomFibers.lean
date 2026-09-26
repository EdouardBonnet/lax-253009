import Lax253009.RandomFibers
import Lax253009Proofs.ExponentialBounds

namespace Lax253009Proofs

open Lax253009.RandomFibers Lax253009.FiniteProbability
open scoped BigOperators

/--
---
conclusion: Lax253009.RandomFibers.small_fiber
---
Apply the independent bounded-variable tail bound to the negative centered
indicator of membership in the fiber.
-/
theorem random_small_fiber {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] (hN : 0 < Fintype.card ι) (z : κ) :
    probability (fun f : ι → κ ↦ (fiber f z).card <
        (Fintype.card ι : ℝ) / (2 * Fintype.card κ)) ≤
      Real.exp (-(Fintype.card ι : ℝ) / (8 * (Fintype.card κ : ℝ) ^ 2)) := by
  classical
  let q : ℝ := (Fintype.card κ : ℝ)⁻¹
  let X : κ → ℝ := fun a ↦ q - if a = z then 1 else 0
  have hM : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hNr : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  have hq0 : 0 ≤ q := inv_nonneg.mpr hM.le
  have hq1 : q ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact_mod_cast (show 1 ≤ Fintype.card κ from Fintype.card_pos)
  have hX : ∀ a, |X a| ≤ 1 := by
    intro a
    apply abs_le.mpr
    dsimp [X]
    split_ifs <;> constructor <;> linarith
  have hm : (𝔼 a, X a) = 0 := by
    have hi : (𝔼 a : κ, if a = z then (1 : ℝ) else 0) = q := by
      rw [Fintype.expect_eq_sum_div_card]
      simp [q]
    simp only [X, Finset.expect_sub_distrib, Fintype.expect_const, hi, sub_self]
  have hs (f : ι → κ) : (∑ i, X (f i)) =
      (Fintype.card ι : ℝ) * q - (fiber f z).card := by
    simp only [X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [← Finset.sum_filter]
    simp [fiber]
  let t : ℝ := (Fintype.card ι : ℝ) / (2 * Fintype.card κ)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htwice : (Fintype.card ι : ℝ) * q = 2 * t := by
    dsimp [q, t]
    ring
  calc
    _ ≤ probability (fun f : ι → κ ↦ t ≤ ∑ i, X (f i)) := by
      apply finite_probability_mono
      intro f hf
      rw [hs, htwice]
      change (fiber f z).card < t at hf
      linarith
    _ ≤ Real.exp (-t ^ 2 / (2 * Fintype.card ι)) :=
      independent_bounded_upper_tail (fun _ ↦ X) (fun _ ↦ hX) (fun _ ↦ hm) hN t ht
    _ = _ := by
      congr 1
      dsimp [t]
      field_simp
      ring

/--
---
conclusion: Lax253009.RandomFibers.any_small_fiber
---
Take the union bound over all possible labels of a fiber.
-/
theorem random_any_small_fiber {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] (hN : 0 < Fintype.card ι) :
    probability (fun f : ι → κ ↦ ∃ z, (fiber f z).card <
        (Fintype.card ι : ℝ) / (2 * Fintype.card κ)) ≤
      (Fintype.card κ : ℝ) *
        Real.exp (-(Fintype.card ι : ℝ) / (8 * (Fintype.card κ : ℝ) ^ 2)) := by
  calc
    _ ≤ ∑ z, probability (fun f : ι → κ ↦ (fiber f z).card <
        (Fintype.card ι : ℝ) / (2 * Fintype.card κ)) := finite_probability_finite_union _
    _ ≤ ∑ _z : κ, Real.exp (-(Fintype.card ι : ℝ) / (8 * (Fintype.card κ : ℝ) ^ 2)) :=
      Finset.sum_le_sum fun z _ ↦ random_small_fiber hN z
    _ = _ := by simp

end Lax253009Proofs
