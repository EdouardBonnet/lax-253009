import Lax253009.FiniteProbability
import Mathlib.Tactic

namespace Lax253009Proofs

open Lax253009.FiniteProbability
open scoped BigOperators

/--
---
conclusion: Lax253009.FiniteProbability.monotone
---
Count the included event and divide by the size of the common sample space.
-/
theorem finite_probability_mono {α : Type} [Fintype α]
    (P Q : α → Prop) (h : ∀ x, P x → Q x) : probability P ≤ probability Q := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show Finset.univ.filter P ⊆ Finset.univ.filter Q from
    fun x hx ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x (Finset.mem_filter.mp hx).2⟩)

/--
---
conclusion: Lax253009.FiniteProbability.union_bound
---
The cardinality of a union is at most the sum of the two cardinalities.
-/
theorem finite_probability_union {α : Type} [Fintype α] (P Q : α → Prop) :
    probability (fun x ↦ P x ∨ Q x) ≤ probability P + probability Q := by
  classical
  unfold probability
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := Finset.card_union_le (Finset.univ.filter P) (Finset.univ.filter Q)
  rw [← Finset.filter_or] at h
  norm_cast
  convert h using 1
  congr 1
  ext x
  simp

/--
---
conclusion: Lax253009.FiniteProbability.even_moment_bound
---
Every point of the tail contributes at least t^m to a nonnegative moment sum.
-/
theorem finite_even_moment_bound {α : Type} [Fintype α] [Nonempty α]
    (X : α → ℝ) (t : ℝ) (ht : 0 < t) (m : ℕ) (hm : Even m) :
    probability (fun x ↦ t ≤ X x) ≤ (𝔼 x, X x ^ m) / t ^ m := by
  classical
  let bad := Finset.univ.filter fun x ↦ t ≤ X x
  have hsum : (bad.card : ℝ) * t ^ m ≤ ∑ x, X x ^ m := by
    calc
      _ = ∑ _x ∈ bad, t ^ m := by simp
      _ ≤ ∑ x ∈ bad, X x ^ m := Finset.sum_le_sum fun x hx ↦
        pow_le_pow_left₀ ht.le (Finset.mem_filter.mp hx).2 m
      _ ≤ ∑ x, X x ^ m := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun x _ _ ↦ hm.pow_nonneg (X x))
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  unfold probability
  rw [Fintype.expect_eq_sum_div_card, le_div_iff₀ (pow_pos ht m), div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right hN).mpr hsum

end Lax253009Proofs
