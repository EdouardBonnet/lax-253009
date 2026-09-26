import Lax253009.TupleAveraging
import Lax253009Proofs.ProductMoments
import Lax253009Proofs.FiniteProbability

namespace Lax253009Proofs

open Lax253009 Lax253009.FiniteProbability
open scoped BigOperators

/--
---
conclusion: Lax253009.TupleAveraging.variance_bound
---
Expand the centered second moment. Distinct coordinates have zero mixed
moment by independence; each diagonal variance is at most one.
-/
theorem tuple_variance_bound {A : Type} [Fintype A] [Nonempty A]
    (t : ℕ) (ht : 0 < t) (f : A → ℝ) (hf : ∀ a, |f a| ≤ 1) :
    (𝔼 z : Fin t → A, ((𝔼 i, f (z i)) - (𝔼 a, f a)) ^ 2) ≤ 1 / (t : ℝ) := by
  classical
  have : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  let μ := 𝔼 a, f a
  let g := fun a ↦ f a - μ
  have hg : (𝔼 a, g a) = 0 := by simp [g, μ, Finset.expect_sub_distrib]
  have hs : (𝔼 a, f a ^ 2) ≤ 1 := Finset.expect_le Finset.univ_nonempty fun a _ ↦ by
    have ha := abs_le.mp (hf a)
    nlinarith
  have hv : (𝔼 a, g a ^ 2) ≤ 1 := by
    have he : (𝔼 a, g a ^ 2) = (𝔼 a, f a ^ 2) - μ ^ 2 := by
      calc
        _ = 𝔼 a, (f a ^ 2 - 2 * μ * f a + μ ^ 2) := by
          apply Finset.expect_congr rfl
          intro a _
          dsimp [g]
          ring
        _ = _ := by
          rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
            ← Finset.mul_expect, Fintype.expect_const]
          change (𝔼 a, f a ^ 2) - 2 * μ * μ + μ ^ 2 = _
          ring
    rw [he]
    nlinarith [sq_nonneg μ]
  have hmix (i j : Fin t) : (𝔼 z : Fin t → A, g (z i) * g (z j)) =
      if i = j then (𝔼 a, g a ^ 2) else 0 := by
    have h := balanced_mixed_moment g g hg hg {i} {j}
    simpa only [Finset.prod_singleton, Finset.singleton_inj, Finset.card_singleton,
      pow_one, ← pow_two] using h
  have hsum : (𝔼 z : Fin t → A, (∑ i, g (z i)) ^ 2) =
      (t : ℝ) * (𝔼 a, g a ^ 2) := by
    have h := weighted_sum_second_moment (Finset.univ : Finset (Fin t))
      (fun _ ↦ (1 : ℝ)) (fun i (z : Fin t → A) ↦ g (z i))
    simpa [hmix] using h
  have he (z : Fin t → A) : ((𝔼 i, f (z i)) - (𝔼 a, f a)) ^ 2 =
      (∑ i, g (z i)) ^ 2 / (t : ℝ) ^ 2 := by
    have hm : (𝔼 i : Fin t, g (z i)) = (𝔼 i, f (z i)) - μ := by
      simp [g, Finset.expect_sub_distrib]
    rw [← hm, Fintype.expect_eq_sum_div_card, div_pow]
    simp
  simp_rw [he]
  rw [← Finset.expect_div, hsum]
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  calc
    _ ≤ (t : ℝ) * 1 / (t : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv ht'.le) (sq_nonneg _)
    _ = _ := by field_simp

/--
---
conclusion: Lax253009.TupleAveraging.restriction_correlation
---
Apply Cauchy–Schwarz to the event indicator and the centered sample mean.
The indicator's second moment is at most one.
-/
theorem tuple_restriction_correlation {A : Type} [Fintype A] [Nonempty A]
    (t : ℕ) (ht : 0 < t) (f : A → ℝ) (hf : ∀ a, |f a| ≤ 1)
    (S : (Fin t → A) → Prop) [DecidablePred S] :
    |𝔼 z : Fin t → A, if S z then (𝔼 i, f (z i)) - (𝔼 a, f a) else 0| ^ 2 ≤
      1 / (t : ℝ) := by
  classical
  let X := fun z : Fin t → A ↦ (𝔼 i, f (z i)) - (𝔼 a, f a)
  have hc := Finset.expect_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin t → A))
    (fun z ↦ if S z then (1 : ℝ) else 0) X
  have hi : (𝔼 z, (if S z then (1 : ℝ) else 0) ^ 2) ≤ 1 :=
    Finset.expect_le Finset.univ_nonempty fun z _ ↦ by split_ifs <;> norm_num
  have hv := tuple_variance_bound t ht f hf
  calc
    _ = (𝔼 z, (if S z then (1 : ℝ) else 0) * X z) ^ 2 := by
      rw [sq_abs]
      congr 1
      apply Finset.expect_congr rfl
      intro z _
      split_ifs <;> simp [X]
    _ ≤ _ := hc
    _ ≤ 1 * (𝔼 z, X z ^ 2) := mul_le_mul_of_nonneg_right hi
      (Finset.expect_nonneg fun z _ ↦ sq_nonneg _)
    _ ≤ _ := by simpa [X] using hv

end Lax253009Proofs
