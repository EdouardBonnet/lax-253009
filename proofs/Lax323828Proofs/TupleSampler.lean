import Lax323828.TupleSampler
import Lax323828Proofs.TupleAveraging

namespace Lax323828Proofs

open Lax323828 Lax323828.TupleSampler Lax323828.FiniteProbability
open scoped BigOperators

private def swapCoordinate {I A : Type} [DecidableEq I] (i : I) :
    (A × (I → A)) ≃ (A × (I → A)) where
  toFun p := (p.2 i, Function.update p.2 i p.1)
  invFun p := (p.2 i, Function.update p.2 i p.1)
  left_inv := by rintro ⟨a, z⟩; simp
  right_inv := by rintro ⟨a, z⟩; simp

theorem coordinate_resampling_adjoint {I A : Type} [Fintype I] [DecidableEq I]
    [Fintype A] [Nonempty A] (i : I) (F : (I → A) → ℝ) (f : A → ℝ) :
    (𝔼 a, 𝔼 z : I → A, F (Function.update z i a) * f a) =
      𝔼 z : I → A, F z * f (z i) := by
  have he := Fintype.expect_equiv (swapCoordinate (A := A) i)
    (fun p : A × (I → A) ↦ F (Function.update p.2 i p.1) * f p.1)
    (fun p : A × (I → A) ↦ F p.2 * f (p.2 i))
    (fun p ↦ by simp [swapCoordinate])
  rw [← Finset.expect_product', Finset.univ_product_univ, he]
  rw [← Finset.univ_product_univ, Finset.expect_product]
  exact Fintype.expect_const (ι := A) (𝔼 z : I → A, F z * f (z i))

theorem tuple_sampler_pairing {A : Type} [Fintype A] [Nonempty A]
    (t : ℕ) (S : (Fin t → A) → Prop) (f : A → ℝ) :
    (𝔼 a, mass t S a * f a) =
      𝔼 z : Fin t → A, indicator S z * (𝔼 i, f (z i)) := by
  classical
  calc
    _ = 𝔼 a, 𝔼 i : Fin t, 𝔼 z : Fin t → A,
        indicator S (Function.update z i a) * f a := by
      simp only [mass, Finset.expect_mul]
    _ = 𝔼 i : Fin t, 𝔼 a, 𝔼 z : Fin t → A,
        indicator S (Function.update z i a) * f a := Finset.expect_comm _ _ _
    _ = 𝔼 i : Fin t, 𝔼 z : Fin t → A, indicator S z * f (z i) := by
      apply Finset.expect_congr rfl
      intro i _
      exact coordinate_resampling_adjoint i (indicator S) f
    _ = 𝔼 z : Fin t → A, 𝔼 i : Fin t, indicator S z * f (z i) := Finset.expect_comm _ _ _
    _ = _ := by simp only [← Finset.mul_expect]

/--
---
conclusion: Lax323828.TupleSampler.bounds
---
The sampler mass is an average of indicators.
-/
theorem tuple_sampler_bounds {A : Type} [Fintype A] [Nonempty A]
    (t : ℕ) (ht : 0 < t) (S : (Fin t → A) → Prop) (a : A) :
    0 ≤ mass t S a ∧ mass t S a ≤ 1 := by
  classical
  have : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  unfold mass indicator
  constructor
  · exact Finset.expect_nonneg fun _ _ ↦ Finset.expect_nonneg fun _ _ ↦ by positivity
  · apply Finset.expect_le Finset.univ_nonempty
    intro i _
    apply Finset.expect_le Finset.univ_nonempty
    intro z _
    split_ifs <;> norm_num

/--
---
conclusion: Lax323828.TupleSampler.mean
---
An independently sampled planted letter leaves the uniform tuple law unchanged.
-/
theorem tuple_sampler_mean {A : Type} [Fintype A] [Nonempty A]
    (t : ℕ) (ht : 0 < t) (S : (Fin t → A) → Prop) :
    (𝔼 a, mass t S a) = probability S := by
  classical
  have : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  have h := tuple_sampler_pairing t S (fun _ ↦ (1 : ℝ))
  simpa only [indicator, mul_one, Fintype.expect_const, ← finite_probability_indicator] using h

/--
---
conclusion: Lax323828.TupleSampler.mixing
---
Test the centered sampler density against its sign. The adjoint identity
turns this pairing into the restricted centered tuple average, whose
second moment has already been bounded independently of the alphabet.
-/
theorem tuple_sampler_mixing {A : Type} [Fintype A] [Nonempty A]
    (t : ℕ) (ht : 0 < t) (S : (Fin t → A) → Prop) :
    (𝔼 a, |mass t S a - probability S|) ^ 2 ≤ 1 / (t : ℝ) := by
  classical
  let f := fun a ↦ if 0 ≤ mass t S a - probability S then (1 : ℝ) else -1
  have hf : ∀ a, |f a| ≤ 1 := by intro a; dsimp [f]; split_ifs <;> norm_num
  have he (a : A) : |mass t S a - probability S| = (mass t S a - probability S) * f a := by
    dsimp [f]
    split_ifs with h
    · rw [abs_of_nonneg h, mul_one]
    · rw [abs_of_neg (lt_of_not_ge h)]; ring
  have hp : (𝔼 a, |mass t S a - probability S|) =
      𝔼 z : Fin t → A, if S z then (𝔼 i, f (z i)) - (𝔼 a, f a) else 0 := by
    simp_rw [he, sub_mul, Finset.expect_sub_distrib, ← Finset.mul_expect]
    rw [tuple_sampler_pairing, finite_probability_indicator, Finset.expect_mul]
    rw [← Finset.expect_sub_distrib]
    apply Finset.expect_congr rfl
    intro z _
    unfold indicator
    split_ifs <;> simp
  rw [hp]
  have h := Lax323828.TupleAveraging.restriction_correlation t ht f hf S
  simpa only [sq_abs] using h

end Lax323828Proofs
