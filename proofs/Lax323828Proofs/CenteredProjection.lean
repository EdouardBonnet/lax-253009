import Lax323828.CenteredProjection
import Lax323828Proofs.TupleFortification
import Lax323828Proofs.FortifiedSquaring
import Lax323828Proofs.ProjectionGames

namespace Lax323828Proofs

open Lax323828 Lax323828.FiniteProbability Lax323828.FortifiedSquaring
open Lax323828.TupleFortification
open scoped BigOperators

namespace CenteredProjection

open Lax323828.CenteredProjection

def swapLast (U Ω : Type) : (U × (Ω × Ω)) ≃ (Ω × (U × Ω)) where
  toFun z := (z.2.2, (z.1, z.2.1))
  invFun z := (z.2.1, (z.2.2, z.1))
  left_inv _ := rfl
  right_inv _ := rfl

/--
---
conclusion: Lax323828.CenteredProjection.symmetrize_sound
---
-/
theorem symmetrize_sound {U Ω W X Y : Type}
    [Fintype U] [Fintype Ω] [Nonempty Ω]
    (G : System U Ω W X Y) (s : ℝ) (h : G.Sound s) : G.symmetrize.Sound s := by
  intro P Q
  rw [finite_probability_equiv (swapLast U Ω) (G.symmetrize.Wins P Q)
    (fun z ↦ G.symmetrize.Wins P Q ((swapLast U Ω).symm z)) (fun _ ↦ Iff.rfl)]
  apply finite_probability_product_bound (β := U × Ω)
    (fun ω z ↦ G.symmetrize.Wins P Q ((swapLast U Ω).symm (ω, z))) s
  intro ω
  apply le_trans (Lax323828.FiniteProbability.monotone _ _ ?_)
    (h P (fun u ↦ G.project u ω (Q (G.question u ω))))
  intro z hz
  exact ⟨hz.1, hz.2.2⟩

theorem symmetrize_uniform_left {U Ω W X Y : Type}
    [Fintype U] [Fintype Ω] [Nonempty Ω] [Fintype W]
    (G : System U Ω W X Y) (h : G.Uniform) (f : W → ℝ) :
    (𝔼 z, f (G.symmetrize.left z)) = 𝔼 w, f w := by
  change (𝔼 z : U × (Ω × Ω), f (G.question z.1 z.2.1)) = _
  rw [← Finset.univ_product_univ, Finset.expect_product]
  simp_rw [← Finset.univ_product_univ, Finset.expect_product, Fintype.expect_const]
  exact h f

theorem symmetrize_uniform_right {U Ω W X Y : Type}
    [Fintype U] [Fintype Ω] [Nonempty Ω] [Fintype W]
    (G : System U Ω W X Y) (h : G.Uniform) (f : W → ℝ) :
    (𝔼 z, f (G.symmetrize.right z)) = 𝔼 w, f w := by
  change (𝔼 z : U × (Ω × Ω), f (G.question z.1 z.2.2)) = _
  rw [← Finset.univ_product_univ, Finset.expect_product]
  simp_rw [← Finset.univ_product_univ, Finset.expect_product, Fintype.expect_const]
  exact h f

/--
---
conclusion: Lax323828.CenteredProjection.fortify_complete
---
-/
theorem fortify_complete {U Ω W X Y : Type}
    (G : System U Ω W X Y) (h : G.Complete) (t : ℕ) : (G.fortify t).Complete := by
  obtain ⟨P, Q, h⟩ := h
  refine ⟨fun w i ↦ P (w i), Q, ?_⟩
  intro u ω
  simpa [System.Test, System.fortify, plant] using h u ω.1

/--
---
conclusion: Lax323828.CenteredProjection.tensor_complete
---
-/
theorem tensor_complete {U Ω W X Y : Type}
    (G : System U Ω W X Y) (h : G.Complete) : G.tensor.Complete := by
  obtain ⟨P, Q, h⟩ := h
  refine ⟨fun w ↦ (P w.1, P w.2), fun u ↦ (Q u.1, Q u.2), ?_⟩
  intro u ω
  exact ⟨by simp [System.tensor, (h u.1 ω.1).1, (h u.2 ω.2).1],
    Prod.ext (h u.1 ω.1).2 (h u.2 ω.2).2⟩

/--
---
conclusion: Lax323828.CenteredProjection.fortify_uniform
---
-/
theorem fortify_uniform {U Ω W X Y : Type}
    [Fintype U] [Fintype Ω] [Fintype W] [Nonempty W]
    (G : System U Ω W X Y) (h : G.Uniform) (t : ℕ) (ht : 0 < t) :
    (G.fortify t).Uniform := by
  intro f
  change (𝔼 u, 𝔼 ω : Ω × History t W, f (plant (G.question u ω.1) ω.2)) = _
  simp_rw [← Finset.univ_product_univ, Finset.expect_product]
  have hh := h (fun w ↦ 𝔼 h : History t W, f (plant w h))
  simp only [← Finset.univ_product_univ, Finset.expect_product] at hh
  rw [hh]
  simpa only [← Finset.univ_product_univ, Finset.expect_product]
    using TupleLift.plant_uniform t ht f

/--
---
conclusion: Lax323828.CenteredProjection.tensor_uniform
---
-/
theorem tensor_uniform {U Ω W X Y : Type}
    [Fintype U] [Fintype Ω] [Fintype W]
    (G : System U Ω W X Y) (h : G.Uniform) : G.tensor.Uniform := by
  intro f
  change (𝔼 u : U × U, 𝔼 ω : Ω × Ω,
    f (G.question u.1 ω.1, G.question u.2 ω.2)) = _
  simp_rw [← Finset.univ_product_univ, Finset.expect_product]
  calc
    _ = 𝔼 u, 𝔼 ω, 𝔼 v, 𝔼 ν, f (G.question u ω, G.question v ν) := by
      apply Finset.expect_congr rfl
      intro u _
      exact Finset.expect_comm _ _ _
    _ = 𝔼 u, 𝔼 ω, 𝔼 w, f (G.question u ω, w) := by
      apply Finset.expect_congr rfl
      intro u _
      apply Finset.expect_congr rfl
      intro ω _
      exact h (fun w ↦ f (G.question u ω, w))
    _ = _ := h (fun v ↦ 𝔼 w, f (v, w))

def fortifyEquiv (U Ω W : Type) (t : ℕ) :
    (U × ((Ω × History t W) × (Ω × History t W))) ≃
      ((U × (Ω × Ω)) × (History t W × History t W)) where
  toFun z := ((z.1, (z.2.1.1, z.2.2.1)), (z.2.1.2, z.2.2.2))
  invFun z := (z.1.1, ((z.1.2.1, z.2.1), (z.1.2.2, z.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

theorem fortify_sym_sound {U Ω W X Y : Type}
    [Fintype U] [Fintype Ω] [Fintype W] [Nonempty W] [DecidableEq W] [Fintype Y]
    (G : System U Ω W X Y) (t : ℕ) (ht : 0 < t) (s : ℝ)
    (h : G.symmetrize.Sound s) : (G.fortify t).symmetrize.Sound s := by
  intro P Q
  rw [finite_probability_equiv (fortifyEquiv U Ω W t) ((G.fortify t).symmetrize.Wins P Q)
    ((lift G.symmetrize t).Wins P Q) (fun _ ↦ Iff.rfl)]
  exact Lax323828.TupleFortification.soundness G.symmetrize t ht s h P Q

theorem fortify_sym_fortified {U Ω W X Y : Type}
    [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
    [Fintype W] [Nonempty W] [DecidableEq W] [Fintype Y] [Nonempty Y]
    (G : System U Ω W X Y) (hu : G.Uniform)
    (t : ℕ) (ht : 0 < t) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (h : G.symmetrize.Sound s) (r : ℝ) (hr : 0 ≤ r) (htr : 1 / (t : ℝ) ≤ r ^ 2) :
    (G.fortify t).symmetrize.Fortified s (4 * r) := by
  intro P Q S T
  rw [finite_probability_equiv (fortifyEquiv U Ω W t)
    (fun z ↦ (G.fortify t).symmetrize.Wins P Q z ∧ S ((G.fortify t).symmetrize.left z) ∧
      T ((G.fortify t).symmetrize.right z))
    (fun z ↦ (lift G.symmetrize t).Wins P Q z ∧ S ((lift G.symmetrize t).left z) ∧
      T ((lift G.symmetrize t).right z)) (fun _ ↦ Iff.rfl)]
  rw [finite_probability_equiv (fortifyEquiv U Ω W t)
    (fun z ↦ S ((G.fortify t).symmetrize.left z) ∧ T ((G.fortify t).symmetrize.right z))
    (fun z ↦ S ((lift G.symmetrize t).left z) ∧ T ((lift G.symmetrize t).right z))
    (fun _ ↦ Iff.rfl)]
  exact Lax323828.TupleFortification.fortification G.symmetrize (symmetrize_uniform_left G hu)
    (symmetrize_uniform_right G hu) s hs hs1 h t ht r hr htr P Q S T

def tensorEquiv (U Ω : Type) :
    ((U × U) × ((Ω × Ω) × (Ω × Ω))) ≃
      ((U × (Ω × Ω)) × (U × (Ω × Ω))) where
  toFun z := ((z.1.1, (z.2.1.1, z.2.2.1)), (z.1.2, (z.2.1.2, z.2.2.2)))
  invFun z := ((z.1.1, z.2.1), ((z.1.2.1, z.2.2.1), (z.1.2.2, z.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

theorem tensor_sym_probability {U Ω W X Y : Type} [Fintype U] [Fintype Ω]
    (G : System U Ω W X Y) (P Q : W × W → Y × Y) :
    probability (G.tensor.symmetrize.Wins P Q) = probability (G.symmetrize.DoubleWins P Q) := by
  apply finite_probability_equiv (tensorEquiv U Ω)
  intro z
  simp only [Game.Wins, Game.DoubleWins, Game.Test, System.symmetrize, System.tensor,
    tensorEquiv, Equiv.coe_fn_mk, Bool.and_eq_true, Prod.mk.injEq]
  tauto

/--
---
conclusion: Lax323828.CenteredProjection.fortify_square_sound
---
-/
theorem fortify_square_sound {U Ω W X Y : Type}
    [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
    [Fintype W] [Nonempty W] [DecidableEq W]
    [Fintype X] [Fintype Y] [Nonempty Y]
    (G : System U Ω W X Y) (hu : G.Uniform)
    (t : ℕ) (ht : 0 < t) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (h : G.symmetrize.Sound s) (r : ℝ) (hr : 0 ≤ r) (htr : 1 / (t : ℝ) ≤ r ^ 2) :
    (G.fortify t).tensor.symmetrize.Sound (s ^ 2 + (Fintype.card X : ℝ) * (4 * r)) := by
  have : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  intro P Q
  rw [tensor_sym_probability]
  simpa only [pow_two] using Lax323828.FortifiedSquaring.soundness (G.fortify t).symmetrize s s (4 * r) hs
    (fortify_sym_sound G t ht s h)
    (fortify_sym_fortified G hu t ht s hs hs1 h r hr htr) P Q

/--
---
conclusion: Lax323828.CenteredProjection.center_sound_of_sym
---
-/
theorem center_sound_of_sym {U Ω W X Y : Type}
    [Fintype U] [Nonempty U] [Fintype Ω]
    (G : System U Ω W X Y) (s : ℝ) (hs : 0 ≤ s)
    (h : G.symmetrize.Sound (s ^ 2)) : G.Sound s := by
  classical
  intro P Q
  let E := fun u ω ↦ G.Test u ω (P (G.question u ω)) (Q u)
  have hprod (u : U) :
      probability (fun z : Ω × Ω ↦ E u z.1 ∧ E u z.2) = probability (E u) ^ 2 := by
    rw [TupleLift.probability_indicator, TupleLift.probability_indicator]
    rw [← Finset.univ_product_univ, Finset.expect_product]
    have hi (ω ν : Ω) :
        TupleSampler.indicator (fun z : Ω × Ω ↦ E u z.1 ∧ E u z.2) (ω, ν) =
          TupleSampler.indicator (E u) ω * TupleSampler.indicator (E u) ν := by
      by_cases hω : E u ω <;> by_cases hν : E u ν <;>
        simp [TupleSampler.indicator, hω, hν]
    simp_rw [hi, ← Finset.mul_expect, ← Finset.expect_mul, pow_two]
  have hle : (𝔼 u, probability (E u) ^ 2) ≤ probability (G.symmetrize.Wins P P) := by
    simp_rw [← hprod]
    rw [← finite_probability_product (fun (u : U) (z : Ω × Ω) ↦ E u z.1 ∧ E u z.2)]
    exact Lax323828.FiniteProbability.monotone _ _ (fun z hz ↦
      ⟨hz.1.1, hz.2.1, hz.1.2.trans hz.2.2.symm⟩)
  have hc : (𝔼 u, probability (E u)) ^ 2 ≤ 𝔼 u, probability (E u) ^ 2 := by
    have hh := Finset.expect_mul_sq_le_sq_mul_sq (Finset.univ : Finset U)
      (fun _ ↦ (1 : ℝ)) (fun u ↦ probability (E u))
    simpa only [one_mul, one_pow, Fintype.expect_const] using hh
  have he : probability (fun z : U × Ω ↦ E z.1 z.2) = 𝔼 u, probability (E u) :=
    finite_probability_product E
  change probability (fun z : U × Ω ↦ E z.1 z.2) ≤ s
  have hr := hc.trans (hle.trans (h P P))
  rw [he]
  nlinarith [Finset.expect_nonneg (fun u (_ : u ∈ Finset.univ) ↦ finite_probability_nonneg (E u))]

/--
---
conclusion: Lax323828.CenteredProjection.from_constraints_complete
---
-/
theorem from_constraints_complete {V D A : Type}
    (C : ProjectionGames.System V D A) (h : C.Satisfiable) : (fromConstraints C).Complete :=
  Lax323828.ProjectionGames.completeness C h

/--
---
conclusion: Lax323828.CenteredProjection.from_constraints_sound
---
-/
theorem from_constraints_sound {V D A : Type} [Fintype V] [Nonempty V]
    [Fintype D] [Nonempty D] [Nonempty A]
    (C : ProjectionGames.System V D A) (γ : ℝ) (h : C.Sound γ) :
    (fromConstraints C).Sound (1 - γ / 2) := by
  intro P Q
  have hp := Lax323828.ProjectionGames.soundness C γ h (fun w ↦ some (P w)) (fun v ↦ some (Q v))
  apply le_trans (Lax323828.FiniteProbability.monotone _ _ ?_) hp
  intro z hz
  exact ⟨P (C.question z.1 z.2), Q z.1, rfl, rfl, hz⟩

def constraintQuestionEquiv {V D A : Type} (C : ProjectionGames.System V D A) :
    (V × (D × Bool)) ≃ ((V × D) × Bool) where
  toFun z := (C.question z.1 z.2, z.2.2)
  invFun z := if z.2 then ((C.reverse z.1).1, ((C.reverse z.1).2, true))
    else (z.1.1, (z.1.2, false))
  left_inv := by rintro ⟨v, d, b⟩; cases b <;> simp [ProjectionGames.System.question]
  right_inv := by rintro ⟨z, b⟩; cases b <;> simp [ProjectionGames.System.question]

/--
---
conclusion: Lax323828.CenteredProjection.from_constraints_uniform
---
-/
theorem from_constraints_uniform {V D A : Type} [Fintype V] [Fintype D]
    (C : ProjectionGames.System V D A) : (fromConstraints C).Uniform := by
  intro f
  change (𝔼 v, 𝔼 ω, f (C.question v ω)) = _
  rw [← Finset.expect_product', Finset.univ_product_univ]
  rw [Fintype.expect_equiv (constraintQuestionEquiv C)
    (fun z ↦ f (C.question z.1 z.2)) (fun z ↦ f z.1) (fun _ ↦ rfl)]
  rw [← Finset.univ_product_univ, Finset.expect_product]
  simp only [Fintype.expect_const]

theorem exists_tuple_length (r : ℝ) (hr : 0 < r) :
    ∃ t : ℕ, 0 < t ∧ 1 / (t : ℝ) ≤ r ^ 2 := by
  obtain ⟨t, ht⟩ := exists_nat_gt (1 / r ^ 2)
  have ht0 : (0 : ℝ) < t := lt_trans (by positivity) ht
  refine ⟨t, by exact_mod_cast ht0, ?_⟩
  apply (div_le_iff₀ ht0).mpr
  have h := (div_lt_iff₀ (sq_pos_of_pos hr)).mp ht
  linarith

theorem exists_square_parameter (X : Type) [Fintype X] [Nonempty X]
    (η : ℝ) (hη : 0 < η) :
    ∃ t : ℕ, 0 < t ∧ ∃ r : ℝ, 0 ≤ r ∧ 1 / (t : ℝ) ≤ r ^ 2 ∧
      (Fintype.card X : ℝ) * (4 * r) = η := by
  have hx : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  let r := η / (4 * (Fintype.card X : ℝ))
  have hr : 0 < r := div_pos hη (by positivity)
  obtain ⟨t, ht, htr⟩ := exists_tuple_length r hr
  refine ⟨t, ht, r, hr.le, htr, ?_⟩
  dsimp [r]
  field_simp

end CenteredProjection
end Lax323828Proofs
