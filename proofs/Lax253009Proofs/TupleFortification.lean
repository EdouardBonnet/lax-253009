import Lax253009.TupleFortification
import Lax253009Proofs.FiniteMixedStrategies
import Lax253009Proofs.TupleSampler

namespace Lax253009Proofs

open Lax253009 Lax253009.FiniteProbability Lax253009.FortifiedSquaring
open Lax253009.TupleSampler
open scoped BigOperators

namespace TupleLift

open Lax253009.TupleFortification

theorem probability_indicator {H : Type} [Fintype H] (E : H → Prop) :
    probability E = 𝔼 h, indicator E h := by
  classical
  rw [finite_probability_indicator]
  apply Finset.expect_congr rfl
  intro h _
  by_cases he : E h <;> simp [indicator, he]

theorem indicator_congr {H K : Type} {E : H → Prop} {F : K → Prop}
    {h : H} {k : K} (he : E h ↔ F k) : indicator E h = indicator F k := by
  classical
  by_cases hE : E h
  · simp [indicator, hE, he.mp hE]
  · simp [indicator, hE, mt he.mpr hE]

noncomputable def density {W A : Type} [Fintype W] (t : ℕ)
    (P : (Fin t → W) → (Fin t → A)) (S : (Fin t → W) → Prop)
    (w : W) (a : A) : ℝ :=
  𝔼 h : History t W, indicator (fun h ↦ S (plant w h) ∧ P (plant w h) h.1 = a) h

theorem density_pushforward {H A : Type} [Fintype H] [Fintype A]
    (E : H → Prop) (a : H → A) (f : A → ℝ) :
    (∑ b, (𝔼 h, indicator (fun h ↦ E h ∧ a h = b) h) * f b) =
      𝔼 h, indicator E h * f (a h) := by
  classical
  simp only [Finset.expect_mul, ← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro h _
  by_cases he : E h
  · simp [indicator, he]
  · simp [indicator, he]

theorem density_nonneg {W A : Type} [Fintype W] (t : ℕ)
    (P : (Fin t → W) → (Fin t → A)) (S : (Fin t → W) → Prop)
    (w : W) (a : A) : 0 ≤ density t P S w a := by
  unfold density indicator
  exact Finset.expect_nonneg fun _ _ ↦ by split_ifs <;> norm_num

theorem density_mass {W A : Type} [Fintype W] [Fintype A] (t : ℕ)
    (P : (Fin t → W) → (Fin t → A)) (S : (Fin t → W) → Prop) (w : W) :
    (∑ a, density t P S w a) = mass t S w := by
  have h := density_pushforward (fun h : History t W ↦ S (plant w h))
    (fun h ↦ P (plant w h) h.1) (fun _ ↦ (1 : ℝ))
  calc
    _ = 𝔼 h : History t W, indicator (fun h ↦ S (plant w h)) h := by
      simpa only [mul_one, density] using h
    _ = _ := by
      unfold mass
      rw [← Finset.expect_product', Finset.univ_product_univ]
      apply Finset.expect_congr rfl
      intro h _
      exact indicator_congr Iff.rfl

theorem independent_density {H K A : Type} [Fintype H] [Fintype K] [Fintype A]
    (E : H → Prop) (F : K → Prop) (a : H → A) (b : K → A) (R : A → A → Prop) :
    (𝔼 h, 𝔼 k, indicator (fun p : H × K ↦ R (a p.1) (b p.2) ∧ E p.1 ∧ F p.2) (h, k)) =
      ∑ x, ∑ y, (𝔼 h, indicator (fun h ↦ E h ∧ a h = x) h) *
        (𝔼 k, indicator (fun k ↦ F k ∧ b k = y) k) * indicator (fun y ↦ R x y) y := by
  classical
  symm
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp_rw [density_pushforward]
  simp_rw [Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro h _
  apply Finset.expect_congr rfl
  intro k _
  simp only [indicator]
  split_ifs <;> simp_all

theorem restricted_identity {Z W A B : Type} [Fintype Z] [Fintype W] [Fintype A]
    (G : Game Z W A B) (t : ℕ)
    (P Q : (Fin t → W) → (Fin t → A)) (S T : (Fin t → W) → Prop) :
    probability (fun z ↦ (lift G t).Wins P Q z ∧ S ((lift G t).left z) ∧
      T ((lift G t).right z)) =
      𝔼 z, ∑ a, ∑ b, density t P S (G.left z) a * density t Q T (G.right z) b *
        indicator (fun b ↦ G.Test z a b) b := by
  classical
  rw [probability_indicator]
  rw [← Finset.univ_product_univ, Finset.expect_product]
  apply Finset.expect_congr rfl
  intro z _
  rw [← Finset.univ_product_univ, Finset.expect_product]
  have h := independent_density (fun h ↦ S (plant (G.left z) h))
    (fun h ↦ T (plant (G.right z) h))
    (fun h ↦ P (plant (G.left z) h) h.1)
    (fun h ↦ Q (plant (G.right z) h) h.1) (G.Test z)
  unfold density
  rw [← h]
  apply Finset.expect_congr rfl
  intro j _
  apply Finset.expect_congr rfl
  intro k _
  exact indicator_congr Iff.rfl

theorem rectangle_identity {Z W A B : Type} [Fintype Z] [Fintype W]
    (G : Game Z W A B) (t : ℕ) (S T : (Fin t → W) → Prop) :
    probability (fun z ↦ S ((lift G t).left z) ∧ T ((lift G t).right z)) =
      𝔼 z, mass t S (G.left z) * mass t T (G.right z) := by
  classical
  rw [probability_indicator, ← Finset.univ_product_univ, Finset.expect_product]
  apply Finset.expect_congr rfl
  intro z _
  rw [← Finset.univ_product_univ, Finset.expect_product]
  calc
    _ = 𝔼 h : History t W, 𝔼 k : History t W,
        indicator S (plant (G.left z) h) * indicator T (plant (G.right z) k) := by
      apply Finset.expect_congr rfl
      intro h _
      apply Finset.expect_congr rfl
      intro k _
      by_cases hs : S (plant (G.left z) h) <;>
        by_cases ht : T (plant (G.right z) k) <;> simp [indicator, lift, hs, ht]
    _ = _ := by
      simp only [← Finset.mul_expect, ← Finset.expect_mul, mass, plant,
        ← Finset.expect_product', Finset.univ_product_univ]

theorem true_mass {W : Type} [Fintype W] [Nonempty W] (t : ℕ) (ht : 0 < t) (w : W) :
    mass t (fun _ : Fin t → W ↦ True) w = 1 := by
  have : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  simp [mass, indicator]

/--
---
conclusion: Lax253009.TupleFortification.soundness
---
-/
theorem lift_soundness {Z W A B : Type} [Fintype Z] [Fintype W] [DecidableEq W]
    [Nonempty W] [Fintype A] (G : Game Z W A B) (t : ℕ) (ht : 0 < t)
    (s : ℝ) (hG : G.Sound s) : (lift G t).Sound s := by
  classical
  intro P Q
  have he := restricted_identity G t P Q (fun _ ↦ True) (fun _ ↦ True)
  simp only [and_true] at he
  rw [he]
  have h := finite_mixed_strategy_bound G s hG
    (density t P (fun _ ↦ True)) (density t Q (fun _ ↦ True))
    (density_nonneg t P _) (density_nonneg t Q _)
    (fun w ↦ by rw [density_mass, true_mass t ht])
    (fun w ↦ by rw [density_mass, true_mass t ht])
  simpa only [indicator] using h

/--
---
conclusion: Lax253009.TupleFortification.fortification
---
-/
theorem lift_fortified {Z W A B : Type}
    [Fintype Z] [Nonempty Z] [Fintype W] [DecidableEq W] [Nonempty W]
    [Fintype A] [Nonempty A]
    (G : Game Z W A B)
    (hl : ∀ f : W → ℝ, (𝔼 z, f (G.left z)) = (𝔼 w, f w))
    (hr : ∀ f : W → ℝ, (𝔼 z, f (G.right z)) = (𝔼 w, f w))
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hG : G.Sound s)
    (t : ℕ) (ht : 0 < t) (r : ℝ) (hr0 : 0 ≤ r) (htr : 1 / (t : ℝ) ≤ r ^ 2) :
    (lift G t).Fortified s (4 * r) := by
  classical
  intro P Q S T
  rw [restricted_identity, rectangle_identity]
  have h := subdensity_soundness G hl hr s hs hG (density t P S) (density t Q T)
    (density_nonneg t P S) (density_nonneg t Q T)
    (fun w ↦ by rw [density_mass]; exact (Lax253009.TupleSampler.bounds t ht S w).2)
    (fun w ↦ by rw [density_mass]; exact (Lax253009.TupleSampler.bounds t ht T w).2)
    (probability S) (probability T)
    ⟨finite_probability_nonneg S, finite_probability_le_one S⟩
    ⟨finite_probability_nonneg T, finite_probability_le_one T⟩
  simp_rw [density_mass] at h
  have hS : (𝔼 w, |mass t S w - probability S|) ≤ r := by
    have hb := (Lax253009.TupleSampler.mixing t ht S).trans htr
    nlinarith [Finset.expect_nonneg (fun w (_ : w ∈ Finset.univ) ↦
      abs_nonneg (mass t S w - probability S))]
  have hT : (𝔼 w, |mass t T w - probability T|) ≤ r := by
    have hb := (Lax253009.TupleSampler.mixing t ht T).trans htr
    nlinarith [Finset.expect_nonneg (fun w (_ : w ∈ Finset.univ) ↦
      abs_nonneg (mass t T w - probability T))]
  have he : (s + 1) * ((𝔼 w, |mass t S w - probability S|) +
      (𝔼 w, |mass t T w - probability T|)) ≤ 4 * r := by
    calc
      _ ≤ (s + 1) * (r + r) := mul_le_mul_of_nonneg_left (add_le_add hS hT) (by linarith)
      _ ≤ 2 * (r + r) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  simpa only [indicator] using h.trans (add_le_add le_rfl he)

theorem plant_uniform {W : Type} [Fintype W] [Nonempty W]
    (t : ℕ) (ht : 0 < t) (f : (Fin t → W) → ℝ) :
    (𝔼 w, 𝔼 h : History t W, f (plant w h)) = 𝔼 z, f z := by
  have : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  calc
    _ = 𝔼 w, 𝔼 i : Fin t, 𝔼 z : Fin t → W, f (Function.update z i w) := by
      simp only [plant, ← Finset.univ_product_univ, Finset.expect_product]
    _ = 𝔼 i : Fin t, 𝔼 w, 𝔼 z : Fin t → W, f (Function.update z i w) :=
      Finset.expect_comm _ _ _
    _ = 𝔼 i : Fin t, 𝔼 z, f z := by
      apply Finset.expect_congr rfl
      intro i _
      simpa only [mul_one] using coordinate_resampling_adjoint i f (fun _ ↦ 1)
    _ = _ := Fintype.expect_const _

/--
---
conclusion: Lax253009.TupleFortification.left_uniform
---
-/
theorem lift_uniform_left {Z W A B : Type} [Fintype Z] [Fintype W] [Nonempty W]
    (G : Game Z W A B)
    (hl : ∀ f : W → ℝ, (𝔼 z, f (G.left z)) = (𝔼 w, f w))
    (t : ℕ) (ht : 0 < t) (f : (Fin t → W) → ℝ) :
    (𝔼 z, f ((lift G t).left z)) = 𝔼 w, f w := by
  have : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  change (𝔼 z : Z × (History t W × History t W), f (plant (G.left z.1) z.2.1)) = _
  rw [← Finset.univ_product_univ, Finset.expect_product]
  have he (z : Z) :
      (𝔼 h : History t W × History t W, f (plant (G.left z) h.1)) =
        𝔼 h : History t W, f (plant (G.left z) h) := by
    rw [← Finset.univ_product_univ, Finset.expect_product]
    simp only [Fintype.expect_const]
  simp_rw [he]
  rw [hl (fun w ↦ 𝔼 h : History t W, f (plant w h))]
  exact plant_uniform t ht f

/--
---
conclusion: Lax253009.TupleFortification.right_uniform
---
-/
theorem lift_uniform_right {Z W A B : Type} [Fintype Z] [Fintype W] [Nonempty W]
    (G : Game Z W A B)
    (hr : ∀ f : W → ℝ, (𝔼 z, f (G.right z)) = (𝔼 w, f w))
    (t : ℕ) (ht : 0 < t) (f : (Fin t → W) → ℝ) :
    (𝔼 z, f ((lift G t).right z)) = 𝔼 w, f w := by
  have : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  change (𝔼 z : Z × (History t W × History t W), f (plant (G.right z.1) z.2.2)) = _
  rw [← Finset.univ_product_univ, Finset.expect_product]
  have he (z : Z) :
      (𝔼 h : History t W × History t W, f (plant (G.right z) h.2)) =
        𝔼 h : History t W, f (plant (G.right z) h) := by
    rw [← Finset.univ_product_univ, Finset.expect_product]
    exact Fintype.expect_const (ι := History t W)
      (𝔼 h : History t W, f (plant (G.right z) h))
  simp_rw [he]
  rw [hr (fun w ↦ 𝔼 h : History t W, f (plant w h))]
  exact plant_uniform t ht f

/--
---
conclusion: Lax253009.TupleFortification.completeness
---
-/
theorem lift_complete {Z W A B : Type} (G : Game Z W A B)
    (P Q : W → A) (h : ∀ z, G.Wins P Q z) (t : ℕ) :
    ∀ z, (lift G t).Wins (fun w i ↦ P (w i)) (fun w i ↦ Q (w i)) z := by
  intro z
  simpa [Game.Wins, Game.Test, lift, plant] using h z.1

end TupleLift
end Lax253009Proofs
