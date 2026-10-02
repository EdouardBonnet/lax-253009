import Lax323828.Amplification
import Lax323828Proofs.CenteredProjection
import Mathlib.Data.PNat.Basic

namespace Lax323828Proofs

open Lax323828 Lax323828.FiniteProbability Lax323828.FortifiedSquaring
open Lax323828.TupleFortification Lax323828.CenteredProjection
open Lax323828Proofs.CenteredProjection
open scoped BigOperators

namespace Amplification

open Lax323828.Amplification
open Lax323828.Amplification.Scheme
  (centers questions extensions centerPower questionPower extensionCoefficient extensionPower)

namespace Scheme

/--
---
conclusion: Lax323828.Amplification.Scheme.transform_complete
---
-/
theorem transform_complete {U Ω W X Y : Type} (S : Scheme) (G : System U Ω W X Y)
    (h : G.Complete) : (S.transform G).Complete := by
  induction S with
  | base => exact h
  | step t S ih => exact Lax323828.CenteredProjection.tensor_complete _ (Lax323828.CenteredProjection.fortify_complete _ ih t)

/--
---
conclusion: Lax323828.Amplification.Scheme.transform_uniform
---
-/
theorem transform_uniform {U Ω W X Y : Type}
    [Fintype U] [Fintype Ω] [Fintype W] [Nonempty W]
    (S : Scheme) (G : System U Ω W X Y) (h : G.Uniform) : (S.transform G).Uniform := by
  induction S with
  | base => exact h
  | step t S ih => exact Lax323828.CenteredProjection.tensor_uniform _ (Lax323828.CenteredProjection.fortify_uniform _ ih t t.pos)

/--
---
conclusion: Lax323828.Amplification.Scheme.card_centers
---
-/
theorem card_centers {U : Type} [Fintype U] (S : Scheme) :
    Fintype.card (S.centers U) = Fintype.card U ^ S.centerPower := by
  induction S with
  | base =>
    simp only [centers, centerPower, pow_one]
    exact congrArg (@Fintype.card U) (Subsingleton.elim _ _)
  | step t S ih =>
    change Fintype.card (S.centers U × S.centers U) = _
    rw [Fintype.card_prod, ih]
    simp only [centerPower, pow_mul, pow_two]

/--
---
conclusion: Lax323828.Amplification.Scheme.card_questions
---
-/
theorem card_questions {W : Type} [Fintype W] (S : Scheme) :
    Fintype.card (S.questions W) = Fintype.card W ^ S.questionPower := by
  induction S with
  | base =>
    simp only [questions, questionPower, pow_one]
    exact congrArg (@Fintype.card W) (Subsingleton.elim _ _)
  | step t S ih =>
    change Fintype.card ((Fin t → S.questions W) × (Fin t → S.questions W)) = _
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ih,
      questionPower, pow_mul, pow_two]

/--
---
conclusion: Lax323828.Amplification.Scheme.card_extensions
---
-/
theorem card_extensions {Ω W : Type} [Fintype Ω] [Fintype W] (S : Scheme) :
    Fintype.card (S.extensions Ω W) =
      S.extensionCoefficient * Fintype.card Ω ^ S.centerPower * Fintype.card W ^ S.extensionPower := by
  induction S with
  | base =>
    simp only [extensions, extensionCoefficient, centerPower, extensionPower, pow_one, pow_zero, one_mul, mul_one]
    exact congrArg (@Fintype.card Ω) (Subsingleton.elim _ _)
  | step t S ih =>
    change Fintype.card ((S.extensions Ω W × History t (S.questions W)) ×
      (S.extensions Ω W × History t (S.questions W))) = _
    simp only [Fintype.card_prod, History, Fintype.card_fun, Fintype.card_fin, ih, Lax323828.Amplification.Scheme.card_questions,
      extensionCoefficient, centerPower, extensionPower, pow_mul, pow_add, pow_two]
    ring

/--
---
conclusion: Lax323828.Amplification.Scheme.size_polynomial
---
-/
theorem size_polynomial {U Ω W : Type} [Fintype U] [Fintype Ω] [Fintype W] (S : Scheme) :
    Fintype.card (S.centers U) + Fintype.card (S.extensions Ω W) + Fintype.card (S.questions W) ≤
      (S.extensionCoefficient + 2) * (Fintype.card U + Fintype.card Ω + Fintype.card W + 1) ^
        (S.centerPower + S.questionPower + S.extensionPower) := by
  rw [Lax323828.Amplification.Scheme.card_centers, Lax323828.Amplification.Scheme.card_questions, Lax323828.Amplification.Scheme.card_extensions]
  let N := Fintype.card U + Fintype.card Ω + Fintype.card W + 1
  let e := S.centerPower + S.questionPower + S.extensionPower
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hu : Fintype.card U ^ S.centerPower ≤ N ^ e := by
    apply (pow_le_pow_left' (show Fintype.card U ≤ N by dsimp [N]; omega) _).trans
    exact pow_le_pow_right' hN (by dsimp [e]; omega)
  have hw : Fintype.card W ^ S.questionPower ≤ N ^ e := by
    apply (pow_le_pow_left' (show Fintype.card W ≤ N by dsimp [N]; omega) _).trans
    exact pow_le_pow_right' hN (by dsimp [e]; omega)
  have he : S.extensionCoefficient * Fintype.card Ω ^ S.centerPower *
      Fintype.card W ^ S.extensionPower ≤ S.extensionCoefficient * N ^ e := by
    rw [mul_assoc]
    apply Nat.mul_le_mul_left
    calc
      _ ≤ N ^ S.centerPower * N ^ S.extensionPower := mul_le_mul'
        (pow_le_pow_left' (show Fintype.card Ω ≤ N by dsimp [N]; omega) _)
        (pow_le_pow_left' (show Fintype.card W ≤ N by dsimp [N]; omega) _)
      _ ≤ _ := by
        rw [← pow_add]
        exact pow_le_pow_right' hN (by dsimp [e]; omega)
  change _ ≤ (S.extensionCoefficient + 2) * N ^ e
  nlinarith

end Scheme

theorem exists_geometric_scheme (X Y : Type) [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (s q : ℝ) (hs : 0 < s) (hsq : s < q) (hq : q < 1)
    (n : ℕ) : ∃ S : Scheme, SoundReduction S X Y s (s * q ^ n) := by
  classical
  have hq0 : 0 < q := hs.trans hsq
  induction n with
  | zero =>
    refine ⟨.base, ?_⟩
    intro U Ω W _ _ _ _ _ _ G _ hG
    simpa only [pow_zero, mul_one] using (show (Scheme.base.transform G).symmetrize.Sound s from by
      convert hG using 1 <;> rfl)
  | succ n ih =>
    obtain ⟨S, hS⟩ := ih
    let v := s * q ^ n
    let η := v * (q - s)
    have hv : 0 < v := mul_pos hs (pow_pos hq0 _)
    have hη : 0 < η := mul_pos hv (sub_pos.mpr hsq)
    have hvs : v ≤ s := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (pow_le_one₀ hq0.le hq.le) hs.le
    obtain ⟨t, ht, r, hr, htr, he⟩ := exists_square_parameter (S.centers X) η hη
    refine ⟨.step ⟨t, ht⟩ S, ?_⟩
    intro U Ω W _ _ _ _ _ _ G hu hG
    have hh := Lax323828.CenteredProjection.fortify_square_sound (S.transform G) (Lax323828.Amplification.Scheme.transform_uniform S G hu)
      t ht v hv.le (hvs.trans (hsq.trans hq).le) (hS U Ω W G hu hG) r hr htr
    rw [he] at hh
    have hvnext : v ^ 2 + η ≤ s * q ^ (n + 1) := by
      have h := mul_le_mul_of_nonneg_left hvs hv.le
      dsimp [η]
      dsimp [v] at *
      rw [pow_succ q n]
      nlinarith
    intro P Q
    exact (hh P Q).trans hvnext

/--
---
conclusion: Lax323828.Amplification.exists_small_value_scheme
---
-/
theorem exists_small_value_scheme (X Y : Type) [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (s δ : ℝ) (hs : 0 < s) (hs1 : s < 1) (hδ : 0 < δ) :
    ∃ S : Scheme, SoundReduction S X Y s δ := by
  let q := (1 + s) / 2
  have hsq : s < q := by dsimp [q]; linarith
  have hq : q < 1 := by dsimp [q]; linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hδ hs) hq
  obtain ⟨S, hS⟩ := exists_geometric_scheme X Y s q hs hsq hq n
  refine ⟨S, ?_⟩
  intro U Ω W _ _ _ _ _ _ G hu hG P Q
  apply (hS U Ω W G hu hG P Q).trans
  have h := (lt_div_iff₀ hs).mp hn
  nlinarith

end Amplification
end Lax323828Proofs
