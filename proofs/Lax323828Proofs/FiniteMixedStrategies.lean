import Lax323828.FortifiedSquaring
import Lax323828Proofs.FiniteProbability
import Mathlib.Data.Fintype.Pi

namespace Lax323828Proofs

open Lax323828 Lax323828.FiniteProbability Lax323828.FortifiedSquaring
open scoped BigOperators

theorem strategy_weight_sum {W A : Type} [Fintype W] [DecidableEq W] [Fintype A]
    (p : W → A → ℝ) (hp : ∀ w, ∑ a, p w a = 1) :
    (∑ P : W → A, ∏ w, p w (P w)) = 1 := by
  classical
  rw [← Fintype.prod_sum]
  simp [hp]

theorem strategy_weight_evaluation {W A : Type} [Fintype W] [DecidableEq W] [Fintype A]
    (p : W → A → ℝ) (hp : ∀ w, ∑ a, p w a = 1) (w : W) (f : A → ℝ) :
    (∑ P : W → A, (∏ v, p v (P v)) * f (P w)) = ∑ a, p w a * f a := by
  classical
  have he (P : W → A) : (∏ v, p v (P v)) * f (P w) =
      ∏ v, p v (P v) * (if v = w then f (P v) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [he]
  rw [← Fintype.prod_sum (fun v a ↦ p v a * (if v = w then f a else 1))]
  have ht (v : W) : (∑ a, p v a * (if v = w then f a else 1)) =
      if v = w then (∑ a, p w a * f a) else 1 := by
    by_cases h : v = w
    · subst v; simp
    · simp [h, hp]
  simp_rw [ht]
  simp

theorem finite_mixed_strategy_bound {Z W A B : Type}
    [Fintype Z] [Fintype W] [DecidableEq W] [Fintype A]
    (G : Game Z W A B) (s : ℝ) (h : G.Sound s)
    (p q : W → A → ℝ) (hp : ∀ w a, 0 ≤ p w a) (hq : ∀ w a, 0 ≤ q w a)
    (hp1 : ∀ w, ∑ a, p w a = 1) (hq1 : ∀ w, ∑ a, q w a = 1) :
    letI := Classical.propDecidable
    (𝔼 z, ∑ a, ∑ b, p (G.left z) a * q (G.right z) b *
      (if G.Test z a b then (1 : ℝ) else 0)) ≤ s := by
  classical
  let wp := fun P : W → A ↦ ∏ w, p w (P w)
  let wq := fun Q : W → A ↦ ∏ w, q w (Q w)
  have hwp : ∀ P, 0 ≤ wp P := fun P ↦ Finset.prod_nonneg fun w _ ↦ hp w (P w)
  have hwq : ∀ Q, 0 ≤ wq Q := fun Q ↦ Finset.prod_nonneg fun w _ ↦ hq w (Q w)
  have hsp : ∑ P, wp P = 1 := strategy_weight_sum p hp1
  have hsq : ∑ Q, wq Q = 1 := strategy_weight_sum q hq1
  have he (z : Z) :
      (∑ a, ∑ b, p (G.left z) a * q (G.right z) b * (if G.Test z a b then (1 : ℝ) else 0)) =
        ∑ P : W → A, ∑ Q : W → A,
          wp P * wq Q * (if G.Wins P Q z then (1 : ℝ) else 0) := by
    symm
    calc
      _ = ∑ P : W → A, wp P * ∑ b, q (G.right z) b *
          (if G.Test z (P (G.left z)) b then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro P _
        simp_rw [mul_assoc, ← Finset.mul_sum]
        congr 1
        convert strategy_weight_evaluation q hq1 (G.right z)
          (fun b ↦ if G.Test z (P (G.left z)) b then (1 : ℝ) else 0)
          using 1
        apply Finset.sum_congr rfl
        intro Q _
        congr 1
      _ = ∑ a, p (G.left z) a * ∑ b, q (G.right z) b *
          (if G.Test z a b then (1 : ℝ) else 0) := by
        simpa only [wp] using strategy_weight_evaluation p hp1 (G.left z)
          (fun a ↦ ∑ b, q (G.right z) b * (if G.Test z a b then (1 : ℝ) else 0))
      _ = _ := by simp only [Finset.mul_sum, mul_assoc]
  simp_rw [he, Finset.expect_sum_comm, ← Finset.mul_expect]
  calc
    _ ≤ ∑ P : W → A, ∑ Q : W → A, wp P * wq Q * s := by
      apply Finset.sum_le_sum
      intro P _
      apply Finset.sum_le_sum
      intro Q _
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hwp P) (hwq Q))
      have hh := h P Q
      rw [finite_probability_indicator] at hh
      exact hh
    _ = s := by
      simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [hsq, one_mul, hsp, one_mul]

end Lax323828Proofs

namespace Lax323828Proofs

open scoped BigOperators

noncomputable def normalizeAnswers {A : Type} [Fintype A] [Nonempty A]
    (p : A → ℝ) (a : A) : ℝ := by
  classical
  exact if (∑ b, p b) = 0 then
    (if a = Classical.arbitrary A then 1 else 0) else p a / (∑ b, p b)

theorem normalize_answers_nonneg {A : Type} [Fintype A] [Nonempty A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (a : A) : 0 ≤ normalizeAnswers p a := by
  classical
  unfold normalizeAnswers
  split_ifs
  · norm_num
  · norm_num
  · exact div_nonneg (hp a) (Finset.sum_nonneg fun b _ ↦ hp b)

theorem normalize_answers_sum {A : Type} [Fintype A] [Nonempty A]
    (p : A → ℝ) : (∑ a, normalizeAnswers p a) = 1 := by
  classical
  by_cases h : (∑ b, p b) = 0
  · simp [normalizeAnswers, h]
  · simp only [normalizeAnswers, h, if_false, ← Finset.sum_div]
    exact div_self h

theorem normalize_answers_mass {A : Type} [Fintype A] [Nonempty A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (a : A) :
    p a = (∑ b, p b) * normalizeAnswers p a := by
  classical
  by_cases h : (∑ b, p b) = 0
  · have hl : p a ≤ ∑ b, p b := Finset.single_le_sum (fun b _ ↦ hp b) (Finset.mem_univ a)
    rw [h, zero_mul]
    linarith [hp a]
  · simp only [normalizeAnswers, h, if_false]
    field_simp

end Lax323828Proofs

namespace Lax323828Proofs

open scoped BigOperators

theorem product_density_distance (a b u v : ℝ)
    (_ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ 1) (_hv : 0 ≤ v ∧ v ≤ 1) :
    |a * b - u * v| ≤ |a - u| + |b - v| := by
  have he : a * b - u * v = (a - u) * b + u * (b - v) := by ring
  rw [he]
  calc
    _ ≤ |(a - u) * b| + |u * (b - v)| := abs_add_le _ _
    _ = |a - u| * b + u * |b - v| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hb.1, abs_of_nonneg hu.1]
    _ ≤ |a - u| * 1 + 1 * |b - v| := add_le_add
      (mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hu.2 (abs_nonneg _))
    _ = _ := by ring

theorem bounded_score_perturbation {Z : Type} [Fintype Z] [Nonempty Z]
    (d X : Z → ℝ) (c s e : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hX : ∀ z, 0 ≤ X z ∧ X z ≤ 1) (hscore : (𝔼 z, X z) ≤ s)
    (hd : (𝔼 z, |d z - c|) ≤ e) :
    (𝔼 z, d z * X z) ≤ s * (𝔼 z, d z) + (s + 1) * e := by
  have hpt (z : Z) : d z * X z ≤ c * X z + |d z - c| := by
    have h₁ : (d z - c) * X z ≤ |d z - c| * X z :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (hX z).1
    have h₂ : |d z - c| * X z ≤ |d z - c| * 1 :=
      mul_le_mul_of_nonneg_left (hX z).2 (abs_nonneg _)
    nlinarith
  have hwin : (𝔼 z, d z * X z) ≤ c * s + e := by
    calc
      _ ≤ 𝔼 z, (c * X z + |d z - c|) := Finset.expect_le_expect fun z _ ↦ hpt z
      _ = c * (𝔼 z, X z) + (𝔼 z, |d z - c|) := by
        rw [Finset.expect_add_distrib, ← Finset.mul_expect]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hscore hc) hd
  have hmass : c ≤ (𝔼 z, d z) + e := by
    calc
      c = 𝔼 _z : Z, c := (Fintype.expect_const _).symm
      _ ≤ 𝔼 z, (d z + |d z - c|) := Finset.expect_le_expect fun z _ ↦ by
        have h := neg_le_abs (d z - c)
        linarith
      _ = (𝔼 z, d z) + (𝔼 z, |d z - c|) := Finset.expect_add_distrib _ _ _
      _ ≤ _ := add_le_add le_rfl hd
  have hh := mul_le_mul_of_nonneg_left hmass hs
  nlinarith

theorem rectangle_density_bound {Z W : Type} [Fintype Z] [Nonempty Z]
    [Fintype W] (left right : Z → W)
    (hl : ∀ f : W → ℝ, (𝔼 z, f (left z)) = (𝔼 w, f w))
    (hr : ∀ f : W → ℝ, (𝔼 z, f (right z)) = (𝔼 w, f w))
    (a b : W → ℝ) (u v s : ℝ)
    (ha : ∀ w, 0 ≤ a w ∧ a w ≤ 1) (hb : ∀ w, 0 ≤ b w ∧ b w ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) (hs : 0 ≤ s)
    (X : Z → ℝ) (hX : ∀ z, 0 ≤ X z ∧ X z ≤ 1) (hscore : (𝔼 z, X z) ≤ s) :
    (𝔼 z, a (left z) * b (right z) * X z) ≤
      s * (𝔼 z, a (left z) * b (right z)) +
        (s + 1) * ((𝔼 w, |a w - u|) + (𝔼 w, |b w - v|)) := by
  apply bounded_score_perturbation _ X (u * v) s _ (mul_nonneg hu.1 hv.1) hs hX hscore
  calc
    _ ≤ 𝔼 z, (|a (left z) - u| + |b (right z) - v|) :=
      Finset.expect_le_expect fun z _ ↦ product_density_distance _ _ _ _ (ha _) (hb _) hu hv
    _ = _ := by
      rw [Finset.expect_add_distrib, hl (fun w ↦ |a w - u|), hr (fun w ↦ |b w - v|)]

end Lax323828Proofs
/- Checked together with FiniteMixedStrategies, AnswerNormalization,
   and DensityPerturbation by the draft assembly script. -/

namespace Lax323828Proofs

open Lax323828 Lax323828.FiniteProbability Lax323828.FortifiedSquaring
open scoped BigOperators

theorem subdensity_soundness {Z W A B : Type}
    [Fintype Z] [Nonempty Z] [Fintype W] [DecidableEq W]
    [Fintype A] [Nonempty A]
    (G : Game Z W A B)
    (hl : ∀ f : W → ℝ, (𝔼 z, f (G.left z)) = (𝔼 w, f w))
    (hr : ∀ f : W → ℝ, (𝔼 z, f (G.right z)) = (𝔼 w, f w))
    (s : ℝ) (hs : 0 ≤ s) (hG : G.Sound s)
    (p q : W → A → ℝ) (hp : ∀ w a, 0 ≤ p w a) (hq : ∀ w a, 0 ≤ q w a)
    (hp1 : ∀ w, ∑ a, p w a ≤ 1) (hq1 : ∀ w, ∑ a, q w a ≤ 1)
    (u v : ℝ) (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) :
    letI := Classical.propDecidable
    (𝔼 z, ∑ a, ∑ b, p (G.left z) a * q (G.right z) b *
      (if G.Test z a b then (1 : ℝ) else 0)) ≤
      s * (𝔼 z, (∑ a, p (G.left z) a) * (∑ b, q (G.right z) b)) +
      (s + 1) * ((𝔼 w, |(∑ a, p w a) - u|) + (𝔼 w, |(∑ b, q w b) - v|)) := by
  classical
  let np := fun w ↦ normalizeAnswers (p w)
  let nq := fun w ↦ normalizeAnswers (q w)
  let score := fun z ↦ ∑ a, ∑ b, np (G.left z) a * nq (G.right z) b *
    (if G.Test z a b then (1 : ℝ) else 0)
  have hnp : ∀ w a, 0 ≤ np w a := fun w a ↦ normalize_answers_nonneg _ (hp w) a
  have hnq : ∀ w a, 0 ≤ nq w a := fun w a ↦ normalize_answers_nonneg _ (hq w) a
  have hnp1 : ∀ w, ∑ a, np w a = 1 := fun w ↦ normalize_answers_sum (p w)
  have hnq1 : ∀ w, ∑ a, nq w a = 1 := fun w ↦ normalize_answers_sum (q w)
  have hscore (z : Z) : 0 ≤ score z ∧ score z ≤ 1 := by
    constructor
    · exact Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun b _ ↦
        mul_nonneg (mul_nonneg (hnp _ _) (hnq _ _)) (by split_ifs <;> norm_num)
    · calc
        _ ≤ ∑ a, ∑ b, np (G.left z) a * nq (G.right z) b * 1 := by
          apply Finset.sum_le_sum
          intro a _
          apply Finset.sum_le_sum
          intro b _
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hnp _ _) (hnq _ _))
          split_ifs <;> norm_num
        _ = 1 := by simp only [mul_one, ← Finset.mul_sum, hnq1, hnp1]
  have hval : (𝔼 z, score z) ≤ s :=
    finite_mixed_strategy_bound G s hG np nq hnp hnq hnp1 hnq1
  have he (z : Z) :
      (∑ a, ∑ b, p (G.left z) a * q (G.right z) b *
        (if G.Test z a b then (1 : ℝ) else 0)) =
      (∑ a, p (G.left z) a) * (∑ b, q (G.right z) b) * score z := by
    unfold score
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    conv_lhs => rw [normalize_answers_mass (p (G.left z)) (hp _) a,
      normalize_answers_mass (q (G.right z)) (hq _) b]
    change _ = _ * _ * (np (G.left z) a * nq (G.right z) b * _)
    ring
  simp_rw [he]
  apply rectangle_density_bound G.left G.right hl hr _ _ u v s
    (fun w ↦ ⟨Finset.sum_nonneg (fun a _ ↦ hp w a), hp1 w⟩)
    (fun w ↦ ⟨Finset.sum_nonneg (fun b _ ↦ hq w b), hq1 w⟩) hu hv hs score hscore hval

end Lax323828Proofs
