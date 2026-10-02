import Lax323828.SmallValueSatisfiability
import Lax323828Proofs.ProjectionRelabel
import Lax323828Proofs.Amplification
import Lax323828Proofs.GapSatisfiability

namespace Lax323828Proofs

open Lax323828 Lax323828.FiniteProbability Lax323828.CenteredProjection
open Lax323828.Amplification Lax323828.GapSatisfiability
open scoped BigOperators

/--
---
conclusion: Lax323828.SmallValueSatisfiability.reduction
---
-/
theorem small_value_satisfiability (δ : ℝ) (hδ : 0 < δ) :
    ∃ x y K e : ℕ, 0 < x ∧ 0 < y ∧
      ∀ φ : Formula, Is3CNF φ →
        ∃ u o w : ℕ, 0 < u ∧ 0 < o ∧ 0 < w ∧ u + o + w ≤ K * (φ.length + 1) ^ e ∧
          ∃ G : System (Fin u) (Fin o) (Fin w) (Fin x) (Fin y),
            (Satisfiable φ → G.Complete) ∧ (¬ Satisfiable φ → G.Sound δ) := by
  classical
  obtain ⟨a, d, K, e, ha, hd, _, γ, hγ, hgap⟩ := Lax323828.GapSatisfiability.regular_gap
  have : Nonempty (Fin a) := Fin.pos_iff_nonempty.mp ha
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let s : ℝ := 1 - min γ 1 / 2
  have hs : 0 < s := by dsimp [s]; have := min_le_right γ (1 : ℝ); linarith
  have hs1 : s < 1 := by dsimp [s]; have := lt_min hγ (by norm_num : (0 : ℝ) < 1); linarith
  obtain ⟨S, hS⟩ := Lax323828.Amplification.exists_small_value_scheme
    (Fin a) (Fin a × Fin a) s (δ ^ 2) hs hs1 (sq_pos_of_pos hδ)
  let D := S.centerPower + S.questionPower + S.extensionPower
  let C := (S.extensionCoefficient + 2) * ((2 * d + 2) * (K + 1)) ^ D
  refine ⟨Fintype.card (S.centers (Fin a)), Fintype.card (S.questions (Fin a × Fin a)),
    C, e * D, Fintype.card_pos, Fintype.card_pos, ?_⟩
  intro φ hφ
  obtain ⟨n, hn, hnsize, R, hyes, hno⟩ := hgap φ hφ
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let H := S.transform (CenteredProjection.fromConstraints R)
  let u := Fintype.card (S.centers (Fin n))
  let o := Fintype.card (S.extensions (Fin d × Bool) (Fin n × Fin d))
  let w := Fintype.card (S.questions (Fin n × Fin d))
  have hsize : u + o + w ≤ C * (φ.length + 1) ^ (e * D) := by
    have hh := Lax323828.Amplification.Scheme.size_polynomial
      (U := Fin n) (Ω := Fin d × Bool) (W := Fin n × Fin d) S
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hh
    have hM : 1 ≤ (φ.length + 1) ^ e := Nat.one_le_pow _ _ (by omega)
    have hn1 : n + 1 ≤ (K + 1) * (φ.length + 1) ^ e := by nlinarith
    have hN : n + d * 2 + n * d + 1 ≤
        ((2 * d + 2) * (K + 1)) * (φ.length + 1) ^ e := by nlinarith
    apply hh.trans
    calc
      _ ≤ (S.extensionCoefficient + 2) *
          (((2 * d + 2) * (K + 1)) * (φ.length + 1) ^ e) ^ D :=
        Nat.mul_le_mul_left _ (pow_le_pow_left' hN D)
      _ = _ := by simp only [C, mul_pow, pow_mul, mul_assoc]
  refine ⟨u, o, w, Fintype.card_pos, Fintype.card_pos, Fintype.card_pos, hsize,
    ProjectionRelabel.relabel H (Fintype.equivFin _) (Fintype.equivFin _)
      (Fintype.equivFin _) (Fintype.equivFin _) (Fintype.equivFin _), ?_, ?_⟩
  · intro hsat
    apply ProjectionRelabel.complete
    exact Lax323828.Amplification.Scheme.transform_complete S _
      (Lax323828.CenteredProjection.from_constraints_complete R (hyes hsat))
  · intro hnsat
    apply ProjectionRelabel.sound H _ _ _ _ _ δ
    apply Lax323828.CenteredProjection.center_sound_of_sym H δ hδ.le
    apply hS (Fin n) (Fin d × Bool) (Fin n × Fin d)
      (CenteredProjection.fromConstraints R) (Lax323828.CenteredProjection.from_constraints_uniform R)
    apply Lax323828.CenteredProjection.symmetrize_sound
    intro P Q
    apply (Lax323828.CenteredProjection.from_constraints_sound R γ (hno hnsat) P Q).trans
    dsimp [s]
    have := min_le_left γ (1 : ℝ)
    linarith

end Lax323828Proofs
