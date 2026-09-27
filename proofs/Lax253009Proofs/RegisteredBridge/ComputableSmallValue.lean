import Lax253009Proofs.RegisteredBridge.AmplificationNumbering
import Lax253009Proofs.RegisteredBridge.RegularGameAlgorithms
import Lax253009Proofs.RegisteredBridge.RegisteredGap
import Lax253009Proofs.Amplification

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace Lax253009Proofs.RegisteredBridge

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding ComputableNumbering
open ComputableAmplification Lax253009.CenteredProjection Lax253009.Amplification

/-- The small-value game reduction with explicit polynomial-time numerical
queries. The scheme and its answer alphabets are fixed before the language. -/
theorem computable_small_value (F : FinBase) (hd : 1 < F.deg) (δ : ℝ) (hδ : 0 < δ) :
    ∃ S : Scheme, ∀ L ∈ Lax434930.NondeterministicPolynomialTime.NP,
      ∃ u o w : Word → ℕ, UnaryFn u ∧ UnaryFn o ∧ UnaryFn w ∧
        (∀ z, 0 < u z ∧ 0 < o z ∧ 0 < w z) ∧
        ∃ G : ∀ z, System (Fin (u z)) (Fin (o z)) (Fin (w z))
            (S.centers DinurAlpha) (S.questions (DinurAlpha × DinurAlpha)),
          ComputableAmplification.Algorithms (unary u) (unary o) (unary w)
            (centerCode S code) (questionCode S code) G ∧
          (∀ z, z ∈ L → (G z).Complete) ∧ (∀ z, z ∉ L → (G z).Sound δ) := by
  classical
  let E := F.toFamily hd
  let γ : ℝ := ConstraintGraph.preprocessConst E DinurAlpha * ((Dinur.amplifier E).gap : ℝ)
  have hγ : 0 < γ := mul_pos (Dinur.preprocessConst_pos E)
    (by exact_mod_cast (Dinur.amplifier E).gap_pos)
  let s : ℝ := 1 - min γ 1 / 2
  have hs : 0 < s := by
    dsimp only [s]
    have h := min_le_right γ (1 : ℝ)
    linarith
  have hs1 : s < 1 := by
    dsimp only [s]
    have h := lt_min hγ (by norm_num : (0 : ℝ) < 1)
    linarith
  obtain ⟨S, hS⟩ := Lax253009Proofs.Amplification.exists_small_value_scheme DinurAlpha (DinurAlpha × DinurAlpha)
    s (δ ^ 2) hs hs1 (sq_pos_of_pos hδ)
  refine ⟨S, ?_⟩
  intro L hL
  obtain ⟨enc, C, henc, he, hpos, hyes, hno⟩ := registered_gap_family F hd hL
  let R := fun z ↦ GapBridge.system ((C z).preprocess E)
  let B := fun z ↦ Lax253009.CenteredProjection.fromConstraints (R z)
  let pu := RegularGameAlgorithms.vertexNumbering enc C henc he
  let pd := RegularGameAlgorithms.dartNumbering E
  let po := product pd (ComputableNumbering.finite (code (A := Bool)) code_injective)
  let pw := product pu pd
  let qu := centerNumbering S pu
  let qo := extensionNumbering S po pw
  let qw := questionNumbering S pw
  let H := fun z ↦ ProjectionRelabel.relabel (S.transform (B z))
    (qu.equiv z) (qo.equiv z) (qw.equiv z) (Equiv.refl _) (Equiv.refl _)
  have hbase : ComputableAmplification.Algorithms
      (RegularGameAlgorithms.vertexCode C)
      (prod (RegularGameAlgorithms.dartCode E) (ComputableEncoding.finite Bool))
      (prod (RegularGameAlgorithms.vertexCode C) (RegularGameAlgorithms.dartCode E))
      code (code (A := DinurAlpha × DinurAlpha)) B :=
    ConstraintAlgorithms.centered _ _ R (RegularGameAlgorithms.algorithms F hd enc C henc he)
  refine ⟨qu.size, qo.size, qw.size, qu.size_poly, qo.size_poly, qw.size_poly, ?_, H,
    numbered_transform _ _ B hbase pu po pw S, ?_, ?_⟩
  · intro z
    letI : Nonempty (Fin (C z).numEdges) := Fin.pos_iff_nonempty.mp (hpos z)
    exact ⟨Fin.pos_iff_nonempty.mpr ⟨qu.equiv z (Classical.arbitrary _)⟩,
      Fin.pos_iff_nonempty.mpr ⟨qo.equiv z (Classical.arbitrary _)⟩,
      Fin.pos_iff_nonempty.mpr ⟨qw.equiv z (Classical.arbitrary _)⟩⟩
  · intro z hz
    apply ProjectionRelabel.complete
    apply Lax253009Proofs.Amplification.Scheme.transform_complete
    apply Lax253009Proofs.CenteredProjection.from_constraints_complete
    apply GapBridge.system_complete
    exact ConstraintGraph.satisfiable_preprocess_of_satisfiable _ _ (hyes z hz)
  · intro z hz
    letI : Nonempty (Fin (C z).numEdges) := Fin.pos_iff_nonempty.mp (hpos z)
    letI : Nonempty ((C z).preprocess E).graph.V :=
      inferInstanceAs (Nonempty (C z).HalfEdge)
    apply ProjectionRelabel.sound
    apply Lax253009Proofs.CenteredProjection.center_sound_of_sym _ δ hδ.le
    apply hS (C z).HalfEdge (ConstraintGraph.PreDart E × Bool)
      ((C z).HalfEdge × ConstraintGraph.PreDart E) (B z)
      (Lax253009Proofs.CenteredProjection.from_constraints_uniform (R z))
    apply Lax253009Proofs.CenteredProjection.symmetrize_sound
    intro P Q
    have hgap : γ ≤ (((C z).preprocess E).unsatVal : ℝ) := by
      apply le_trans _ ((C z).le_unsatVal_preprocess E)
      apply mul_le_mul_of_nonneg_left _ (Dinur.preprocessConst_pos E).le
      exact_mod_cast hno z hz
    have hg := Lax253009Proofs.CenteredProjection.from_constraints_sound (R z) γ
      (GapBridge.system_sound _ γ hgap) P Q
    apply hg.trans
    dsimp only [s]
    have hmin := min_le_left γ (1 : ℝ)
    linarith

end Lax253009Proofs.RegisteredBridge
