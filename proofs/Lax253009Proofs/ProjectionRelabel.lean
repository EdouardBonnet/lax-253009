import Lax253009Proofs.CenteredProjection

namespace Lax253009Proofs

open Lax253009 Lax253009.FiniteProbability Lax253009.CenteredProjection
open scoped BigOperators

namespace ProjectionRelabel

def relabel {U Ω W X Y U' Ω' W' X' Y' : Type}
    (G : System U Ω W X Y) (eu : U ≃ U') (eω : Ω ≃ Ω') (ew : W ≃ W')
    (ex : X ≃ X') (ey : Y ≃ Y') : System U' Ω' W' X' Y' where
  question u ω := ew (G.question (eu.symm u) (eω.symm ω))
  valid u ω y := G.valid (eu.symm u) (eω.symm ω) (ey.symm y)
  project u ω y := ex (G.project (eu.symm u) (eω.symm ω) (ey.symm y))

theorem complete {U Ω W X Y U' Ω' W' X' Y' : Type}
    (G : System U Ω W X Y) (eu : U ≃ U') (eω : Ω ≃ Ω') (ew : W ≃ W')
    (ex : X ≃ X') (ey : Y ≃ Y') (h : G.Complete) :
    (relabel G eu eω ew ex ey).Complete := by
  obtain ⟨P, Q, h⟩ := h
  refine ⟨fun w ↦ ey (P (ew.symm w)), fun u ↦ ex (Q (eu.symm u)), ?_⟩
  intro u ω
  simpa only [System.Test, relabel, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
    using h (eu.symm u) (eω.symm ω)

theorem sound {U Ω W X Y U' Ω' W' X' Y' : Type}
    [Fintype U] [Fintype Ω] [Fintype U'] [Fintype Ω']
    (G : System U Ω W X Y) (eu : U ≃ U') (eω : Ω ≃ Ω') (ew : W ≃ W')
    (ex : X ≃ X') (ey : Y ≃ Y') (s : ℝ) (h : G.Sound s) :
    (relabel G eu eω ew ex ey).Sound s := by
  intro P Q
  have he := finite_probability_equiv (eu.symm.prodCongr eω.symm)
    (fun z : U' × Ω' ↦ (relabel G eu eω ew ex ey).Test z.1 z.2
      (P ((relabel G eu eω ew ex ey).question z.1 z.2)) (Q z.1))
    (fun z : U × Ω ↦ G.Test z.1 z.2 (ey.symm (P (ew (G.question z.1 z.2))))
      (ex.symm (Q (eu z.1)))) (by
        intro z
        simp only [System.Test, relabel, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
          Equiv.apply_symm_apply]
        exact and_congr_right fun _ ↦ ex.eq_symm_apply.symm)
  rw [he]
  exact h (fun w ↦ ey.symm (P (ew w))) (fun u ↦ ex.symm (Q (eu u)))

theorem uniform {U Ω W X Y U' Ω' W' X' Y' : Type}
    [Fintype U] [Fintype Ω] [Fintype W] [Fintype U'] [Fintype Ω'] [Fintype W']
    (G : System U Ω W X Y) (eu : U ≃ U') (eω : Ω ≃ Ω') (ew : W ≃ W')
    (ex : X ≃ X') (ey : Y ≃ Y') (h : G.Uniform) :
    (relabel G eu eω ew ex ey).Uniform := by
  intro f
  change (𝔼 u, 𝔼 ω, f (ew (G.question (eu.symm u) (eω.symm ω)))) = _
  calc
    _ = 𝔼 u : U, 𝔼 ω : Ω, f (ew (G.question u ω)) := by
      rw [Fintype.expect_equiv eu.symm _
        (fun u ↦ 𝔼 ω : Ω', f (ew (G.question u (eω.symm ω)))) (fun _ ↦ rfl)]
      apply Finset.expect_congr rfl
      intro u _
      exact Fintype.expect_equiv eω.symm _ (fun ω ↦ f (ew (G.question u ω))) (fun _ ↦ rfl)
    _ = 𝔼 w : W, f (ew w) := h (fun w ↦ f (ew w))
    _ = _ := Fintype.expect_equiv ew _ f (fun _ ↦ rfl)

end ProjectionRelabel
end Lax253009Proofs
