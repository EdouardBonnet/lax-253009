import Lax253009Proofs.SlotGraph
import Lax253009Proofs.FiniteProbability

namespace Lax253009Proofs.LocalTestRelabel

open Lax253009 LocalTests TestSampling FiniteProbability
open scoped Classical

noncomputable def system {r m r' m' : ℕ} (C : LocalTests.System r m)
    (er : Fin r' ≃ Fin r) (ei : Fin m' ≃ Fin m) : LocalTests.System r' m' :=
  ⟨fun seed ↦ (C.accepting (er seed)).image (fun v i ↦ v (ei i))⟩

theorem passes {r m r' m' : ℕ} (C : LocalTests.System r m)
    (er : Fin r' ≃ Fin r) (ei : Fin m' ≃ Fin m) (π : Oracle m') (seed : Fin r') :
    Passes (system C er ei) π seed ↔ Passes C (fun i ↦ π (ei.symm i)) (er seed) := by
  constructor
  · rintro ⟨v, hv, he⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    refine ⟨a, ha, ?_⟩
    intro i b hb
    apply he (ei.symm i) b
    simpa only [Equiv.apply_symm_apply] using hb
  · rintro ⟨a, ha, he⟩
    refine ⟨fun i ↦ a (ei i), Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    intro i b hb
    simpa only [Equiv.symm_apply_apply] using he (ei i) b hb

theorem complete {r m r' m' : ℕ} (C : LocalTests.System r m)
    (er : Fin r' ≃ Fin r) (ei : Fin m' ≃ Fin m) (h : Complete C) :
    Complete (system C er ei) := by
  obtain ⟨π, hπ⟩ := h
  refine ⟨fun i ↦ π (ei i), fun seed ↦ (passes C er ei _ seed).mpr ?_⟩
  simpa only [Equiv.apply_symm_apply] using hπ (er seed)

theorem sound {r m r' m' : ℕ} (C : LocalTests.System r m)
    (er : Fin r' ≃ Fin r) (ei : Fin m' ≃ Fin m) (p : ℝ) (h : Sound C p) :
    Sound (system C er ei) p := by
  intro π
  rw [finite_probability_equiv er _ (Passes C (fun i ↦ π (ei.symm i))) (passes C er ei π)]
  exact h _

noncomputable def enumeration {r m r' m' A : ℕ} {C : LocalTests.System r m}
    (E : SlotGraph.Enumeration C A) (er : Fin r' ≃ Fin r) (ei : Fin m' ≃ Fin m) :
    SlotGraph.Enumeration (system C er ei) A where
  valid seed j := E.valid (er seed) j
  view seed j i := E.view (er seed) j (ei i)
  sound seed j hj := Finset.mem_image.mpr ⟨E.view (er seed) j, E.sound _ _ hj, rfl⟩
  complete seed a ha := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, hview⟩ := E.complete (er seed) v hv
    exact ⟨j, hj, by rw [hview]⟩

end Lax253009Proofs.LocalTestRelabel
