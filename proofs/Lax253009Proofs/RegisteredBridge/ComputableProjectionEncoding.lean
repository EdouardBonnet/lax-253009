import Lax253009Proofs.RegisteredBridge.ComputableAmplification
import Lax253009Proofs.ProjectionEncoding

set_option backward.isDefEq.respectTransparency false

namespace Lax253009Proofs.RegisteredBridge.ComputableProjectionEncoding

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding
open ComputableAmplification Lax253009.CenteredProjection

variable {U Ω W : Family} {eu : Encoding U} {eo : Encoding Ω} {ew : Encoding W}
variable {X Y : Type} [Fintype X] [Fintype Y]
variable {ex : X → Word} {ey : Y → Word}

noncomputable def encoded {u w : ℕ} (ix : X ↪ Lax253009.LongCode.Word u)
    (iy : Y ↪ Lax253009.LongCode.Word w) (G : ∀ z, System (U z) (Ω z) (W z) X Y) :
    ∀ z, System (U z) (Ω z) (W z) (Lax253009.LongCode.Word u) (Lax253009.LongCode.Word w) :=
  fun z ↦ ⟨(G z).question, Lax253009.ProjectionEncoding.valid iy (G z).valid,
    Lax253009.ProjectionEncoding.project ix iy (G z).project⟩

/-- Encoding the fixed answer alphabets does not change the polynomial-time
query property. Invalid encodings are handled by a fixed finite lookup. -/
theorem algorithms {u w : ℕ} (ix : X ↪ Lax253009.LongCode.Word u)
    (iy : Y ↪ Lax253009.LongCode.Word w) (hx : Function.Injective ex)
    (G : ∀ z, System (U z) (Ω z) (W z) X Y) (h : Algorithms eu eo ew ex ey G) :
    Algorithms eu eo ew code code (encoded ix iy G) := by
  classical
  let src := prod (prod eu eo) (ComputableEncoding.finite (Lax253009.LongCode.Word w))
  have hk := comp (snd (prod eu eo) (ComputableEncoding.finite (Lax253009.LongCode.Word w)))
    (finite_map (Lax253009.ProjectionEncoding.decode iy))
  have input (y : Y) : Realizes src (prod (prod eu eo) (fun _ ↦ ey))
      (fun _ p ↦ (p.1, y)) :=
    pair_maps (fst (prod eu eo) (ComputableEncoding.finite (Lax253009.LongCode.Word w)))
      ⟨fun _ ↦ ey y, constFn_mem_FP _, fun _ _ ↦ rfl⟩
  refine ⟨h.question, ?_, ?_⟩
  · have hh := finite_dispatch (b := ComputableEncoding.finite Bool) (f := fun y z p ↦
        match y with | none => false | some y => (G z).valid p.1.1 p.1.2 y) hk
      (fun y ↦ ?_)
    · apply of_pointwise hh
      intro z p
      cases hd : Lax253009.ProjectionEncoding.decode iy p.2 <;>
        simp only [encoded, Lax253009.ProjectionEncoding.valid, hd]
    · cases y with
      | none => exact finite_constant src false
      | some y =>
        have hy := comp (input y) h.valid
        exact hy
  · have hout := fixed_map ex hx (code (A := Lax253009.LongCode.Word u)) ix
    have hh := finite_dispatch (b := ComputableEncoding.finite (Lax253009.LongCode.Word u))
      (f := fun y z p ↦
        match y with | none => fun _ : Fin u ↦ false | some y => ix ((G z).project p.1.1 p.1.2 y)) hk
      (fun y ↦ ?_)
    · apply of_pointwise hh
      intro z p
      cases hd : Lax253009.ProjectionEncoding.decode iy p.2 <;>
        simp only [encoded, Lax253009.ProjectionEncoding.project, hd]
    · cases y with
      | none => exact finite_constant src (fun _ ↦ false)
      | some y =>
        have hy := comp (input y) h.project
        have hz := comp hy hout
        exact hz

end Lax253009Proofs.RegisteredBridge.ComputableProjectionEncoding
