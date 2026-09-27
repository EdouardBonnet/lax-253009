import Lax253009Proofs.RegisteredBridge.FAFTranscriptAlgorithms
import Lax253009Proofs.RegisteredBridge.SlotGraphAlgorithms
import Lax253009Proofs.LocalTestRelabel

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax253009Proofs.RegisteredBridge

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding ComputableNumbering
open Lax253009 CenteredProjection FAFLocalTests TestSampling
open FAFDataAlgorithms FAFPartAlgorithms FAFTranscriptAlgorithms
open scoped Classical

theorem finite_of_unary (n : ℕ) :
    Realizes (unary (fun _ ↦ n)) (ComputableEncoding.finite (Fin n)) (fun _ i ↦ i) :=
  fixed_map (fun i : Fin n ↦ List.replicate i.val true)
    (fun i j h ↦ Fin.ext (by simpa using congrArg List.length h)) code id

/-- The finite FAF system, now with uniform polynomial-time transcript and
consistency queries and explicit polynomial-time numbering of seeds and
proof coordinates. Its semantic guarantees transfer unchanged. -/
theorem computable_faf {U Ω W : Family} [∀ z, Fintype (U z)] [∀ z, Fintype (Ω z)]
    [∀ z, Fintype (W z)] {eu : Encoding U} {eo : Encoding Ω} {ew : Encoding W}
    {u w : ℕ} (n s q : ℕ) (pu : Numbering eu) (po : Numbering eo) (pw : Numbering ew)
    (G : ∀ z, System (U z) (Ω z) (W z) (LongCode.Word u) (LongCode.Word w))
    (h : ComputableAmplification.Algorithms eu eo ew code code G) :
    let pr := seedNumbering eu eo pu po u w n s q
    let pi := indexNumbering pu pw u w
    ∃ C : ∀ z, LocalTests.System (pr.size z) (pi.size z),
    ∃ E : ∀ z, SlotGraph.Enumeration (C z) (2 ^ (q + n * s)),
      SlotGraphAlgorithms.Algorithms E ∧
      (∀ z, Complete (FAFLocalTests.system (n := n) (s := s) (q := q)
        (G z).question (G z).project (G z).valid) → Complete (C z)) ∧
      (∀ z δ, Sound (FAFLocalTests.system (n := n) (s := s) (q := q)
        (G z).question (G z).project (G z).valid) δ → Sound (C z) δ) := by
  let pr := seedNumbering eu eo pu po u w n s q
  let pi := indexNumbering pu pw u w
  let er := fun z ↦ (pr.equiv z).symm.trans (randomEquiv (U z) (Ω z) u w n s q)
  let ei := fun z ↦ (pi.equiv z).symm.trans (indexEquiv (U z) (W z) u w)
  let C := fun z ↦ LocalTestRelabel.system
    (FAFLocalTests.system (n := n) (s := s) (q := q) (G z).question (G z).project (G z).valid)
    (er z) (ei z)
  let E := fun z ↦ LocalTestRelabel.enumeration
    (FAFSlots.enumeration (n := n) (s := s) (q := q) (G z).question (G z).project (G z).valid)
    (er z) (ei z)
  refine ⟨C, E, ?_, ?_, ?_⟩
  · let count := fun _ : Word ↦ 2 ^ (q + n * s)
    let ev := prod (unary pr.size) (unary count)
    have hr := comp (fst (unary pr.size) (unary count)) pr.element
    have hj := comp (snd (unary pr.size) (unary count)) (finite_of_unary (2 ^ (q + n * s)))
    have raw := pair_maps hr hj
    refine ⟨?_, ?_⟩
    · have hh := comp raw (valid_slot (n := n) (s := s) (q := q) pu pw G h)
      apply of_pointwise hh
      intro z v
      simp only [E, LocalTestRelabel.enumeration, FAFSlots.enumeration, er,
        Equiv.trans_apply, Equiv.symm_apply_apply]
      cases hp : FAFSlots.patternSlot
        (FAFSlots.data (G z).project (G z).valid ((pr.equiv z).symm v.1)) v.2 <;> rfl
    · have hi := pair_maps (comp (fst ev (unary pi.size)) raw)
        (comp (snd ev (unary pi.size)) pi.element)
      have hh := comp hi (view_slot (n := n) (s := s) (q := q) pu pw G h)
      apply of_pointwise hh
      intro z v
      simp only [E, LocalTestRelabel.enumeration, FAFSlots.enumeration, er, ei,
        Equiv.trans_apply, Equiv.symm_apply_apply]
      cases hp : FAFSlots.patternSlot
        (FAFSlots.data (G z).project (G z).valid ((pr.equiv z).symm v.1.1)) v.1.2 <;> rfl
  · intro z hz
    exact LocalTestRelabel.complete _ _ _ hz
  · intro z δ hz
    exact LocalTestRelabel.sound _ _ _ δ hz

end Lax253009Proofs.RegisteredBridge
