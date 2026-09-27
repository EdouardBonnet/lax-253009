import Lax253009Proofs.RegisteredBridge.ComputableViewArrays
import Lax253009Proofs.RegisteredBridge.ComputableDigits
import Lax253009Proofs.RegisteredBridge.SlotGraphAlgorithms

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax253009Proofs.RegisteredBridge.RepeatedSlotAlgorithms

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding ComputableNumbering
open Lax253009 LocalTests
open scoped Classical

theorem algorithms {r m A N k : Word → ℕ} {C : ∀ z, LocalTests.System (r z) (m z)}
    (E : ∀ z, SlotGraph.Enumeration (C z) (A z)) (hE : SlotGraphAlgorithms.Algorithms E)
    (seed : ∀ z, Fin (N z) → Fin (k z) → Fin (r z))
    (hseed : Realizes (prod (unary N) (unary k)) (unary r) (fun z v ↦ seed z v.1 v.2))
    (hm : UnaryFn m) (hk : UnaryFn k) (hA : UnaryFn A) :
    SlotGraphAlgorithms.Algorithms
      (fun z ↦ RepeatedSlotViews.repeatedEnumeration (E z) (k z) (N z) (seed z)) := by
  let B := fun z ↦ A z ^ k z
  let slot := prod (unary N) (unary B)
  let v := fun z (p : Fin (N z) × Fin (B z)) (j : Fin (k z)) ↦
    (E z).view (seed z p.1 j) ((@finFunctionFinEquiv (A z) (k z)).symm p.2 j)
  have houter := fst slot (unary k)
  have hsample := comp houter (fst (unary N) (unary B))
  have hcode := comp houter (snd (unary N) (unary B))
  have hindex := snd slot (unary k)
  have hquestion := comp (pair_maps hsample hindex) hseed
  have hdigit := comp (pair_maps hcode hindex) (ComputableDigits.digit_realizes A k hA)
  have query := pair_maps hquestion hdigit
  have hvalid := comp query hE.valid
  have hview : ComputableViewArrays.Algorithms (a := slot) v := by
    have hi := pair_maps (comp (fst (prod slot (unary k)) (unary m)) query)
      (snd (prod slot (unary k)) (unary m))
    have hh := comp hi hE.view
    exact hh
  constructor
  · have hall := Testable.forall_fin (a := slot)
      (p := fun z p j ↦ (E z).valid (seed z p.1 j)
        ((@finFunctionFinEquiv (A z) (k z)).symm p.2 j) = true)
      hk (testable_of_flag hvalid)
    have hcoh := ComputableViewArrays.coherent v hview hk hm
    have hh := (hall.and hcoh).realizes
    exact hh
  · exact ComputableViewArrays.union v hview hk

end Lax253009Proofs.RegisteredBridge.RepeatedSlotAlgorithms
