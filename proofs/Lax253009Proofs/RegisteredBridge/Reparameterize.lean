import Lax253009Proofs.RegisteredBridge.SlotGraphAlgorithms

set_option backward.isDefEq.respectTransparency false

namespace Lax253009Proofs.RegisteredBridge

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding ComputableNumbering

theorem ComputableEncoding.Realizes.reparameterize {A B : Family} {a : Encoding A} {b : Encoding B}
    {f : ∀ z, A z → B z} (hf : Realizes a b f) {P : Word → Word} (hP : P ∈ FP) :
    Realizes (fun z ↦ a (P z)) (fun z ↦ b (P z)) (fun z ↦ f (P z)) := by
  obtain ⟨F, hF, hc⟩ := hf
  refine ⟨fun w ↦ F (pair (P (pairFst w)) (pairSnd w)),
    mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hP) pairSnd_mem_FP) hF, ?_⟩
  intro z v
  simp only [pairFst_pair, pairSnd_pair, hc]

noncomputable def ComputableNumbering.Numbering.reparameterize {A : Family} {a : Encoding A}
    (p : Numbering a) {P : Word → Word} (hP : P ∈ FP) : Numbering (fun z ↦ a (P z)) where
  size := fun z ↦ p.size (P z)
  equiv := fun z ↦ p.equiv (P z)
  size_poly := p.size_poly.comp hP
  index := p.index.reparameterize hP
  element := p.element.reparameterize hP

theorem SlotGraphAlgorithms.Algorithms.reparameterize {r m A : Word → ℕ}
    {C : ∀ z, Lax253009.LocalTests.System (r z) (m z)}
    {E : ∀ z, SlotGraph.Enumeration (C z) (A z)} (hE : SlotGraphAlgorithms.Algorithms E)
    {P : Word → Word} (hP : P ∈ FP) :
    SlotGraphAlgorithms.Algorithms (fun z ↦ E (P z)) :=
  ⟨hE.valid.reparameterize hP, hE.view.reparameterize hP⟩

end Lax253009Proofs.RegisteredBridge
