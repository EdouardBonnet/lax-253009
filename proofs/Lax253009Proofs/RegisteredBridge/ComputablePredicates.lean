import Lax253009Proofs.RegisteredBridge.ComputableFiniteFunctions

set_option backward.isDefEq.respectTransparency false

namespace Lax253009Proofs.RegisteredBridge.ComputableEncoding

open PCPFoundation.Complexity FiniteEncoding ComputableNumbering
open scoped Classical

variable {A B : Family} {a : Encoding A} {b : Encoding B}

theorem testable_eq (p : Numbering b) {f g : ∀ z, A z → B z}
    (hf : Realizes a b f) (hg : Realizes a b g) :
    Testable a (fun z v ↦ f z v = g z v) :=
  (testable_fin_eq (comp hf p.index) (comp hg p.index)).of_iff
    (fun z _ ↦ (p.equiv z).injective.eq_iff)

theorem Testable.ite_realizes {P : ∀ z, A z → Prop} {f g : ∀ z, A z → B z}
    (hp : Testable a P) (hf : Realizes a b f) (hg : Realizes a b g) :
    Realizes a b (fun z v ↦ if P z v then f z v else g z v) := by
  have hh := finite_dispatch (b := b)
    (f := fun bit z v ↦ if bit then f z v else g z v) hp.realizes
    (fun bit ↦ Bool.rec hg hf bit)
  apply of_pointwise hh
  intro z v
  by_cases h : P z v <;> simp [h]

theorem Testable.forall_finite {I : Type} [Fintype I] {P : ∀ z, A z → I → Prop}
    (hp : ∀ i, Testable a (fun z v ↦ P z v i)) :
    Testable a (fun z v ↦ ∀ i, P z v i) := by
  have h := finite_function (fun i ↦ (hp i).realizes)
  have hh := ComputableEncoding.comp h (finite_map (fun f : I → Bool ↦ decide (∀ i, f i = true)))
  apply (testable_of_flag hh).of_iff
  intro z v
  simp

end Lax253009Proofs.RegisteredBridge.ComputableEncoding
