import Lax323828Proofs.RegisteredBridge.ComputableAmplification
import Lax323828Proofs.RegisteredBridge.ComputableNumbering
import Lax323828Proofs.ProjectionRelabel

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax323828Proofs.RegisteredBridge.ComputableAmplification

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding ComputableNumbering
open Lax323828.CenteredProjection Lax323828.Amplification

variable {U Ω W : Family} {eu : Encoding U} {eo : Encoding Ω} {ew : Encoding W}

noncomputable def centerNumbering (S : Scheme) (p : Numbering eu) :
    Numbering (fun z ↦ centerCode S (eu z)) := match S with
  | .base => p
  | .step _ S => product (centerNumbering S p) (centerNumbering S p)

noncomputable def questionNumbering (S : Scheme) (p : Numbering ew) :
    Numbering (fun z ↦ questionCode S (ew z)) := match S with
  | .base => p
  | .step t S => product (tuples (questionNumbering S p) t) (tuples (questionNumbering S p) t)

noncomputable def extensionNumbering (S : Scheme) (p : Numbering eo) (q : Numbering ew) :
    Numbering (fun z ↦ extensionCode S (eo z) (ew z)) := match S with
  | .base => p
  | .step t S =>
      let factor := product (extensionNumbering S p q)
        (product (ComputableNumbering.finite (code (A := Fin t)) code_injective)
          (tuples (questionNumbering S q) t))
      product factor factor

theorem relabel_questions {X Y : Type} (ex : X → Word) (ey : Y → Word)
    (G : ∀ z, System (U z) (Ω z) (W z) X Y) (h : Algorithms eu eo ew ex ey G)
    (pu : Numbering eu) (po : Numbering eo) (pw : Numbering ew) :
    Algorithms (unary pu.size) (unary po.size) (unary pw.size) ex ey
      (fun z ↦ ProjectionRelabel.relabel (G z) (pu.equiv z) (po.equiv z) (pw.equiv z)
        (Equiv.refl X) (Equiv.refl Y)) := by
  have hin : Realizes (prod (unary pu.size) (unary po.size)) (prod eu eo)
      (fun z p ↦ ((pu.equiv z).symm p.1, (po.equiv z).symm p.2)) :=
    pair_maps (comp (fst _ _) pu.element) (comp (snd _ _) po.element)
  have hq := comp (comp hin h.question) pw.index
  have hargs : Realizes (prod (prod (unary pu.size) (unary po.size)) (fun _ ↦ ey))
      (prod (prod eu eo) (fun _ ↦ ey))
      (fun z p ↦ (((pu.equiv z).symm p.1.1, (po.equiv z).symm p.1.2), p.2)) :=
    pair_maps (comp (fst _ _) hin) (snd _ _)
  exact ⟨hq, comp hargs h.valid, comp hargs h.project⟩

theorem numbered_transform {X Y : Type} (ex : X → Word) (ey : Y → Word)
    (G : ∀ z, System (U z) (Ω z) (W z) X Y) (h : Algorithms eu eo ew ex ey G)
    (pu : Numbering eu) (po : Numbering eo) (pw : Numbering ew) (S : Scheme) :
    Algorithms (unary (centerNumbering S pu).size) (unary (extensionNumbering S po pw).size)
      (unary (questionNumbering S pw).size) (centerCode S ex) (questionCode S ey)
      (fun z ↦ ProjectionRelabel.relabel (S.transform (G z))
        ((centerNumbering S pu).equiv z) ((extensionNumbering S po pw).equiv z)
        ((questionNumbering S pw).equiv z) (Equiv.refl _) (Equiv.refl _)) :=
  relabel_questions _ _ _ (transform _ _ _ _ _ _ h S)
    (centerNumbering S pu) (extensionNumbering S po pw) (questionNumbering S pw)

end Lax323828Proofs.RegisteredBridge.ComputableAmplification
