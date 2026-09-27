import Lax253009Proofs.RegisteredBridge.ComputableAmplification
import Lax253009Proofs.RegisteredBridge.RegularAlgorithm
import Lax253009Proofs.GapSatisfiability

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax253009Proofs.RegisteredBridge.ConstraintAlgorithms

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding
open ComputableAmplification

variable {V D : Family} {A : Type} [Fintype A]

structure Algorithms (ev : Encoding V) (ed : Encoding D)
    (C : ∀ z, Lax253009.ProjectionGames.System (V z) (D z) A) : Prop where
  reverse : Realizes (prod ev ed) (prod ev ed) (fun z ↦ (C z).reverse)
  relation : Realizes (prod (prod ev ed) (ComputableEncoding.finite (A × A)))
    (ComputableEncoding.finite Bool) (fun z p ↦ (C z).relation p.1 p.2.1 p.2.2)

theorem centered (ev : Encoding V) (ed : Encoding D)
    (C : ∀ z, Lax253009.ProjectionGames.System (V z) (D z) A) (h : Algorithms ev ed C) :
    ComputableAmplification.Algorithms ev (prod ed (ComputableEncoding.finite Bool)) (prod ev ed)
      code (code (A := A × A)) (fun z ↦ Lax253009.CenteredProjection.fromConstraints (C z)) := by
  let eb := ComputableEncoding.finite Bool
  let eω := prod ed eb
  let ec := prod ev eω
  have hi : Realizes ec eb (fun _ p ↦ p.2.2) := comp (snd ev eω) (snd ed eb)
  have hvd : Realizes ec (prod ev ed) (fun _ p ↦ (p.1, p.2.1)) :=
    pair_maps (fst ev eω) (comp (snd ev eω) (fst ed eb))
  have hq : Realizes ec (prod ev ed) (fun z p ↦ (C z).question p.1 p.2) := by
    apply finite_dispatch (f := fun b z p ↦ if b then (C z).reverse (p.1, p.2.1) else (p.1, p.2.1)) hi
    intro b
    cases b
    · exact hvd
    · exact comp hvd h.reverse
  let ey := ComputableEncoding.finite (A × A)
  let eargs := prod ec ey
  have houter : Realizes eargs ec (fun _ p ↦ p.1) := fst ec ey
  have hquestion := comp houter hq
  have hanswer : Realizes eargs ey (fun _ p ↦ p.2) := snd ec ey
  have hrel := comp (pair_maps hquestion hanswer) h.relation
  have hbit := comp houter hi
  have hproj : Realizes eargs (ComputableEncoding.finite A)
      (fun _ p ↦ Lax253009.ProjectionGames.System.project p.1.2.2 p.2) := by
    apply finite_dispatch (f := fun b _ p ↦ Lax253009.ProjectionGames.System.project b p.2) hbit
    intro b
    exact comp hanswer (finite_map (Lax253009.ProjectionGames.System.project b))
  exact ⟨hq, hrel, hproj⟩

end Lax253009Proofs.RegisteredBridge.ConstraintAlgorithms
