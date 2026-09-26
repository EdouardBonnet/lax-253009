import Lax253009.SideConditionAveraging
import Lax253009Proofs.FourierProjection

namespace Lax253009Proofs

open Lax253009.LongCode Lax253009.BooleanFourier Lax253009.FourierProjection
open Lax253009.SideConditionAveraging

/--
---
conclusion: Lax253009.SideConditionAveraging.query_preserved
---
The extra queries force the averaging fiber to be constant at the queried value.
-/
theorem side_query_projection {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w)
    (h : Coordinate w) (hpass : AcceptsWithCondition A f h)
    (g : Coordinate w) (hg : Queried f g) :
    project (fun q ↦ sign (A q)) (satisfying h) g = sign (A g) := by
  apply fourier_projection_constant
  intro q hq
  apply congrArg sign
  symm
  apply hpass.2 g hg q
  intro x hx
  exact (hq x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)).symm

end Lax253009Proofs
