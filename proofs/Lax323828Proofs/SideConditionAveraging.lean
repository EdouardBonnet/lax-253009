import Lax323828.SideConditionAveraging
import Lax323828Proofs.FourierProjection

namespace Lax323828Proofs

open Lax323828.LongCode Lax323828.BooleanFourier Lax323828.FourierProjection
open Lax323828.SideConditionAveraging

/--
---
conclusion: Lax323828.SideConditionAveraging.query_preserved
---
The extra queries force the averaging fiber to be constant at the queried value.
-/
theorem side_query_projection {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w)
    (h : Coordinate w) (hpass : AcceptsWithCondition A f h)
    (g : Coordinate w) (hg : Queried f g) :
    project (fun q ↦ sign (A q)) (satisfying h) g = sign (A g) := by
  apply Lax323828.FourierProjection.constant_fiber
  intro q hq
  apply congrArg sign
  symm
  apply hpass.2 g hg q
  intro x hx
  exact (hq x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)).symm

end Lax323828Proofs
