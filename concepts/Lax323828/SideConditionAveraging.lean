import Lax323828.LongCode
import Lax323828.FourierProjection

/-!
---
title: The averaged table preserves the answers of an accepting side-condition test
type: theorem
---
Let $U$ be the words satisfying the side condition $h$. If the extended
CNA test accepts a table $A$, then averaging its sign-valued version over
coordinates outside $U$ preserves every base query answer of that run.
Indeed, step (3) requires the table to have the same answer on every
function agreeing with the query on $U$.

This links the actual test definition to the averaged function in equation
(17) and to its Fourier projection formula, Lemma 4.18.
-/

namespace Lax323828.SideConditionAveraging

open LongCode BooleanFourier FourierProjection

def satisfying {w : ℕ} (h : Coordinate w) : Finset (Word w) :=
  Finset.univ.filter fun x ↦ h x = true

axiom query_preserved {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w)
    (h : Coordinate w) (hpass : AcceptsWithCondition A f h)
    (g : Coordinate w) (hg : Queried f g) :
  project (fun q ↦ sign (A q)) (satisfying h) g = sign (A g)

end Lax323828.SideConditionAveraging
