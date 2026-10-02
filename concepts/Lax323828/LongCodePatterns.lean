import Lax323828.LongCode
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Card

/-!
---
title: Free bits of the complete nonadaptive test
type: theorem
---
For fixed random functions, record an accepting table only at queried
coordinates, leaving other coordinates unspecified. There are at most
$2^s$ distinct such answer patterns. The same bound holds when all the
queries imposed by a side condition are included. Thus the CNA test and
its extension both use at most $s$ free bits.

Patterns are explicitly enumerated as restrictions of accepting tables.
The bound counts distinct patterns, not distinct tables: the unqueried
entries of a table can be arbitrary.
-/

namespace Lax323828.LongCodePatterns

open scoped Classical

open LongCode

/-- A partial Boolean answer table; `none` marks an unqueried coordinate. -/
abbrev Pattern (w : ℕ) := Coordinate w → Option Bool

/-- Record the table answers on the queried coordinates and leave the others unspecified. -/
noncomputable def restrict {w : ℕ} (Q : Coordinate w → Prop) (A : Table w) :
    Pattern w :=
  fun g ↦ if Q g then some (A g) else none

/-- All queried answer patterns arising from accepting tables. -/
noncomputable def patterns {w s : ℕ} (f : Fin s → Coordinate w) : Finset (Pattern w) :=
  (Finset.univ.filter (fun A : Table w ↦ Accepts A f)).image (restrict (Queried f))

/-- A coordinate queried by the test or forced by agreement on the side condition. -/
def SideQueried {w s : ℕ} (f : Fin s → Coordinate w) (h g' : Coordinate w) : Prop :=
  ∃ g, Queried f g ∧ AgreesOn h g g'

/-- All queried answer patterns arising from tables accepted with the side condition. -/
noncomputable def sidePatterns {w s : ℕ} (f : Fin s → Coordinate w)
    (h : Coordinate w) : Finset (Pattern w) :=
  (Finset.univ.filter (fun A : Table w ↦ AcceptsWithCondition A f h)).image
    (restrict (SideQueried f h))

axiom free_bits {w s : ℕ} (f : Fin s → Coordinate w) :
  (patterns f).card ≤ 2 ^ s

axiom side_free_bits {w s : ℕ} (f : Fin s → Coordinate w) (h : Coordinate w) :
  (sidePatterns f h).card ≤ 2 ^ s

end Lax323828.LongCodePatterns
