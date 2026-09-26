import Lax253009.LongCode
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

namespace Lax253009.LongCodePatterns

open LongCode

abbrev Pattern (w : ℕ) := Coordinate w → Option Bool

noncomputable def restrict {w : ℕ} (Q : Coordinate w → Prop) (A : Table w) :
    Pattern w := by
  classical
  exact fun g ↦ if Q g then some (A g) else none

noncomputable def patterns {w s : ℕ} (f : Fin s → Coordinate w) : Finset (Pattern w) := by
  classical
  exact (Finset.univ.filter (fun A : Table w ↦ Accepts A f)).image (restrict (Queried f))

def SideQueried {w s : ℕ} (f : Fin s → Coordinate w) (h g' : Coordinate w) : Prop :=
  ∃ g, Queried f g ∧ AgreesOn h g g'

noncomputable def sidePatterns {w s : ℕ} (f : Fin s → Coordinate w)
    (h : Coordinate w) : Finset (Pattern w) := by
  classical
  exact (Finset.univ.filter (fun A : Table w ↦ AcceptsWithCondition A f h)).image
    (restrict (SideQueried f h))

axiom free_bits {w s : ℕ} (f : Fin s → Coordinate w) :
  (patterns f).card ≤ 2 ^ s

axiom side_free_bits {w s : ℕ} (f : Fin s → Coordinate w) (h : Coordinate w) :
  (sidePatterns f h).card ≤ 2 ^ s

end Lax253009.LongCodePatterns
