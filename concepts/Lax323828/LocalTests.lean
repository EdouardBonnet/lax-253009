import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Lattice.Fold

/-!
---
title: Accepting local views of a proof
type: definition
---
Fix a proof with $m$ Boolean positions and a set of $r$ random choices.
A local view is a partial assignment to proof positions. For each random
choice, a finite list of accepting local views specifies a test: a proof
passes when it extends at least one of those views.

This is the finite combinatorial data extracted from a verifier on a fixed
input. A local view records every queried position and its answer, including
positions chosen adaptively. No running-time assertion is built into this
data. Uniform computation of the lists is a separate obligation.
-/

namespace Lax323828.LocalTests

open scoped Classical

/-- A complete Boolean proof with `m` positions. -/
abbrev Oracle (m : ℕ) := Fin m → Bool
/-- A partial proof; `none` means that the position is not queried. -/
abbrev View (m : ℕ) := Fin m → Option Bool

/-- The complete proof agrees with every specified answer in the local view. -/
def Extends {m : ℕ} (π : Oracle m) (a : View m) : Prop :=
  ∀ i b, a i = some b → π i = b

/-- The two partial views agree at all positions where both specify an answer. -/
def Compatible {m : ℕ} (a b : View m) : Prop :=
  ∀ i x y, a i = some x → b i = some y → x = y

/-- For each random choice, the collection of local views that make the verifier accept. -/
structure System (r m : ℕ) where
  /-- The acceptable partial answer patterns for this random choice. -/
  accepting : Fin r → Finset (View m)

/-- The random choices on which the supplied proof extends an accepting view. -/
noncomputable def System.acceptedSeeds {r m : ℕ} (C : System r m)
    (π : Oracle m) : Finset (Fin r) :=
  Finset.univ.filter fun seed ↦ ∃ a ∈ C.accepting seed, Extends π a

/-- The largest number of accepting random choices attained by any single proof. -/
noncomputable def System.optimum {r m : ℕ} (C : System r m) : ℕ :=
  Finset.univ.sup fun π : Oracle m ↦ (C.acceptedSeeds π).card

end Lax323828.LocalTests
