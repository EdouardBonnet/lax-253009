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

namespace Lax253009.LocalTests

abbrev Oracle (m : ℕ) := Fin m → Bool
abbrev View (m : ℕ) := Fin m → Option Bool

def Extends {m : ℕ} (π : Oracle m) (a : View m) : Prop :=
  ∀ i b, a i = some b → π i = b

def Compatible {m : ℕ} (a b : View m) : Prop :=
  ∀ i x y, a i = some x → b i = some y → x = y

structure System (r m : ℕ) where
  accepting : Fin r → Finset (View m)

noncomputable def System.acceptedSeeds {r m : ℕ} (C : System r m)
    (π : Oracle m) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter fun seed ↦ ∃ a ∈ C.accepting seed, Extends π a

noncomputable def System.optimum {r m : ℕ} (C : System r m) : ℕ :=
  Finset.univ.sup fun π : Oracle m ↦ (C.acceptedSeeds π).card

end Lax253009.LocalTests
