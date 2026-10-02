import Lax323828.LocalTests
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Sigma

/-!
---
title: The consistency graph of accepting local views
type: definition
---
There is a vertex for each pair consisting of a random choice and an
accepting local view. Two vertices are adjacent when their random choices
differ and their partial assignments agree wherever both are defined.
This is the consistency graph used in the PCP-to-clique reduction.

Excluding edges between vertices with the same random choice ensures that
a clique contains at most one accepting view for each choice, even when
the supplied lists contain overlapping views.
-/

namespace Lax323828.ConsistencyGraph

open LocalTests

abbrev Vertex {r m : ℕ} (C : System r m) :=
  (seed : Fin r) × {a // a ∈ C.accepting seed}

def graph {r m : ℕ} (C : System r m) : SimpleGraph (Vertex C) where
  Adj u v := u.1 ≠ v.1 ∧ Compatible u.2.1 v.2.1
  symm := ⟨fun _ _ h ↦ ⟨Ne.symm h.1,
    fun i x y hx hy ↦ (h.2 i y x hy hx).symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

end Lax323828.ConsistencyGraph
