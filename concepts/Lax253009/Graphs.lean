import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.List.FinRange

/-!
---
title: Finite graphs and their binary encoding
type: definition
---
A graph on $n$ vertices is a symmetric Boolean adjacency matrix with zero
diagonal. Its vertices are $0,\ldots,n-1$. We encode it by $n$ one-bits,
one zero-bit, and its complete adjacency matrix in row-major order.
The encoding has length $n+1+n^2$, so polynomial time in its length is
equivalent to polynomial time in the number of vertices.

The clique number $\omega(G)$ is the maximum cardinality of a clique.
-/

namespace Lax253009.Graphs

structure Graph (n : ℕ) where
  adjacent : Fin n → Fin n → Bool
  loopless : ∀ v, adjacent v v = false
  symmetric : ∀ u v, adjacent u v = adjacent v u

def Graph.simpleGraph {n : ℕ} (G : Graph n) : SimpleGraph (Fin n) where
  Adj u v := G.adjacent u v = true
  symm u v h := by rw [← G.symmetric]; exact h
  loopless := ⟨fun v ↦ by simp [G.loopless]⟩

def Graph.encode {n : ℕ} (G : Graph n) : List Bool :=
  List.replicate n true ++ [false] ++
    (List.finRange n).flatMap (fun u ↦ (List.finRange n).map (G.adjacent u))

noncomputable def Graph.cliqueNumber {n : ℕ} (G : Graph n) : ℕ :=
  G.simpleGraph.cliqueNum

end Lax253009.Graphs
