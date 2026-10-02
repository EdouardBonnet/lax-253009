import Lax323828.Graphs

/-!
---
title: Numbering finite graphs and the size of their encoding
type: theorem
---
A bijective numbering of the vertices of a finite simple graph gives a
Boolean adjacency matrix on $0,\ldots,n-1$ with the same clique number.
Its binary encoding has exactly $n+1+n^2$ bits. These facts connect abstract
consistency graphs to the input representation used by approximation
algorithms.
-/

namespace Lax323828.GraphEncoding

open Graphs

/-- Transfer adjacency along the vertex numbering `e` to obtain a Boolean matrix. -/
def numbered {α : Type} {n : ℕ} (G : SimpleGraph α) [DecidableRel G.Adj]
    (e : Fin n ≃ α) : Graph n where
  adjacent u v := decide (G.Adj (e u) (e v))
  loopless v := decide_eq_false (G.loopless.irrefl (e v))
  symmetric u v := decide_eq_decide.mpr (G.adj_comm (e u) (e v))

/-- Relabeling the vertices preserves the largest clique size. -/
axiom cliqueNumber_numbered {α : Type} [Fintype α] {n : ℕ}
    (G : SimpleGraph α) [DecidableRel G.Adj] (e : Fin n ≃ α) :
  (numbered G e).cliqueNumber = G.cliqueNum

/-- The encoding contains the unary vertex count, one separator, and `n²` matrix entries. -/
axiom encoding_length {n : ℕ} (G : Graph n) :
  G.encode.length = n + 1 + n * n

end Lax323828.GraphEncoding
