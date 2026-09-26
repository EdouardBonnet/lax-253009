import Lax253009.Graphs

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

namespace Lax253009.GraphEncoding

open Graphs

def numbered {α : Type} {n : ℕ} (G : SimpleGraph α) [DecidableRel G.Adj]
    (e : Fin n ≃ α) : Graph n where
  adjacent u v := decide (G.Adj (e u) (e v))
  loopless v := by simp
  symmetric u v := by simp only [G.adj_comm]

axiom cliqueNumber_numbered {α : Type} [Fintype α] {n : ℕ}
    (G : SimpleGraph α) [DecidableRel G.Adj] (e : Fin n ≃ α) :
  (numbered G e).cliqueNumber = G.cliqueNum

axiom encoding_length {n : ℕ} (G : Graph n) :
  G.encode.length = n + 1 + n * n

end Lax253009.GraphEncoding
