import Lax323828.GraphEncoding
import Mathlib.Tactic

namespace Lax323828Proofs

open Lax323828.Graphs Lax323828.GraphEncoding

private theorem cliqueNum_le_of_embedding {α β : Type} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) (e : α ↪ β)
    (he : ∀ u v, G.Adj u v → H.Adj (e u) (e v)) :
    G.cliqueNum ≤ H.cliqueNum := by
  classical
  obtain ⟨s, hs, hc⟩ := G.exists_isNClique_cliqueNum
  have hclique : H.IsClique (s.image e) := by
    intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    exact he x y (hs hx hy (fun h ↦ huv (congrArg e h)))
  have hcard := hclique.card_le_cliqueNum
  simpa [Finset.card_image_of_injective _ e.injective, hc] using hcard

/--
---
conclusion: Lax323828.GraphEncoding.cliqueNumber_numbered
---
Transport cliques in both directions along the vertex numbering.
-/
theorem numbered_cliqueNumber {α : Type} [Fintype α] {n : ℕ}
    (G : SimpleGraph α) [DecidableRel G.Adj] (e : Fin n ≃ α) :
    (numbered G e).cliqueNumber = G.cliqueNum := by
  apply le_antisymm
  · apply cliqueNum_le_of_embedding (numbered G e).simpleGraph G e.toEmbedding
    intro u v huv
    exact of_decide_eq_true huv
  · apply cliqueNum_le_of_embedding G (numbered G e).simpleGraph e.symm.toEmbedding
    intro u v huv
    change decide (G.Adj (e (e.symm u)) (e (e.symm v))) = true
    simpa using huv

/--
---
conclusion: Lax323828.GraphEncoding.encoding_length
---
The unary vertex count and delimiter occupy n+1 bits, and the n rows
of the adjacency matrix occupy n bits each.
-/
theorem graph_encoding_length {n : ℕ} (G : Graph n) :
    G.encode.length = n + 1 + n * n := by
  simp [Graph.encode, List.length_flatMap]
  omega

end Lax323828Proofs
