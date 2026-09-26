import Lax253009.CliqueCorrespondence
import Lax253009.GraphEncoding
import Lax253009.Approximation

/-!
---
title: The consistency graph as an approximation input
type: theorem
---
Numbering the vertices of the consistency graph produces an input to the
clique approximation problem whose clique number is exactly the optimum
acceptance count of the local tests.

An $N^{1-\varepsilon}$-approximation separates optimum acceptance counts
at most $a$ from counts at least $b$ whenever
$N^{1-\varepsilon}a<b$, provided $N>0$. The separating predicate compares
the returned integer with $a$. The same polynomial-time estimator works
for every such system and gap.

This statement supplies the graph-theoretic and numerical transfer.
Efficiently producing the accepting views and the numbered graph from a
language input remains a separate machine-construction obligation.
-/

namespace Lax253009.EncodedReduction

open LocalTests ConsistencyGraph Lax434930.PolynomialTime

noncomputable def output {r m : ℕ} (C : System r m) :
    Graphs.Graph (Fintype.card (Vertex C)) := by
  classical
  exact GraphEncoding.numbered (graph C) (Fintype.equivFin (Vertex C)).symm

axiom cliqueNumber_output {r m : ℕ} (C : System r m) :
  (output C).cliqueNumber = C.optimum

axiom approximation_separates (ε : ℝ) (hε : Approximation.Approximable ε) :
  ∃ estimate : Word → ℕ,
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate) ∧
    ∀ (r m : ℕ) (C : System r m), 0 < Fintype.card (Vertex C) →
      ∀ a b : ℕ,
        Real.rpow (Fintype.card (Vertex C) : ℝ) (1 - ε) * (a : ℝ) < (b : ℝ) →
        (C.optimum ≤ a → estimate (output C).encode ≤ a) ∧
        (b ≤ C.optimum → a < estimate (output C).encode)

end Lax253009.EncodedReduction
