import Lax323828.ConsistencyGraph

/-!
---
title: Clique number equals the maximum number of accepting random choices
type: theorem
---
A proof accepted on $k$ random choices yields a clique of size $k$ in the
consistency graph. Conversely, the local views of any clique extend to
one global proof accepted on at least as many random choices.
Consequently the clique number equals the maximum number of random choices
on which a proof is accepted.

If every proof is accepted on at most $s$ choices, the clique number is at
most $s$. Perfect completeness gives a clique of size $r$. If each random
choice has at most $A$ accepting views, the graph has at most $rA$ vertices;
in particular $f$ free bits give the bound $r2^f$.
-/

namespace Lax323828.CliqueCorrespondence

open LocalTests ConsistencyGraph

axiom completeness {r m : ℕ} (C : System r m) (π : Oracle m) :
  ∃ s : Finset (Vertex C), (graph C).IsClique s ∧ s.card = (C.acceptedSeeds π).card

axiom soundness {r m : ℕ} (C : System r m) (s : Finset (Vertex C))
    (hs : (graph C).IsClique s) :
  ∃ π : Oracle m, s.card ≤ (C.acceptedSeeds π).card

axiom cliqueNumber_eq_optimum {r m : ℕ} (C : System r m) :
  (graph C).cliqueNum = C.optimum

axiom vertex_count {r m : ℕ} (C : System r m) :
  Fintype.card (Vertex C) = ∑ seed, (C.accepting seed).card

axiom vertex_bound {r m : ℕ} (C : System r m) (A : ℕ)
    (hA : ∀ seed, (C.accepting seed).card ≤ A) :
  Fintype.card (Vertex C) ≤ r * A

axiom perfect_completeness {r m : ℕ} (C : System r m)
    (h : ∃ π : Oracle m, ∀ seed, seed ∈ C.acceptedSeeds π) :
  (graph C).cliqueNum = r

axiom soundness_bound {r m : ℕ} (C : System r m) (s : ℕ)
    (h : ∀ π : Oracle m, (C.acceptedSeeds π).card ≤ s) :
  (graph C).cliqueNum ≤ s

end Lax323828.CliqueCorrespondence
