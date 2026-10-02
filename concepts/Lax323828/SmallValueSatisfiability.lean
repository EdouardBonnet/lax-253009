import Lax323828.Amplification
import Lax323828.GapSatisfiability

/-!
---
title: A polynomial-size 3-SAT reduction to arbitrarily small projection-game value
type: theorem
---
For every fixed positive soundness δ, exact 3-CNF formulas reduce to centered
projection games over fixed answer alphabets. Satisfiable formulas give
perfectly complete games, and unsatisfiable formulas give value at most δ.
The sum of all three question-space sizes is bounded by one fixed polynomial
in the number of clauses.

This combines the regular Dinur gap, projection symmetrization, tuple
fortification, repeated squaring, and Cauchy–Schwarz. It is a finite
mathematical reduction; the uniform machine running-time proof is separate.
-/

namespace Lax323828.SmallValueSatisfiability

open CenteredProjection GapSatisfiability

axiom reduction (δ : ℝ) (hδ : 0 < δ) :
    ∃ x y K e : ℕ, 0 < x ∧ 0 < y ∧
      ∀ φ : Formula, Is3CNF φ →
        ∃ u o w : ℕ, 0 < u ∧ 0 < o ∧ 0 < w ∧ u + o + w ≤ K * (φ.length + 1) ^ e ∧
          ∃ G : System (Fin u) (Fin o) (Fin w) (Fin x) (Fin y),
            (Satisfiable φ → G.Complete) ∧ (¬ Satisfiable φ → G.Sound δ)

end Lax323828.SmallValueSatisfiability
