import Lax253009.SmallValueSatisfiability
import Lax434930.NondeterministicPolynomialTime

/-!
---
title: Small-value projection games for every registered NP language
type: theorem
---
Every language in the registered certificate definition of NP has a
polynomial-size reduction to projection games of arbitrarily small positive
value. The answer alphabets depend only on the target value. The polynomial
bound can depend on the language. Completeness is perfect.

The proof connects the registered stack-machine verifiers to Cook–Levin,
then applies the proved finite gap and fortification construction. This
statement records semantic correctness and size; the machine implementation
of the complete game transformation is a separate obligation.
-/

namespace Lax253009.SmallValueNP

open CenteredProjection

axiom reduction (δ : ℝ) (hδ : 0 < δ) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧
      ∀ L ∈ Lax434930.NondeterministicPolynomialTime.NP, ∃ K e : ℕ,
        ∀ z : List Bool,
          ∃ u o w : ℕ, 0 < u ∧ 0 < o ∧ 0 < w ∧ u + o + w ≤ K * (z.length + 1) ^ e ∧
            ∃ G : System (Fin u) (Fin o) (Fin w) (Fin x) (Fin y),
              (z ∈ L → G.Complete) ∧ (z ∉ L → G.Sound δ)

end Lax253009.SmallValueNP
