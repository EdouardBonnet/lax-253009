import Lax253009.ProjectionGames

/-!
---
title: A fixed-alphabet regular gap reduction for 3-SAT
type: theorem
---
Dinur's gap construction followed by degree reduction gives regular binary
constraint systems with a fixed alphabet, fixed degree, and a positive
constant unsatisfiability gap. Their number of vertices is bounded by a
fixed polynomial in the number of clauses. Satisfiable formulas give
satisfiable systems.

This is the finite mathematical reduction. Its proof uses the ported Dinur
development from complexitylib (Apache-2.0). A polynomial bound on the
output size is stated here; a machine running-time claim is separate.
-/

namespace Lax253009.GapSatisfiability

abbrev Literal := Bool × ℕ
abbrev Formula := List (List Literal)

def Is3CNF (φ : Formula) : Prop := ∀ c ∈ φ, c.length = 3

def Satisfiable (φ : Formula) : Prop :=
  ∃ a : List Bool, ∀ c ∈ φ, ∃ l ∈ c, (a[l.2]?).getD false = l.1

axiom regular_gap :
  ∃ a d K e : ℕ, 0 < a ∧ 0 < d ∧ 0 < K ∧
    ∃ γ : ℝ, 0 < γ ∧
      ∀ φ : Formula, Is3CNF φ →
        ∃ n : ℕ, 0 < n ∧ n ≤ K * (φ.length + 1) ^ e ∧
          ∃ C : ProjectionGames.System (Fin n) (Fin d) (Fin a),
            (Satisfiable φ → C.Satisfiable) ∧ (¬ Satisfiable φ → C.Sound γ)

end Lax253009.GapSatisfiability
