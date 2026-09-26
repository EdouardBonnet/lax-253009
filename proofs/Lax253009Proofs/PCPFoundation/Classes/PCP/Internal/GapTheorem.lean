/- Adapted for lax-253009 from complexitylib commit
5a1696fdd3bff26a5e7197f3333e8bef50ea146a. Imports, module directives,
and compatibility details are modified for Lean 4.33.
The original copyright and Apache-2.0 license remain applicable;
see LICENSES/complexitylib-Apache-2.0.txt at the submission root. -/
/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Lax253009Proofs.PCPFoundation.Classes.PCP.Internal.Dinur
import Lax253009Proofs.PCPFoundation.Classes.PCP.Internal.ExpanderExists
import Lax253009Proofs.PCPFoundation.Classes.PCP.Internal.FamilyFin
import Lax253009Proofs.PCPFoundation.Classes.PCP.Internal.GapReduction
import Mathlib.Tactic.IrreducibleDef

/-!
# Dinur's gap theorem for 3-SAT

The mathematical conclusion of the development. Every 3CNF formula is turned
into a constraint graph over a fixed constant-size alphabet, of size polynomial
in the formula, which is satisfiable when the formula is and whose
unsatisfiability value is at least a universal constant when it is not.

Three ingredients meet: the reduction of `ThreeSATCSP` carried across alphabets
by `GapReduction`, the explicit expander family `algFamily` of `FamilyFin` (a
numbered tower over a constant-size base picked once by
`Classical.choose exists_finBase`), and the amplifier of `Dinur`, whose
`dichotomy` supplies the gap after logarithmically many rounds.

This module states the gap theorem as a reduction in the mathematical sense:
`gapGraph` is a `noncomputable` definition and no running time is claimed here.
The upstream polynomial-time implementation is not part of this port.
This module supplies the finite mathematical gap construction only.

## Main definitions

- `Lax253009Proofs.PCPFoundation.Complexity.dinurAmp` — Dinur's amplifier, with the expander supplied
- `Lax253009Proofs.PCPFoundation.Complexity.gapGraph` — the gap graph of a formula

## Main results

- `Lax253009Proofs.PCPFoundation.Complexity.satisfiable_gapGraph` — completeness
- `Lax253009Proofs.PCPFoundation.Complexity.gap_le_unsatVal_gapGraph` — soundness, with a universal gap
- `Lax253009Proofs.PCPFoundation.Complexity.numEdges_gapGraph_le` — the size bound
-/

namespace Lax253009Proofs.PCPFoundation.Complexity

open ThreeSATCSP SAT

/-- Dinur's amplifier, with the expander family supplied. -/
noncomputable irreducible_def dinurAmp : Amplifier DinurAlpha := Dinur.amplifier algFamily

/-- How many rounds of amplification a formula needs: enough that the doubling
of the unsatisfiability value reaches the threshold, which is the bit length of
the edge count. -/
def gapRounds (φ : CNF) : ℕ := Nat.log 2 (3 * φ.length) + 1

theorem numEdges_baseCSP_le_pow_rounds (φ : CNF) :
    (baseCSP φ).numEdges ≤ 2 ^ gapRounds φ := by
  rw [numEdges_baseCSP, gapRounds]
  exact Nat.le_of_lt (Nat.lt_pow_succ_log_self (by omega) _)

/-- **The gap graph** of a formula: logarithmically many rounds of amplification
applied to its constraint graph. -/
noncomputable def gapGraph (φ : CNF) : ConstraintGraph DinurAlpha :=
  dinurAmp.iter (gapRounds φ) (baseCSP φ)

/-- **Completeness.** -/
theorem satisfiable_gapGraph {φ : CNF} (h3 : φ.Is3CNF) (h : φ.Satisfiable) :
    (gapGraph φ).Satisfiable :=
  (Amplifier.dichotomy dinurAmp (baseCSP φ) (numEdges_baseCSP_le_pow_rounds φ)).1
    ((satisfiable_baseCSP_iff h3).2 h)

/-- **Soundness**, with a gap that does not depend on the formula. -/
theorem gap_le_unsatVal_gapGraph {φ : CNF} (h3 : φ.Is3CNF) (h : ¬ φ.Satisfiable) :
    dinurAmp.gap ≤ (gapGraph φ).unsatVal :=
  (Amplifier.dichotomy dinurAmp (baseCSP φ) (numEdges_baseCSP_le_pow_rounds φ)).2
    fun hs => h ((satisfiable_baseCSP_iff h3).1 hs)

/-- The gap is a positive constant. -/
theorem dinurAmp_gap_pos : 0 < dinurAmp.gap := dinurAmp.gap_pos

/-- The gap is at most one, as any unsatisfiability value is. -/
theorem dinurAmp_gap_le_one : dinurAmp.gap ≤ 1 := dinurAmp.gap_le_one

/-- A bit length costs at most a doubling. -/
theorem two_pow_log_succ_le (n : ℕ) : 2 ^ (Nat.log 2 n + 1) ≤ 2 * n + 2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · have hlow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    omega

private theorem pow_pow_comm (a b c : ℕ) : (a ^ b) ^ c = (a ^ c) ^ b := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

private theorem pow_rounds_le (E m : ℕ) :
    E ^ (Nat.log 2 m + 1) ≤ (2 * m + 2) ^ (Nat.log 2 E + 1) := by
  calc E ^ (Nat.log 2 m + 1)
      ≤ (2 ^ (Nat.log 2 E + 1)) ^ (Nat.log 2 m + 1) :=
        Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by omega) _)) _
    _ = (2 ^ (Nat.log 2 m + 1)) ^ (Nat.log 2 E + 1) := pow_pow_comm 2 _ _
    _ ≤ (2 * m + 2) ^ (Nat.log 2 E + 1) :=
        Nat.pow_le_pow_left (two_pow_log_succ_le _) _

/-- **The size bound**: a constant factor per round, and logarithmically many
rounds, so polynomially many edges. -/
theorem numEdges_gapGraph_le (φ : CNF) :
    (gapGraph φ).numEdges
      ≤ (2 * (3 * φ.length) + 2) ^ (Nat.log 2 dinurAmp.edgeFactor + 1)
        * (3 * φ.length) := by
  have h := Amplifier.numEdges_iter_le dinurAmp (gapRounds φ) (baseCSP φ)
  rw [numEdges_baseCSP] at h
  exact le_trans h (Nat.mul_le_mul_right _ (pow_rounds_le _ _))

end Lax253009Proofs.PCPFoundation.Complexity
