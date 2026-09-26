import Lax253009.EncodedReduction
import Lax253009Proofs.ConsistencyGraph
import Lax253009Proofs.GraphEncoding

namespace Lax253009Proofs

open Lax253009 Lax253009.LocalTests Lax253009.ConsistencyGraph
open Lax253009.EncodedReduction Lax434930.PolynomialTime

/--
---
conclusion: Lax253009.EncodedReduction.cliqueNumber_output
---
Compose the consistency-graph correspondence with invariance under numbering.
-/
theorem reduction_cliqueNumber {r m : ℕ} (C : System r m) :
    (output C).cliqueNumber = C.optimum := by
  rw [output, numbered_cliqueNumber, consistency_cliqueNumber]

/--
---
conclusion: Lax253009.EncodedReduction.approximation_separates
---
On low-optimum instances the estimator is at most a. On high-optimum
instances an output at most a would contradict the strict multiplicative gap.
-/
theorem reduction_separates (ε : ℝ) (hε : Approximation.Approximable ε) :
    ∃ estimate : Word → ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate) ∧
      ∀ (r m : ℕ) (C : System r m), 0 < Fintype.card (Vertex C) →
        ∀ a b : ℕ,
          Real.rpow (Fintype.card (Vertex C) : ℝ) (1 - ε) * (a : ℝ) < (b : ℝ) →
          (C.optimum ≤ a → estimate (output C).encode ≤ a) ∧
          (b ≤ C.optimum → a < estimate (output C).encode) := by
  obtain ⟨estimate, hpoly, happrox⟩ := hε
  refine ⟨estimate, hpoly, fun r m C hN a b hgap ↦ ?_⟩
  obtain ⟨hlower, hupper⟩ := happrox _ hN (output C)
  rw [reduction_cliqueNumber] at hlower hupper
  refine ⟨fun hlow ↦ hlower.trans hlow, fun hhigh ↦ ?_⟩
  by_contra hnot
  have hle : estimate (output C).encode ≤ a := Nat.le_of_not_gt hnot
  have hleR : (estimate (output C).encode : ℝ) ≤ (a : ℝ) := by exact_mod_cast hle
  have hhighR : (b : ℝ) ≤ (C.optimum : ℝ) := by exact_mod_cast hhigh
  have hmul := mul_le_mul_of_nonneg_left hleR
    (Real.rpow_nonneg (show (0 : ℝ) ≤ Fintype.card (Vertex C) from Nat.cast_nonneg _) (1 - ε))
  exact (not_lt_of_ge (hhighR.trans (hupper.trans hmul))) hgap

end Lax253009Proofs
