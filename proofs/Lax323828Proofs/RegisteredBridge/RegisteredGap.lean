import Lax323828Proofs.RegisteredBridge.RegisteredNP
import Lax323828Proofs.PCPFoundation.Classes.PCP.Internal.AlgGapCSP
import Mathlib.Tactic

namespace Lax323828Proofs.RegisteredBridge

open PCPFoundation.Complexity PCPFoundation.Complexity.SAT

/-- A polynomial-time, nonempty gap-constraint family for every registered `NP` language. -/
theorem registered_gap_family (F : FinBase) (hd : 1 < F.deg)
    {L : Lax434930.PolynomialTime.Language}
    (hL : L ∈ Lax434930.NondeterministicPolynomialTime.NP) :
    ∃ (E : List Bool → List Bool) (G : List Bool → ConstraintGraph DinurAlpha),
      E ∈ FP ∧ (∀ x, E x = encGraph (G x)) ∧ (∀ x, 0 < (G x).numEdges) ∧
      (∀ x, x ∈ L → (G x).Satisfiable) ∧
      (∀ x, x ∉ L → (Dinur.amplifier (F.toFamily hd)).gap ≤ (G x).unsatVal) := by
  obtain ⟨E, Φ, hEfp, hE, h3, hchar⟩ := registered_exists_reduction_cnf hL
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hEfp
  let q : Polynomial ℕ := Polynomial.C 3 * p + Polynomial.C 1
  obtain ⟨R, hR, hRlen⟩ := Cobham.exists_exact_ruler q
  let pad : List Bool → List Bool := fun x ↦ List.replicate (R x).length true
  have hpad : pad ∈ FP := UnaryFn.length hR
  have hpadlen : ∀ x, (pad x).length = q.eval x.length := by
    intro x
    simpa only [pad, List.length_replicate] using hRlen x
  have hmark : ∀ x, pad x = List.replicate (pad x).length true := by
    intro x
    simp only [pad, List.length_replicate]
  have hle : ∀ x, 3 * (Φ x).length ≤ (pad x).length := by
    intro x
    have h1 := length_le_length_encode (Φ x)
    have h2 := hp x
    rw [hE x] at h2
    rw [hpadlen]
    simp only [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    omega
  have hpos : ∀ x, 0 < (pad x).length := by
    intro x
    rw [hpadlen]
    simp only [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    omega
  refine ⟨gapAll F hd E pad, gapAllG F hd pad (Φ := Φ),
    gapAll_mem_FP F hd E pad hEfp hpad hE h3 hmark hle p q hp hpadlen,
    gapAll_eq F hd E pad hE h3 hmark hle, ?_, ?_, ?_⟩
  · intro x
    rw [gapAllG, numEdges_iterStep, ConstraintGraph.numEdges_padGraph]
    exact Nat.mul_pos (pow_pos (one_le_edgeFactor F hd) _)
      ((hpos x).trans_le (Nat.le_max_left _ _))
  · intro x hx
    exact satisfiable_gapAllG F hd pad h3 hle x ((hchar x).mp hx)
  · intro x hx
    exact gap_le_unsatVal_gapAllG F hd pad h3 hle x (fun hs ↦ hx ((hchar x).mpr hs))

end Lax323828Proofs.RegisteredBridge
