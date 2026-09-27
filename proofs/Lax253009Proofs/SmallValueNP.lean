import Lax253009.SmallValueNP
import Lax253009Proofs.RegisteredBridge.RegisteredNP
import Lax253009Proofs.SmallValueSatisfiability

namespace Lax253009Proofs

open Lax253009 Lax253009.CenteredProjection Lax253009.GapSatisfiability
open PCPFoundation.Complexity

namespace RegisteredBridge

def plainFormula (φ : SAT.CNF) : Formula := φ.map (List.map fun l ↦ (l.sign, l.var))

@[simp] theorem plain_formula_length (φ : SAT.CNF) : (plainFormula φ).length = φ.length :=
  List.length_map _

theorem plain_formula_three (φ : SAT.CNF) (h : φ.Is3CNF) : Is3CNF (plainFormula φ) := by
  simpa [plainFormula, Is3CNF, SAT.CNF.Is3CNF] using h

theorem plain_formula_satisfiable (φ : SAT.CNF) :
    Satisfiable (plainFormula φ) ↔ φ.Satisfiable := by
  have h := (GapBridge.formula_satisfiable (plainFormula φ)).symm
  simpa [GapBridge.formula, plainFormula, List.map_map, Function.comp_def] using h

end RegisteredBridge

/--
---
conclusion: Lax253009.SmallValueNP.reduction
---
The explicit registered-machine simulation supplies Cook–Levin, and the
fixed-alphabet soundness amplifier preserves a polynomial bound in input length.
-/
theorem small_value_np (δ : ℝ) (hδ : 0 < δ) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧
      ∀ L ∈ Lax434930.NondeterministicPolynomialTime.NP, ∃ K e : ℕ,
        ∀ z : List Bool,
          ∃ u o w : ℕ, 0 < u ∧ 0 < o ∧ 0 < w ∧ u + o + w ≤ K * (z.length + 1) ^ e ∧
            ∃ G : System (Fin u) (Fin o) (Fin w) (Fin x) (Fin y),
              (z ∈ L → G.Complete) ∧ (z ∉ L → G.Sound δ) := by
  obtain ⟨x, y, K, e, hx, hy, hred⟩ := small_value_satisfiability δ hδ
  refine ⟨x, y, hx, hy, ?_⟩
  intro L hL
  obtain ⟨E, Φ, hEfp, hE, h3, hchar⟩ := RegisteredBridge.registered_exists_reduction_cnf hL
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hEfp
  obtain ⟨C, d, hC⟩ := (PolyBound.eval p).exists_mul_pow_bound
  refine ⟨K * (C + 1) ^ e, d * e, ?_⟩
  intro z
  obtain ⟨u, o, w, hu, ho, hw, hsize, G, hyes, hno⟩ :=
    hred (RegisteredBridge.plainFormula (Φ z)) (RegisteredBridge.plain_formula_three (Φ z) (h3 z))
  refine ⟨u, o, w, hu, ho, hw, ?_, G, ?_, ?_⟩
  · have h1 := length_le_length_encode (Φ z)
    have h2 := (hp z).trans (hC z.length)
    rw [hE z] at h2
    have hpow : 1 ≤ (z.length + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    have hlen : (RegisteredBridge.plainFormula (Φ z)).length + 1 ≤
        (C + 1) * (z.length + 1) ^ d := by
      rw [RegisteredBridge.plain_formula_length]
      nlinarith
    refine hsize.trans ((Nat.mul_le_mul_left K (Nat.pow_le_pow_left hlen e)).trans_eq ?_)
    simp only [mul_pow, pow_mul, mul_assoc]
  · intro hz
    exact hyes ((RegisteredBridge.plain_formula_satisfiable (Φ z)).mpr ((hchar z).mp hz))
  · intro hz
    apply hno
    intro hs
    exact hz ((hchar z).mpr ((RegisteredBridge.plain_formula_satisfiable (Φ z)).mp hs))

end Lax253009Proofs
