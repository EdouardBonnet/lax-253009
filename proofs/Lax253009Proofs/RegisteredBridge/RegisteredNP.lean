import Lax253009Proofs.RegisteredBridge.TM2InputOutput
import Lax434930.NondeterministicPolynomialTime
import Lax253009Proofs.PCPFoundation.Classes.NP.WitnessConstruction
import Lax253009Proofs.PCPFoundation.Classes.PCP.Internal.AlgFormula

namespace Lax253009Proofs.RegisteredBridge

open PCPFoundation.Complexity PCPFoundation.Complexity.SAT

theorem registered_pair_eq (x y : List Bool) :
    Lax434930.Certificates.pair x y = x.flatMap (fun b ↦ [false, b]) ++ true :: y := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [Lax434930.Certificates.pair, ih]

theorem registered_pair_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z ↦ Lax434930.Certificates.pair (a z) (b z)) ∈ FP := by
  simp_rw [registered_pair_eq]
  exact Cobham.appendFn_mem_FP
    (mem_FP_comp ha (FiniteEncoding.flatMap_mem_FP (fun bit ↦ [false, bit])))
    (Cobham.appendFn_mem_FP (constFn_mem_FP [true]) hb)

/-- The registered certificate definition of `NP` embeds in the machine model used for Cook–Levin. -/
theorem registered_NP_subset :
    Lax434930.NondeterministicPolynomialTime.NP ⊆ PCPFoundation.Complexity.NP := by
  intro L hL
  obtain ⟨V, hV, p, hchar⟩ := hL
  obtain ⟨ruler, hruler, hrlen⟩ := Cobham.exists_exact_ruler p
  have hlen : UnaryFn (fun z ↦ p.eval (pairFst z).length) :=
    (UnaryFn.length (mem_FP_comp pairFst_mem_FP hruler)).of_eq (fun z ↦ hrlen _)
  let V' : Language := {z | (pairSnd z).length ≤ p.eval (pairFst z).length ∧
    Lax434930.Certificates.pair (pairFst z) (pairSnd z) ∈ V}
  have hV' : V' ∈ PCPFoundation.Complexity.P :=
    ((FPPred.le (UnaryFn.length pairSnd_mem_FP) hlen).and
      ((registered_P_pred hV).comp (registered_pair_mem_FP pairFst_mem_FP pairSnd_mem_FP))).mem_P
  refine mem_NP_of_poly_witness p hV' ?_ ?_
  · intro x y hxy
    simpa only [V', Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair] using hxy.1
  · intro x
    simpa only [V', Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair] using hchar x

/-- Cook–Levin for the registered `NP`, with a polynomial-time formula encoding. -/
theorem registered_exists_reduction_cnf {L : Lax434930.PolynomialTime.Language}
    (hL : L ∈ Lax434930.NondeterministicPolynomialTime.NP) :
    ∃ (E : List Bool → List Bool) (Φ : List Bool → CNF), E ∈ FP
      ∧ (∀ x, E x = (Φ x).encode) ∧ (∀ x, (Φ x).Is3CNF)
      ∧ (∀ x, x ∈ L ↔ (Φ x).Satisfiable) :=
  exists_reduction_cnf (registered_NP_subset hL)

end Lax253009Proofs.RegisteredBridge
