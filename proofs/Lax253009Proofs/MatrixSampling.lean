import Lax253009Proofs.FreshBitSampling
import Lax253009Proofs.SlotGraph

namespace Lax253009Proofs.MatrixSampling

open Lax253009 FreshBitSampling FiniteProbability LocalTests TestSampling TestRepetition
open RandomizedReduction SamplingParameters

/-- Group separately sampled base seeds into repeated seeds. The arbitrary
repeated-seed numbering is used only to compare finite probability spaces. -/
noncomputable def groupEquiv (N r k : ℕ) :
    (Fin (N * k) → Fin r) ≃ (Fin N → Fin (r ^ k)) :=
  (((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl (Fin r))).trans
    (Equiv.curry _ _ _)).trans
    (Equiv.piCongrRight (fun _ : Fin N ↦ seedEquiv r k)))

def sample {N r k : ℕ} (hr : 0 < r)
    (coins : Fin (N * k * bitsPerDraw (N * k) r) → Bool) : Fin N → Fin k → Fin r :=
  fun i j ↦ sampleFlat hr coins (finProdFinEquiv (i, j))

/-- Sampling each of the N*k base seeds gives the same total error allowance,
while every arithmetic modulus remains the polynomial-sized base seed count. -/
theorem one_third {N r k : ℕ} (hN : 0 < N) (hk : 0 < k) (hr : 0 < r)
    (P : (Fin N → Fin (r ^ k)) → Prop) (hP : probability P ≤ 1 / 4) :
    probability (fun coins : Fin (N * k * bitsPerDraw (N * k) r) → Bool ↦
      P (fun i ↦ seedEquiv r k (sample hr coins i))) ≤ 1 / 3 := by
  have he := finite_probability_equiv (groupEquiv N r k)
    (fun z ↦ P (groupEquiv N r k z)) P (fun _ ↦ Iff.rfl)
  have hh := fresh_flat_one_third_error (Nat.mul_pos hN hk) hr
    (fun z ↦ P (groupEquiv N r k z)) (he ▸ hP)
  exact hh

theorem slot_bad_event {r m A N k : ℕ} (hr : 0 < r) (hN : 0 < N) (hk : 0 < k)
    (C : LocalTests.System r m) (E : SlotGraph.Enumeration C A) (a : ℕ) (ha : 1 < a)
    (hP : probability (fun z : Fin N → Fin (r ^ k) ↦
      a ≤ (EncodedReduction.output (sampled (repeated C k) z)).cliqueNumber) ≤ 1 / 4) :
    probability (fun coins : Fin (N * k * bitsPerDraw (N * k) r) → Bool ↦
      a ≤ (SlotGraph.output (SlotGraph.sampledRepetition E k N (sample hr coins))).cliqueNumber) ≤
        1 / 3 := by
  apply le_trans (finite_probability_mono _ _ ?_) (one_third hN hk hr _ hP)
  intro coins hc
  have hbound := (SlotGraph.optimum_bounds (SlotGraph.sampledRepetition E k N (sample hr coins))).2
  rw [reduction_cliqueNumber]
  omega

end Lax253009Proofs.MatrixSampling
