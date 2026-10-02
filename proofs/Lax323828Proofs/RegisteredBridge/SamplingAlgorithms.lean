import Lax323828Proofs.RegisteredBridge.ComputableNumbering
import Lax323828Proofs.RegisteredBridge.EstimatorSimulation
import Lax323828Proofs.SamplingParameters
import Lax323828.FreshBitSampling

namespace Lax323828Proofs.RegisteredBridge.SamplingAlgorithms

open PCPFoundation.Complexity FiniteEncoding
open Lax323828.SamplingParameters Lax323828.FreshBitSampling

theorem fixed_power {f : List Bool → ℕ} (hf : UnaryFn f) (n : ℕ) :
    UnaryFn (fun z ↦ f z ^ n) := by
  induction n with
  | zero => simpa using UnaryFn.const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem repetitions_poly {m : List Bool → ℕ} (hm : UnaryFn m) (c : ℕ) :
    UnaryFn (fun z ↦ repetitions c (m z)) :=
  (UnaryFn.const c).mul (((UnaryFn.const 2).clog (hm.add (UnaryFn.const 2))).add (UnaryFn.const 3))

theorem repetition_power_poly {m : List Bool → ℕ} (hm : UnaryFn m) (c d : ℕ) :
    UnaryFn (fun z ↦ 2 ^ (d * repetitions c (m z))) := by
  apply UnaryFn.pow_of_le (UnaryFn.const 2) ((UnaryFn.const d).mul (repetitions_poly hm c))
    ((UnaryFn.const (16 ^ (d * c))).mul (fixed_power (hm.add (UnaryFn.const 2)) (d * c + 1)))
  intro z
  have hb := Lax323828.SamplingParameters.polynomial_bound 0 d c (m z)
  dsimp only [vertexBound] at hb
  simp only [Nat.add_zero] at hb
  have hmul : 2 ^ (d * repetitions c (m z)) ≤
      (m z + 2) * 2 ^ (d * repetitions c (m z)) :=
    Nat.le_mul_of_pos_left _ (by omega)
  exact hmul.trans hb

theorem sampleCount_poly {m : List Bool → ℕ} (hm : UnaryFn m) (c t : ℕ) :
    UnaryFn (fun z ↦ sampleCount t (repetitions c (m z)) (m z)) :=
  (hm.add (UnaryFn.const 2)).mul (repetition_power_poly hm c t)

theorem vertexBound_poly {m : List Bool → ℕ} (hm : UnaryFn m) (f t c : ℕ) :
    UnaryFn (fun z ↦ vertexBound f t (repetitions c (m z)) (m z)) :=
  (hm.add (UnaryFn.const 2)).mul (repetition_power_poly hm c (t + f))

theorem bitsPerDraw_poly {N r : List Bool → ℕ} (hN : UnaryFn N) (hr : UnaryFn r) :
    UnaryFn (fun z ↦ bitsPerDraw (N z) (r z)) :=
  (UnaryFn.const 2).clog (((UnaryFn.const 12).mul hN).mul hr)

theorem pow_clog_two_le (n : ℕ) : 2 ^ Nat.clog 2 n ≤ 2 * n + 1 := by
  by_cases hn : 1 < n
  · have hc := Nat.clog_pos (by norm_num : 1 < 2) hn
    have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hn
    have he : Nat.clog 2 n = (Nat.clog 2 n).pred + 1 :=
      (Nat.succ_pred_eq_of_pos hc).symm
    rw [he, pow_succ]
    omega
  · have hc : Nat.clog 2 n = 0 := Nat.eq_zero_of_le_zero
      (Nat.clog_le_of_le_pow (by simpa using (Nat.le_of_not_gt hn)))
    simp [hc]

theorem drawRange_poly {N r : List Bool → ℕ} (hN : UnaryFn N) (hr : UnaryFn r) :
    UnaryFn (fun z ↦ 2 ^ bitsPerDraw (N z) (r z)) := by
  apply UnaryFn.pow_of_le (UnaryFn.const 2) (bitsPerDraw_poly hN hr)
    (((UnaryFn.const 2).mul (((UnaryFn.const 12).mul hN).mul hr)).add (UnaryFn.const 1))
  intro z
  exact pow_clog_two_le _

theorem binary_value {b : ℕ} (c : Fin b → Bool) :
    (binaryEquiv b c).val = PCPFoundation.BinaryNat.fromBitsLE (List.ofFn c) := by
  induction b with
  | zero => simp [binaryEquiv, finFunctionFinEquiv_apply,
      PCPFoundation.BinaryNat.fromBitsLE, PCPFoundation.BinaryNat.fromBits]
  | succ b ih =>
    have ht := ih (Fin.tail c)
    change (∑ i : Fin (b + 1), (finTwoEquiv.symm (c i)).val * 2 ^ i.val) = _
    rw [List.ofFn_succ, PCPFoundation.BinaryNat.fromBitsLE_cons, Fin.sum_univ_succ]
    change (finTwoEquiv.symm (c 0)).val * 2 ^ 0 +
      (∑ i : Fin b, (finTwoEquiv.symm (c i.succ)).val * 2 ^ (i.val + 1)) = _
    have hs : (∑ i : Fin b, (finTwoEquiv.symm (c i.succ)).val * 2 ^ (i.val + 1)) =
        2 * PCPFoundation.BinaryNat.fromBitsLE (List.ofFn (Fin.tail c)) := by
      rw [← ht]
      change (∑ i : Fin b, (finTwoEquiv.symm (c i.succ)).val * 2 ^ (i.val + 1)) =
        2 * (∑ i : Fin b, (finTwoEquiv.symm (c i.succ)).val * 2 ^ i.val)
      simp only [pow_succ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    cases h : c 0 <;> simp [h, finTwoEquiv] <;> rfl

def draw (N r : ℕ) (coins : List Bool) (i : ℕ) : ℕ :=
  PCPFoundation.BinaryNat.fromBitsLE
    ((coins.drop (i * bitsPerDraw N r)).take (bitsPerDraw N r)) % r

theorem draw_poly {N r i : List Bool → ℕ} {coins : List Bool → List Bool}
    (hN : UnaryFn N) (hr : UnaryFn r) (hi : UnaryFn i) (hc : coins ∈ FP) :
    UnaryFn (fun z ↦ draw (N z) (r z) (coins z) (i z)) := by
  have hb := bitsPerDraw_poly hN hr
  have hd := dropLenFn_mem_FP (hi.mul hb).mem_FP hc
  have hs := Cobham.takeLenFn_mem_FP hb.mem_FP hd
  simp only [List.length_replicate] at hs
  have hval := UnaryFn.fromBitsLE_of_le hs (drawRange_poly hN hr) (fun z ↦ ?_)
  · exact hval.mod hr
  · exact (PCPFoundation.BinaryNat.fromBitsLE_lt_pow_length _).le.trans
      (Nat.pow_le_pow_right (by omega) (List.length_take_le _ _))

theorem block_eq {N b : ℕ} (coins : Fin (N * b) → Bool) (i : Fin N) :
    ((List.ofFn coins).drop (i.val * b)).take b =
      List.ofFn (fun j : Fin b ↦ coins (finProdFinEquiv (i, j))) := by
  have hbound := Nat.mul_le_mul_right b (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at hbound
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro j hj hj'
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    change i.val * b + j = j + b * i.val
    ring

/-- The concrete list algorithm is exactly the already-analyzed fair-bit
sampler, including its ordering of bits and draws. -/
theorem draw_eq_sample {N r : ℕ} (hr : 0 < r)
    (coins : Fin (N * bitsPerDraw N r) → Bool) (i : Fin N) :
    draw N r (List.ofFn coins) i.val = (sampleFlat hr coins i).val := by
  rw [draw, block_eq]
  change _ = (binaryEquiv (bitsPerDraw N r) (coinEquiv N (bitsPerDraw N r) coins i)).val % r
  rw [binary_value]
  rfl

end Lax323828Proofs.RegisteredBridge.SamplingAlgorithms
