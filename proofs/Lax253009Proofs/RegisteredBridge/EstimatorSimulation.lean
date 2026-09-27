import Lax253009Proofs.RegisteredBridge.TM2Functions
import Lax253009Proofs.PCPFoundation.Classes.P.NatCodes
import Lax253009.Approximation

namespace Lax253009Proofs.RegisteredBridge

open PCPFoundation PCPFoundation.Complexity

theorem from_bits_encode_positive (n : PosNum) :
    BinaryNat.fromBitsLE (Computability.encodePosNum n) = (n : ℕ) := by
  induction n with
  | one => simp [Computability.encodePosNum, BinaryNat.fromBitsLE, BinaryNat.fromBits]
  | bit0 n ih =>
    simp [Computability.encodePosNum, BinaryNat.fromBitsLE_cons, ih, PosNum.cast_bit0]
    omega
  | bit1 n ih =>
    simp [Computability.encodePosNum, BinaryNat.fromBitsLE_cons, ih, PosNum.cast_bit1]
    omega

theorem from_bits_encode_num (n : Num) :
    BinaryNat.fromBitsLE (Computability.encodeNum n) = (n : ℕ) := by
  cases n with
  | zero => rfl
  | pos n => exact from_bits_encode_positive n

@[simp] theorem from_bits_encode_nat (n : ℕ) :
    BinaryNat.fromBitsLE (Computability.encodeNat n) = n := by
  simpa only [Computability.encodeNat, Num.to_of_nat] using from_bits_encode_num (n : Num)

/-- Comparing a registered polynomial-time integer estimator with a polynomial-time
threshold is a polynomial-time predicate, even when the integer itself is large. -/
theorem estimator_comparison {estimate : List Bool → ℕ}
    (M : Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate)
    {threshold : List Bool → ℕ} (hthreshold : UnaryFn threshold) :
    FPPred fun z ↦ threshold z < estimate z := by
  have henc := encoded_mem_FP M
  have hcap := hthreshold.add (UnaryFn.const 1)
  have hval := UnaryFn.fromBitsLE_min henc hcap
  have h := FPPred.lt hthreshold hval
  apply h.of_iff
  intro z
  simp only [from_bits_encode_nat, lt_min_iff, Nat.lt_succ_self, and_true]

theorem approximable_estimator_comparison {ε : ℝ}
    (h : Lax253009.Approximation.Approximable ε) :
    ∃ estimate : List Bool → ℕ,
      (∀ (n : ℕ), 0 < n → ∀ G : Lax253009.Graphs.Graph n,
        estimate G.encode ≤ G.cliqueNumber ∧
        (G.cliqueNumber : ℝ) ≤ Real.rpow (n : ℝ) (1 - ε) * (estimate G.encode : ℝ)) ∧
      ∀ {threshold : List Bool → ℕ}, UnaryFn threshold →
        FPPred (fun z ↦ threshold z < estimate z) := by
  obtain ⟨estimate, ⟨M⟩, hM⟩ := h
  exact ⟨estimate, hM, fun {threshold} hthreshold ↦ estimator_comparison M hthreshold⟩

end Lax253009Proofs.RegisteredBridge
