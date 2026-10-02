import Lax323828.SamplingParameters
import Mathlib.Tactic

namespace Lax323828Proofs

open Lax323828.SamplingParameters

private theorem pow_clog_upper (m : ℕ) : 2 ^ Nat.clog 2 (m + 2) ≤ 2 * (m + 2) := by
  have hc : 0 < Nat.clog 2 (m + 2) := Nat.clog_pos (by norm_num) (by omega)
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := m + 2) (by omega)
  calc
    _ = 2 ^ (Nat.clog 2 (m + 2) - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hc]
    _ ≤ (m + 2) * 2 := Nat.mul_le_mul_right 2 h.le
    _ = _ := by omega

private theorem sampling_scale_upper (m : ℕ) :
    2 ^ (Nat.clog 2 (m + 2) + 3) ≤ 16 * (m + 2) := by
  rw [pow_add]
  have h := pow_clog_upper m
  norm_num
  omega

private theorem sampling_scale_lower (m : ℕ) :
    4 * (m + 2) < 2 ^ (Nat.clog 2 (m + 2) + 3) := by
  have h := Nat.le_pow_clog (b := 2) (by norm_num) (m + 2)
  rw [pow_add]
  norm_num
  omega

/--
---
conclusion: Lax323828.SamplingParameters.polynomial_bound
---
The rounded binary logarithm loses at most a factor two. Raising its
exponential to the fixed power (t+f)c gives an explicit polynomial bound.
-/
theorem sampling_polynomial_bound (f t c m : ℕ) :
    vertexBound f t (repetitions c m) m ≤
      16 ^ ((t + f) * c) * (m + 2) ^ ((t + f) * c + 1) := by
  unfold vertexBound repetitions
  rw [show (t + f) * (c * (Nat.clog 2 (m + 2) + 3)) =
    (Nat.clog 2 (m + 2) + 3) * ((t + f) * c) by ring, pow_mul]
  calc
    _ ≤ (m + 2) * (16 * (m + 2)) ^ ((t + f) * c) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (sampling_scale_upper m) _)
    _ = _ := by rw [mul_pow, pow_succ]; ring

/--
---
conclusion: Lax323828.SamplingParameters.approximation_gap
---
The margin in the exponential dominates 4(m+2). The remaining exponent
is exactly the contribution of the graph-size approximation factor.
-/
theorem sampling_approximation_gap (ε : ℝ) (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (f t c : ℕ) (hmargin : 1 ≤ (c : ℝ) * ((t : ℝ) * ε - (f : ℝ) * (1 - ε))) (m : ℕ) :
    Real.rpow (vertexBound f t (repetitions c m) m : ℝ) (1 - ε) * threshold m <
      sampleCount t (repetitions c m) m := by
  let L := Nat.clog 2 (m + 2) + 3
  let δ : ℝ := (t : ℝ) * ε - (f : ℝ) * (1 - ε)
  have hL : (L : ℝ) ≤ (repetitions c m : ℝ) * δ := by
    have h := mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    simpa [repetitions, L, δ, mul_assoc, mul_comm, mul_left_comm] using h
  have hscale : 4 * ((m : ℝ) + 2) < (2 : ℝ) ^ ((repetitions c m : ℝ) * δ) := by
    calc
      _ < (2 : ℝ) ^ L := by exact_mod_cast sampling_scale_lower m
      _ = (2 : ℝ) ^ (L : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hL
  have hB : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hBpow : ((m : ℝ) + 2) ^ (1 - ε) ≤ (m : ℝ) + 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ (m : ℝ) + 2 by have := Nat.cast_nonneg (α := ℝ) m; linarith)
      (show 1 - ε ≤ 1 by linarith)
  have hsmall : 4 * ((m : ℝ) + 2) ^ (1 - ε) <
      (2 : ℝ) ^ ((repetitions c m : ℝ) * δ) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hBpow (by norm_num)) hscale
  have hpositive : 0 < ((m : ℝ) + 2) *
      (2 : ℝ) ^ (((t : ℝ) + f) * repetitions c m * (1 - ε)) := by positivity
  have h := mul_lt_mul_of_pos_right hsmall hpositive
  have he : (repetitions c m : ℝ) * δ +
      ((t : ℝ) + f) * repetitions c m * (1 - ε) = (t : ℝ) * repetitions c m := by
    dsimp [δ]
    ring
  unfold vertexBound threshold sampleCount
  push_cast
  change (((m : ℝ) + 2) * (2 : ℝ) ^ ((t + f) * repetitions c m)) ^ (1 - ε) *
    (4 * ((m : ℝ) + 2)) < ((m : ℝ) + 2) * (2 : ℝ) ^ (t * repetitions c m)
  have hexp : ((2 : ℝ) ^ ((t + f) * repetitions c m)) ^ (1 - ε) =
      (2 : ℝ) ^ (((t : ℝ) + f) * repetitions c m * (1 - ε)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast
    rfl
  rw [Real.mul_rpow hB.le (by positivity), hexp]
  calc
    _ = 4 * ((m : ℝ) + 2) ^ (1 - ε) *
        (((m : ℝ) + 2) * (2 : ℝ) ^ (((t : ℝ) + f) * repetitions c m * (1 - ε))) := by ring
    _ < (2 : ℝ) ^ ((repetitions c m : ℝ) * δ) *
        (((m : ℝ) + 2) * (2 : ℝ) ^ (((t : ℝ) + f) * repetitions c m * (1 - ε))) := h
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), he,
        ← Real.rpow_natCast (2 : ℝ) (t * repetitions c m), Nat.cast_mul]

/--
---
conclusion: Lax323828.SamplingParameters.choose_multiplier
---
An integer strictly larger than the reciprocal of the positive margin
works for every input length.
-/
theorem sampling_choose_multiplier (ε : ℝ) (f t : ℕ)
    (hmargin : 0 < (t : ℝ) * ε - (f : ℝ) * (1 - ε)) :
    ∃ c : ℕ, 0 < c ∧ 1 ≤ (c : ℝ) * ((t : ℝ) * ε - (f : ℝ) * (1 - ε)) := by
  obtain ⟨c, hc⟩ := exists_nat_gt (1 / ((t : ℝ) * ε - (f : ℝ) * (1 - ε)))
  have hcpos : (0 : ℝ) < c := (div_pos (by norm_num) hmargin).trans hc
  refine ⟨c, by exact_mod_cast hcpos, ?_⟩
  exact ((div_lt_iff₀ hmargin).mp hc).le

end Lax323828Proofs
