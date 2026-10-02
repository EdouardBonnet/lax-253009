import Lax323828Proofs.FAFStrategyExtraction

namespace Lax323828Proofs

open Filter Lax323828.FAFStrategyExtraction
open scoped Topology

private theorem pow_pow_comm (a : ℝ) (m n : ℕ) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem faf_error_decay (n k q : ℕ) (a c d : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hfirst : a * d < 1) (hlow : a * (2 * c) ^ (n - k) < 1)
    (hhigh : a * (2 : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ (k + 1)) ^ q < 1) :
    Tendsto (fun s : ℕ ↦ a ^ s * errorBound n (2 ^ s) k (q * s) (c ^ s) (d ^ s))
      atTop (𝓝 0) := by
  have h₁ := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by positivity : 0 ≤ a * d) hfirst).const_mul (n : ℝ)
  have h₂ := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by positivity : 0 ≤ a * (2 * c) ^ (n - k)) hlow).const_mul
      ((2 : ℝ) ^ n * (n : ℝ) ^ (n - k))
  have h₃ := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by positivity : 0 ≤ a * (2 : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ (k + 1)) ^ q) hhigh
  have h := (h₁.add h₂).add h₃
  simp only [mul_zero, add_zero] at h
  apply h.congr
  intro s
  simp only [errorBound, Nat.cast_pow, Nat.cast_ofNat, mul_pow, pow_mul,
    pow_pow_comm (2 : ℝ) n s, pow_pow_comm (2 : ℝ) s (n - k), pow_pow_comm c s (n - k)]
  ring

theorem faf_paper_parameters (l : ℕ) (hl : 0 < l) :
    Tendsto (fun s : ℕ ↦ (2 : ℝ) ^ (20 * l * l * s) *
      errorBound (10 * l) (2 ^ s) (5 * l) (10 * l * s)
        ((1 / 2 : ℝ) ^ (20 * l * s)) ((1 / 2 : ℝ) ^ (40 * l * l * s)))
      atTop (𝓝 0) := by
  have hpow {a b : ℕ} (hab : a < b) : (2 : ℝ) ^ a / (2 : ℝ) ^ b < 1 := by
    rw [div_lt_one (by positivity)]
    exact pow_lt_pow_right₀ (by norm_num) hab
  have h₁ : (2 : ℝ) ^ (20 * l * l) * (1 / 2 : ℝ) ^ (40 * l * l) < 1 := by
    simp only [div_pow, one_pow, mul_one_div]
    apply hpow
    nlinarith [Nat.mul_pos hl hl]
  have h₂ : (2 : ℝ) ^ (20 * l * l) * (2 * (1 / 2 : ℝ) ^ (20 * l)) ^ (10 * l - 5 * l) < 1 := by
    have hsub : 10 * l - 5 * l = 5 * l := by omega
    rw [hsub, mul_pow, div_pow, one_pow, div_pow, one_pow, ← pow_mul]
    simp only [mul_one, ← mul_div_assoc, ← pow_add]
    apply hpow
    nlinarith [Nat.mul_pos hl hl]
  have h₃ : (2 : ℝ) ^ (20 * l * l) * (2 : ℝ) ^ (10 * l) *
      (2 * (1 / 2 : ℝ) ^ (5 * l + 1)) ^ (10 * l) < 1 := by
    rw [mul_pow, div_pow, one_pow, div_pow, one_pow, ← pow_mul]
    simp only [mul_one, ← mul_div_assoc, ← pow_add]
    apply hpow
    nlinarith [Nat.mul_pos hl hl]
  have h := faf_error_decay (10 * l) (5 * l) (10 * l)
    ((2 : ℝ) ^ (20 * l * l)) ((1 / 2 : ℝ) ^ (20 * l)) ((1 / 2 : ℝ) ^ (40 * l * l))
    (by positivity) (by positivity) (by positivity) h₁ h₂ h₃
  simpa only [pow_mul] using h

theorem faf_parameter_bounds (l : ℕ) (hl : 0 < l) :
    ∀ᶠ s : ℕ in atTop,
      (10 * l : ℕ) * (2 : ℝ) ^ s * (1 / 2 : ℝ) ^ (20 * l * s) ≤ 1 ∧
      errorBound (10 * l) (2 ^ s) (5 * l) (10 * l * s)
        ((1 / 2 : ℝ) ^ (20 * l * s)) ((1 / 2 : ℝ) ^ (40 * l * l * s)) ≤
        (1 / 2 : ℝ) ^ (20 * l * l * s) / 2 := by
  have hc : 2 * (1 / 2 : ℝ) ^ (20 * l) < 1 := by
    rw [div_pow, one_pow, mul_one_div, div_lt_one (by positivity)]
    simpa only [pow_one] using (show (2 : ℝ) ^ 1 < (2 : ℝ) ^ (20 * l) from
      pow_lt_pow_right₀ (by norm_num) (by omega))
  have hsmall := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hc).const_mul ((10 * l : ℕ) : ℝ)
  simp only [mul_zero] at hsmall
  filter_upwards [hsmall.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    (faf_paper_parameters l hl).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)] with s hs he
  constructor
  · simpa only [mul_pow, ← pow_mul, mul_assoc] using hs
  · have hpos : (0 : ℝ) < (2 : ℝ) ^ (20 * l * l * s) := by positivity
    calc
      _ ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ (20 * l * l * s) :=
        (le_div_iff₀ hpos).mpr (by nlinarith [he])
      _ = _ := by rw [div_pow, one_pow]; ring

theorem dyadic_negative_rpow (a b : ℕ) :
    Real.rpow 2 (-(a : ℝ) * (b : ℝ)) = (1 / 2 : ℝ) ^ (a * b) := by
  change (2 : ℝ) ^ (-(a : ℝ) * (b : ℝ)) = _
  rw [show -(a : ℝ) * (b : ℝ) = -((a * b : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg (by norm_num), Real.rpow_natCast]
  simp only [one_div, inv_pow]

end Lax323828Proofs
