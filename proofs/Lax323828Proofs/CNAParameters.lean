import Lax323828Proofs.CNAQuantitativeSoundness
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Lax323828Proofs

open Filter Lax323828.CNAPointSoundness Lax323828.CNAQuantitativeSoundness
open Lax323828.SmallCoefficientSoundness
open scoped Topology BigOperators

private theorem pow_pow_comm (a : ℝ) (m n : ℕ) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

private theorem geometric_double_exponential (a c : ℝ) (ha : 0 ≤ a) (hc : 1 < c) :
    Tendsto (fun s : ℕ ↦ a ^ s * Real.exp (-(c ^ s) / 2)) atTop (𝓝 0) := by
  obtain ⟨d, hd⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hc).eventually (eventually_gt_atTop a)).exists
  have he := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d : ℝ) (1 / 2)
    (by norm_num)).comp (tendsto_pow_atTop_atTop_of_one_lt hc)
  have he' : Tendsto (fun s : ℕ ↦ (c ^ s) ^ d * Real.exp (-(c ^ s) / 2)) atTop (𝓝 0) := by
    convert he using 1
    funext s
    simp only [Function.comp_apply, Real.rpow_natCast]
    congr 1
    congr 1
    ring
  apply squeeze_zero (fun _ ↦ mul_nonneg (pow_nonneg ha _) (Real.exp_pos _).le) _ he'
  intro s
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [pow_pow_comm c s d]
  exact pow_le_pow_left₀ ha hd.le s

private theorem scaled_correlation_decay (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun s : ℕ ↦ a ^ s *
      (2 * ((2 : ℝ) ^ s + 1) * Real.exp (-((2 : ℝ) ^ s) * (((3 : ℝ) / 4) ^ s) ^ 2 / 2)))
      atTop (𝓝 0) := by
  have h := ((geometric_double_exponential (2 * a) (9 / 8) (by positivity) (by norm_num)).add
    (geometric_double_exponential a (9 / 8) ha (by norm_num))).const_mul 2
  simp only [add_zero, mul_zero] at h
  apply h.congr
  intro s
  have he : (2 : ℝ) ^ s * (((3 : ℝ) / 4) ^ s) ^ 2 = ((9 : ℝ) / 8) ^ s := by
    rw [pow_pow_comm _ s 2, ← mul_pow]
    norm_num
  rw [neg_mul, he]
  rw [mul_pow]
  ring

theorem cna_point_bound_decay (a α : ℝ) (ha : 0 ≤ a) (hα : 0 ≤ α)
    (l m r : ℕ) (hl : a * ((3 : ℝ) / 4) ^ l < 1)
    (hr : a * ((3 : ℝ) / 4) ^ r < 1)
    (hm : ∀ t ∈ Finset.range r, a * α ^ (m - 2 * t) < 1) :
    Tendsto (fun s : ℕ ↦ a ^ s * pointBound l m r (2 ^ s) (α ^ s) (((3 : ℝ) / 4) ^ s))
      atTop (𝓝 0) := by
  have hpow (j : ℕ) (hj : a * ((3 : ℝ) / 4) ^ j < 1) :
      Tendsto (fun s : ℕ ↦ a ^ s * (((3 : ℝ) / 4) ^ s) ^ j) atTop (𝓝 0) := by
    simpa only [pow_pow_comm _ _ j, ← mul_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ a * ((3 : ℝ) / 4) ^ j) hj
  have hterm (t : ℕ) (ht : t ∈ Finset.range r) :
      Tendsto (fun s : ℕ ↦ a ^ s *
        ((2 : ℝ) ^ m * ((2 : ℝ) ^ t * α ^ s) ^ (m - 2 * t) *
          (1 + (3 : ℝ) ^ (l * (4 * t + 1) * 2 ^ (2 * t))))) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by positivity : 0 ≤ a * α ^ (m - 2 * t)) (hm t ht)).const_mul
        ((2 : ℝ) ^ m * ((2 : ℝ) ^ t) ^ (m - 2 * t) *
          (1 + (3 : ℝ) ^ (l * (4 * t + 1) * 2 ^ (2 * t))))
    simp only [mul_zero] at h
    apply h.congr
    intro s
    rw [mul_pow, mul_pow, pow_pow_comm α s (m - 2 * t)]
    ring
  have hsum := tendsto_finsetSum (Finset.range r) hterm
  simp only [Finset.sum_const_zero] at hsum
  have hfirst := ((hpow l hl).add (scaled_correlation_decay a ha)).const_mul 9
  have hlast := ((hpow r hr).add ((scaled_correlation_decay a ha).const_mul ((2 : ℝ) ^ m))).const_mul
    (1 + (3 : ℝ) ^ (l * (2 * m + 1) * 2 ^ m))
  have hall := hfirst.add ((hsum.add hlast).const_mul ((3 : ℝ) ^ m))
  simp only [add_zero, mul_zero] at hall
  apply hall.congr
  intro s
  simp only [pointBound, boundValue, Nat.cast_pow, Nat.cast_ofNat, mul_add, Finset.mul_sum]
  ring_nf

private theorem cna_large_term_decay (α : ℝ) (hα : 0 < α) (h2α : 1 < 2 * α) (l : ℕ) :
    Tendsto (fun s : ℕ ↦ (l : ℝ) / ((2 : ℝ) ^ s - l) / α ^ s) atTop (𝓝 0) := by
  have hbase : (2 * α)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr h2α
  have hnum := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by positivity : 0 ≤ (2 * α)⁻¹) hbase).const_mul (l : ℝ)
  have hden := (tendsto_const_nhds (x := (1 : ℝ))).sub
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).const_mul (l : ℝ))
  have h := hnum.div hden (by norm_num)
  simp only [mul_zero, sub_zero, zero_div] at h
  have hlt : ∀ᶠ s : ℕ in atTop, (l : ℝ) < (2 : ℝ) ^ s :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually (eventually_gt_atTop _)
  apply h.congr'
  filter_upwards [hlt] with s hs
  have hp : (2 : ℝ) ^ s ≠ 0 := by positivity
  have hap : α ^ s ≠ 0 := pow_ne_zero _ hα.ne'
  change (l : ℝ) * (2 * α)⁻¹ ^ s / (1 - l * (1 / 2) ^ s) = _
  rw [inv_pow, mul_pow, div_pow]
  field_simp
  ring

private theorem exists_cna_base (ε : ℝ) (hε : 0 < ε) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ 1 < 2 * α ∧ 1 < α ^ 2 * Real.rpow 2 ε := by
  let d := min ε 1 / 4
  have hd : 0 < d := by dsimp [d]; positivity
  have hdε : d ≤ ε / 4 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hd1 : d ≤ 1 / 4 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let α := Real.rpow 2 (-d)
  refine ⟨α, Real.rpow_pos_of_pos (by norm_num) _,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith), ?_, ?_⟩
  · have he : 2 * α = Real.rpow 2 (1 - d) := by
      change 2 * α = (2 : ℝ) ^ (1 - d)
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2) 1 (-d)]
      simp only [Real.rpow_one, α]
      rfl
    rw [he]
    exact Real.one_lt_rpow (by norm_num) (by linarith)
  · have he : α ^ 2 * Real.rpow 2 ε = Real.rpow 2 (ε - 2 * d) := by
      dsimp [α]
      rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_add (by norm_num)]
      congr 1
      norm_num
      ring
    rw [he]
    exact Real.one_lt_rpow (by norm_num) (by linarith)

theorem cna_parameter_choice (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ l m r : ℕ, ∃ α : ℝ, 0 < l ∧ 0 < α ∧ α ≤ 1 ∧ 2 * r ≤ m ∧ Even m ∧
      ∀ᶠ s : ℕ in atTop,
        0 < s ∧ l < 2 ^ s ∧
        (l : ℝ) / (α ^ s) ^ 2 ≤ Real.rpow 2 (ε * (s : ℝ)) ∧
        (l : ℝ) / ((2 : ℝ) ^ s - l) / α ^ s ≤ 1 / 3 ∧
        2 * (2 : ℝ) ^ s * pointBound l m r (2 ^ s) (α ^ s) (((3 : ℝ) / 4) ^ s) ≤
          ((2 : ℝ) ^ (k * s))⁻¹ / 2 := by
  obtain ⟨α, hα, hα1, h2α, hαε⟩ := exists_cna_base ε hε
  let a := (2 : ℝ) ^ (k + 1)
  have ha : 0 < a := by positivity
  have hβ := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num)).const_mul a
  have hαlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hα.le hα1).const_mul a
  simp only [mul_zero] at hβ hαlim
  obtain ⟨r, hr0, hrβ, hrα⟩ := ((eventually_gt_atTop 0).and
    ((hβ.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).and
      (hαlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)))).exists
  let l := r
  let m := 4 * r
  have htail := cna_point_bound_decay a α ha.le hα.le l m r hrβ hrβ (by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    have hpow : α ^ (m - 2 * t) ≤ α ^ r := pow_le_pow_of_le_one hα.le hα1.le (by dsimp [m]; omega)
    exact (mul_le_mul_of_nonneg_left hpow ha.le).trans_lt hrα)
  have hcard : ∀ᶠ s : ℕ in atTop, (l : ℝ) / (α ^ s) ^ 2 ≤ Real.rpow 2 (ε * (s : ℝ)) := by
    have he := (tendsto_pow_atTop_atTop_of_one_lt hαε).eventually (eventually_ge_atTop (l : ℝ))
    filter_upwards [he] with s hs
    apply (div_le_iff₀ (sq_pos_of_pos (pow_pos hα s))).mpr
    change (l : ℝ) ≤ (2 : ℝ) ^ (ε * (s : ℝ)) * (α ^ s) ^ 2
    rw [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) ε s]
    change (l : ℝ) ≤ (α ^ 2 * (2 : ℝ) ^ ε) ^ s at hs
    simpa only [mul_pow, pow_pow_comm α 2 s, mul_comm] using hs
  have hsize : ∀ᶠ s : ℕ in atTop, l < 2 ^ s := by
    have he := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually (eventually_gt_atTop (l : ℝ))
    filter_upwards [he] with s hs
    exact_mod_cast hs
  refine ⟨l, m, r, α, hr0, hα, hα1.le, by dsimp [m]; omega, ⟨2 * r, by dsimp [m]; omega⟩, ?_⟩
  filter_upwards [eventually_gt_atTop 0, hsize, hcard,
    (cna_large_term_decay α hα h2α l).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 3),
    htail.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)] with s hs hsz hc hlarge hp
  refine ⟨hs, hsz, hc, hlarge, ?_⟩
  have he : a ^ s = (2 : ℝ) ^ s * (2 : ℝ) ^ (k * s) := by
    dsimp [a]
    rw [← pow_mul]
    have hex : (k + 1) * s = s + k * s := by ring
    rw [hex, pow_add]
  rw [he] at hp
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (k * s) := by positivity
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hpos).mpr
  nlinarith

theorem cna_fiber_bound_eventually (s : ℕ) (b : ℝ) (hb : 0 < b) :
    ∀ᶠ w : ℕ in atTop,
      (2 : ℝ) ^ s * Real.exp (-((2 : ℝ) ^ w) / (8 * ((2 : ℝ) ^ s) ^ 2)) ≤ b := by
  have hlim := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_div_const
      (by positivity : (0 : ℝ) < 8 * ((2 : ℝ) ^ s) ^ 2))
  have hlim' := hlim.const_mul ((2 : ℝ) ^ s)
  simp only [mul_zero] at hlim'
  convert hlim'.eventually_le_const hb using 1
  simp only [Function.comp_apply, neg_div]

end Lax323828Proofs
