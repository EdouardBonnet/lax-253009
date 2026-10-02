import Lax323828.FreshBitSampling
import Lax323828Proofs.FiniteProbability

namespace Lax323828Proofs

open Lax323828.FreshBitSampling Lax323828.FiniteProbability
open scoped Classical BigOperators

private theorem probability_complement {α : Type} [Fintype α] [Nonempty α] (P : α → Prop) :
    probability (fun x ↦ ¬ P x) = 1 - probability P := by
  have h : probability P + probability (fun x ↦ ¬ P x) = 1 := by
    simp_rw [finite_probability_indicator]
    rw [← Finset.expect_add_distrib]
    calc
      _ = 𝔼 _x : α, (1 : ℝ) := by
        apply Finset.expect_congr rfl
        intro x _
        by_cases hx : P x <;> simp [hx]
      _ = _ := Fintype.expect_const _
  linarith

private theorem modulo_card_lower {N r B : ℕ} (hr : 0 < r)
    (P : (Fin N → Fin r) → Prop) :
    Fintype.card {w : Fin N → Fin r // P w} * (B / r) ^ N ≤
      Fintype.card {z : Fin N → Fin B // P (modulo hr z)} := by
  let lift : (Fin N → Fin r) → (Fin N → Fin (B / r)) → (Fin N → Fin B) :=
    fun w j i ↦ Fin.castLE (Nat.div_mul_le_self B r) (finProdFinEquiv (j i, w i))
  have hmod (w : Fin N → Fin r) (j : Fin N → Fin (B / r)) : modulo hr (lift w j) = w := by
    funext i
    apply Fin.ext
    simp [modulo, lift, finProdFinEquiv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (w i).isLt]
  let embed : {w : Fin N → Fin r // P w} × (Fin N → Fin (B / r)) →
      {z : Fin N → Fin B // P (modulo hr z)} :=
    fun x ↦ ⟨lift x.1.val x.2, by rw [hmod]; exact x.1.property⟩
  have hinj : Function.Injective embed := by
    intro x y h
    have he : lift x.1.val x.2 = lift y.1.val y.2 := congrArg Subtype.val h
    have hw : x.1.val = y.1.val := by
      have hm := congrArg (modulo hr) he
      simpa only [hmod] using hm
    apply Prod.ext (Subtype.ext hw)
    funext i
    have hi : finProdFinEquiv (x.2 i, x.1.val i) = finProdFinEquiv (y.2 i, y.1.val i) := by
      apply Fin.ext
      have hval := congrArg (fun z : Fin B ↦ z.val) (congrFun he i)
      exact hval
    exact congrArg Prod.fst (finProdFinEquiv.injective hi)
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_le_of_injective embed hinj

private theorem modulo_probability_lower {N r B : ℕ} (hr : 0 < r) (hB : 0 < B)
    (P : (Fin N → Fin r) → Prop) :
    (((B / r : ℕ) : ℝ) * r / B) ^ N * probability P ≤
      probability (fun z : Fin N → Fin B ↦ P (modulo hr z)) := by
  have hc : (Fintype.card {w : Fin N → Fin r // P w} : ℝ) * (B / r : ℕ) ^ N ≤
      Fintype.card {z : Fin N → Fin B // P (modulo hr z)} := by
    exact_mod_cast modulo_card_lower hr P
  have hr' : (r : ℝ) ≠ 0 := by positivity
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  unfold probability
  simp only [Fintype.card_fun, Fintype.card_fin]
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  push_cast
  apply (le_div_iff₀ (pow_pos hB' N)).mpr
  calc
    _ = (Fintype.card {w : Fin N → Fin r // P w} : ℝ) * (B / r : ℕ) ^ N := by
      rw [div_pow, mul_pow]
      field_simp
    _ ≤ _ := hc

/--
---
conclusion: Lax323828.FreshBitSampling.modulo_error
---
Every tuple of residues has at least floor(B/r)^N preimages. Apply this
lower bound to the complement event, then Bernoulli's inequality bounds
the mass lost in incomplete residue blocks by Nr/B.
-/
theorem fresh_modulo_error {N r B : ℕ} (hr : 0 < r) (hB : 0 < B)
    (P : (Fin N → Fin r) → Prop) :
    probability (fun z : Fin N → Fin B ↦ P (modulo hr z)) ≤
      probability P + (N : ℝ) * r / B := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have : Nonempty (Fin B) := ⟨⟨0, hB⟩⟩
  let a : ℝ := ((B / r : ℕ) : ℝ) * r / B
  have ha : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hB)).mpr
    exact_mod_cast Nat.div_mul_le_self B r
  have hpow : a ^ N ≤ 1 := pow_le_one₀ ha ha1
  have hlow := modulo_probability_lower hr hB (fun w ↦ ¬ P w)
  rw [probability_complement, probability_complement] at hlow
  have hP0 := finite_probability_nonneg P
  have hP1 := finite_probability_le_one P
  have hupper : probability (fun z : Fin N → Fin B ↦ P (modulo hr z)) ≤
      probability P + (1 - a ^ N) := by
    change a ^ N * (1 - probability P) ≤ 1 - probability (fun z ↦ P (modulo hr z)) at hlow
    nlinarith [mul_nonneg (sub_nonneg.mpr hpow) hP0]
  have hbern : 1 - a ^ N ≤ (N : ℝ) * (1 - a) := by
    have h := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ a by linarith) N
    linarith
  have hremain : 1 - a ≤ (r : ℝ) / B := by
    dsimp [a]
    apply (le_div_iff₀ (by exact_mod_cast hB)).mpr
    have hrem : (B : ℝ) - (B / r : ℕ) * r ≤ r := by
      have he := Nat.mod_add_div B r
      have hlt := Nat.mod_lt B hr
      have he' : ((B % r : ℕ) : ℝ) + (r : ℝ) * (B / r : ℕ) = B := by exact_mod_cast he
      have hlt' : ((B % r : ℕ) : ℝ) < r := by exact_mod_cast hlt
      linarith
    have hBne : (B : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith
  calc
    _ ≤ probability P + (1 - a ^ N) := hupper
    _ ≤ probability P + (N : ℝ) * (1 - a) := add_le_add le_rfl hbern
    _ ≤ probability P + (N : ℝ) * (r / B) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hremain (Nat.cast_nonneg _))
    _ = _ := by ring

/--
---
conclusion: Lax323828.FreshBitSampling.sampling_error
---
Binary interpretation is a bijection. The chosen power-of-two range is
at least 12Nr, making the total modulo error at most 1/12.
-/
theorem fresh_sampling_error {N r : ℕ} (_hN : 0 < N) (hr : 0 < r)
    (P : (Fin N → Fin r) → Prop) :
    probability (fun z : Fin N → Fin (bitsPerDraw N r) → Bool ↦ P (sample hr z)) ≤
      probability P + 1 / 12 := by
  have he := finite_probability_equiv
    (Equiv.piCongrRight (fun _ : Fin N ↦ binaryEquiv (bitsPerDraw N r)))
    (fun z ↦ P (sample hr z)) (fun z ↦ P (modulo hr z)) (fun _ ↦ Iff.rfl)
  rw [he]
  apply (Lax323828.FreshBitSampling.modulo_error hr (pow_pos (by norm_num) _) P).trans
  apply add_le_add le_rfl
  apply (div_le_iff₀ (by positivity)).mpr
  have h := Nat.le_pow_clog (b := 2) (by norm_num) (12 * N * r)
  have h' : (12 : ℝ) * N * r ≤ (2 : ℝ) ^ bitsPerDraw N r := by exact_mod_cast h
  push_cast
  nlinarith

/--
---
conclusion: Lax323828.FreshBitSampling.one_third_error
---
Add the 1/12 sampling error to the graph construction's 1/4 bound.
-/
theorem fresh_one_third_error {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (P : (Fin N → Fin r) → Prop) (hP : probability P ≤ 1 / 4) :
    probability (fun z : Fin N → Fin (bitsPerDraw N r) → Bool ↦ P (sample hr z)) ≤ 1 / 3 := by
  have h := Lax323828.FreshBitSampling.sampling_error hN hr P
  linarith

/--
---
conclusion: Lax323828.FreshBitSampling.flat_one_third_error
---
Partition a single vector of fair bits into consecutive blocks using the
explicit product-index equivalence.
-/
theorem fresh_flat_one_third_error {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (P : (Fin N → Fin r) → Prop) (hP : probability P ≤ 1 / 4) :
    probability (fun coins : Fin (N * bitsPerDraw N r) → Bool ↦ P (sampleFlat hr coins)) ≤ 1 / 3 := by
  unfold sampleFlat
  rw [finite_probability_equiv (coinEquiv N (bitsPerDraw N r)) _
    (fun z ↦ P (sample hr z)) (fun _ ↦ Iff.rfl)]
  exact Lax323828.FreshBitSampling.one_third_error hN hr P hP

/--
---
conclusion: Lax323828.FreshBitSampling.repeated_seed_bit_bound
---
Exponentiation of the seed space only multiplies its binary logarithm.
-/
theorem fresh_repeated_seed_bit_bound (N r k : ℕ) :
    bitsPerDraw N (r ^ k) ≤ Nat.clog 2 (12 * N) + k * Nat.clog 2 r := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add, pow_mul']
  exact Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) _)
    (Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) _)

end Lax323828Proofs
