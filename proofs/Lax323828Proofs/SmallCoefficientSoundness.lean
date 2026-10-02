import Lax323828.SmallCoefficientSoundness
import Lax323828Proofs.SmallUnionDoubleCovers
import Lax323828Proofs.MixedPredicateMoments
import Lax323828Proofs.BalancedCancellation

namespace Lax323828Proofs

open Lax323828.BooleanFourier Lax323828.BalancedPredicates Lax323828.HigherMoments
open Lax323828.HighDegreeSoundness Lax323828.SmallCoefficientSoundness Lax323828.FiniteProbability
open scoped BigOperators Classical

private noncomputable def mixedMoment {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (n : ℕ) {m : ℕ} (S : Fin m → Finset ι) : ℝ :=
  𝔼 B : Fin m → predicates κ n, 𝔼 f : ι → κ,
    ∏ j, ∏ i ∈ S j, sign ((B j).val (f i))

private theorem moment_expansion {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (n : ℕ) (c : Finset ι → ℝ) (m : ℕ) :
    (𝔼 f : ι → κ, normalizedSum Finset.univ c n f ^ m) =
      ∑ S : Fin m → Finset ι, (∏ j, c (S j)) * mixedMoment (κ := κ) n S := by
  unfold normalizedSum
  simp_rw [Fintype.sum_pow, Finset.prod_mul_distrib, Finset.expect_sum_comm, ← Finset.mul_expect]
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  have he (f : ι → κ) :
      (∏ j, (𝔼 B : predicates κ n, ∏ i ∈ S j, sign (B.val (f i)))) =
        (𝔼 B : Fin m → predicates κ n, ∏ j, ∏ i ∈ S j, sign ((B j).val (f i))) :=
    (independent_product_average (fun (j : Fin m) (B : predicates κ n) ↦
      ∏ i ∈ S j, sign (B.val (f i)))).symm
  simp_rw [he]
  unfold mixedMoment
  rw [Finset.expect_comm]

private theorem mixed_moment_zero {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (n : ℕ) (hN : Fintype.card κ = 2 * n)
    {m : ℕ} (S : Fin m → Finset ι) (hS : ¬ DoubleCover S) : mixedMoment (κ := κ) n S = 0 := by
  simp only [DoubleCover, not_forall, not_le] at hS
  obtain ⟨i, hi, hcard⟩ := hS
  have hpos : 0 < (Finset.univ.filter fun j ↦ i ∈ S j).card := by
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hi
    exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (show (Finset.univ.filter fun j ↦ i ∈ S j).card = 1 by omega)
  have hij : i ∈ S j := by
    have h : j ∈ Finset.univ.filter fun j ↦ i ∈ S j := by rw [hj]; simp
    exact (Finset.mem_filter.mp h).2
  have huniq (j' : Fin m) (hi' : i ∈ S j') : j' = j := by
    have h : j' ∈ Finset.univ.filter fun j ↦ i ∈ S j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩
    rw [hj] at h
    exact Finset.mem_singleton.mp h
  have he (B : Fin m → predicates κ n) :
      (𝔼 f : ι → κ, ∏ j, ∏ i ∈ S j, sign ((B j).val (f i))) = 0 := by
    apply Lax323828.HigherMoments.singleton_cancellation S (fun j z ↦ sign ((B j).val z)) _ i j hij huniq
    intro j
    rw [Fintype.expect_eq_sum_div_card, balanced_sign_sum n hN (B j), zero_div]
  unfold mixedMoment
  simp_rw [he]
  simp

private theorem mixed_moment_abs_le_one {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (n : ℕ) (hN : Fintype.card κ = 2 * n)
    {m : ℕ} (S : Fin m → Finset ι) : |mixedMoment (κ := κ) n S| ≤ 1 := by
  have : Nonempty (predicates κ n) := balanced_predicates_nonempty n hN
  apply (Finset.abs_expect_le _ _).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro B _
  apply (Finset.abs_expect_le _ _).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro f _
  simp only [Finset.abs_prod]
  have hs (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]
  simp [hs]

/--
---
conclusion: Lax323828.SmallCoefficientSoundness.moment_bound
---
Cancel tuples that are not double covers. For small unions use the small
coefficient bound, and for large unions use mixed-predicate concentration.
-/
theorem small_coefficient_moment_bound {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (c : Finset ι → ℝ) (l m r : ℕ) (δ q : ℝ)
    (hsmall : ∀ S, |c S| ≤ δ) (hδ : 0 ≤ δ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hdegree : ∀ S, l < S.card → c S = 0) (henergy : ∑ S, c S ^ 2 ≤ 1)
    (hr : 2 * r ≤ m) :
    (𝔼 f : ι → κ, normalizedSum Finset.univ c n f ^ m) ≤
      boundValue l m r (Fintype.card κ) δ q := by
  let d := fun S ↦ |c S|
  let F := fun S : Fin m → Finset ι ↦ ∏ j, d (S j)
  let H := q ^ r + (2 : ℝ) ^ m *
    (2 * (Fintype.card κ + 1 : ℝ) * Real.exp (-(Fintype.card κ : ℝ) * q ^ 2 / 2))
  have hH : 0 ≤ H := by positivity
  have hF (S : Fin m → Finset ι) : 0 ≤ F S := Finset.prod_nonneg fun j _ ↦ abs_nonneg _
  have hdeg : ∀ S, l < S.card → d S = 0 := by intro S hS; simp [d, hdegree S hS]
  have henergy' : ∑ S, d S ^ 2 ≤ 1 := by simpa only [d, sq_abs] using henergy
  let A := fun (S : Fin m → Finset ι) ↦ ∑ t ∈ Finset.range r,
    if DoubleCover S ∧ (Finset.univ.biUnion S).card = t then F S else 0
  have hA (S : Fin m → Finset ι) : 0 ≤ A S := by
    apply Finset.sum_nonneg
    intro t _
    split_ifs
    · exact hF S
    · exact le_rfl
  have hterm (S : Fin m → Finset ι) :
      (∏ j, c (S j)) * mixedMoment (κ := κ) n S ≤
        A S + if DoubleCover S then F S * H else 0 := by
    by_cases hdc : DoubleCover S
    · rw [if_pos hdc]
      have hbase : (∏ j, c (S j)) * mixedMoment (κ := κ) n S ≤
          F S * |mixedMoment (κ := κ) n S| := by
        simpa only [abs_mul, Finset.abs_prod, F, d] using
          le_abs_self ((∏ j, c (S j)) * mixedMoment (κ := κ) n S)
      by_cases hcard : (Finset.univ.biUnion S).card < r
      · have hmom : (∏ j, c (S j)) * mixedMoment (κ := κ) n S ≤ F S := by
          have hx := mul_le_mul_of_nonneg_left (mixed_moment_abs_le_one (κ := κ) n hN S) (hF S)
          exact hbase.trans (by simpa only [mul_one] using hx)
        have hs : F S ≤ A S := by
          have hx := Finset.single_le_sum (f := fun t ↦
            if DoubleCover S ∧ (Finset.univ.biUnion S).card = t then F S else 0)
            (fun t _ ↦ by split_ifs; exact hF S; exact le_rfl)
            (Finset.mem_range.mpr hcard)
          simpa only [A, hdc, and_self, if_true] using hx
        exact hmom.trans (hs.trans (le_add_of_nonneg_right (mul_nonneg (hF S) hH)))
      · have hmom : |mixedMoment (κ := κ) n S| ≤ H := by
          apply (Lax323828.MixedPredicateMoments.bound n hn hN m S q hq).trans
          exact add_le_add (pow_le_pow_of_le_one hq hq1 (by omega)) (le_refl _)
        exact (hbase.trans (mul_le_mul_of_nonneg_left hmom (hF S))).trans
          (le_add_of_nonneg_left (hA S))
    · rw [mixed_moment_zero n hN S hdc, mul_zero, if_neg hdc, add_zero]
      exact hA S
  have hsumA : (∑ S : Fin m → Finset ι, A S) =
      ∑ t ∈ Finset.range r, Lax323828.SmallUnionDoubleCovers.weight d m t := by
    dsimp only [A, Lax323828.SmallUnionDoubleCovers.weight]
    rw [Finset.sum_comm]
  have hsumH : (∑ S : Fin m → Finset ι, if DoubleCover S then F S * H else 0) =
      Lax323828.DoubleCoverBounds.weight d m * H := by
    unfold Lax323828.DoubleCoverBounds.weight
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> simp [F]
  rw [moment_expansion n c m]
  calc
    _ ≤ ∑ S : Fin m → Finset ι, (A S + if DoubleCover S then F S * H else 0) :=
      Finset.sum_le_sum fun S _ ↦ hterm S
    _ = (∑ t ∈ Finset.range r, Lax323828.SmallUnionDoubleCovers.weight d m t) +
        Lax323828.DoubleCoverBounds.weight d m * H := by
      rw [Finset.sum_add_distrib, hsumA, hsumH]
    _ ≤ boundValue l m r (Fintype.card κ) δ q := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro t ht
        exact Lax323828.SmallUnionDoubleCovers.bound d l m t δ (fun S ↦ abs_nonneg _)
          hsmall hδ hdeg henergy' (by have := Finset.mem_range.mp ht; omega)
      · exact mul_le_mul_of_nonneg_right
          (Lax323828.DoubleCoverBounds.bound d l m (fun S ↦ abs_nonneg _) hdeg henergy') hH

/--
---
conclusion: Lax323828.SmallCoefficientSoundness.tail_bound
---
Apply the finite even-moment tail inequality to the normalized Fourier sum.
-/
theorem small_coefficient_tail {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (c : Finset ι → ℝ) (l m r : ℕ) (δ q : ℝ)
    (hsmall : ∀ S, |c S| ≤ δ) (hδ : 0 ≤ δ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hdegree : ∀ S, l < S.card → c S = 0) (henergy : ∑ S, c S ^ 2 ≤ 1)
    (hr : 2 * r ≤ m) (hm : Even m) (a : ℝ) (ha : 0 < a) :
    probability (fun f : ι → κ ↦ a ≤ normalizedSum Finset.univ c n f) ≤
      boundValue l m r (Fintype.card κ) δ q / a ^ m := by
  apply (Lax323828.FiniteProbability.even_moment_bound _ a ha m hm).trans
  exact div_le_div_of_nonneg_right
    (Lax323828.SmallCoefficientSoundness.moment_bound n hn hN c l m r δ q hsmall hδ hq hq1 hdegree henergy hr)
    (pow_nonneg ha.le m)

end Lax323828Proofs
