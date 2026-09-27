import Lax253009.CNAPointSoundness
import Lax253009Proofs.FourierDecoding
import Lax253009Proofs.FourierIdentities
import Lax253009Proofs.HighDegreeSoundness
import Lax253009Proofs.SmallCoefficientSoundness
import Lax253009Proofs.LargeCoefficientSoundness

namespace Lax253009Proofs

open Lax253009.BooleanFourier Lax253009.BalancedPredicates Lax253009.SmallSupport
open Lax253009.FiniteProbability Lax253009.HighDegreeSoundness Lax253009.CNAPointSoundness
open scoped BigOperators symmDiff Classical

/--
---
conclusion: Lax253009.CNAPointSoundness.decoding_card
---
Apply the proved decoding-set estimate at squared threshold τ²/ℓ.
-/
theorem cna_decoding_card {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (hF : ∀ x, |F x| ≤ 1)
    (l : ℕ) (hl : 0 < l) (τ : ℝ) (hτ : 0 < τ) :
    ((decoding F l τ).card : ℝ) ≤ (l : ℝ) / τ ^ 2 := by
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hb := Lax253009.SmallSupport.decodingSet_bound (coefficient F) l (τ ^ 2 / l)
    (div_pos (sq_pos_of_pos hτ) hlr) (Lax253009.BooleanFourier.bounded_energy F hF)
  simpa only [one_div_div, one_mul, decoding] using hb

theorem cna_large_support_subset {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (l : ℕ) (hl : 0 < l) (τ : ℝ) (hτ : 0 < τ)
    (S : Finset ι) (hcard : S.card ≤ l) (hcoeff : τ ≤ |coefficient F S|) :
    S ⊆ decoding F l τ := by
  have hlr : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  intro i hi
  apply Finset.mem_biUnion.mpr
  refine ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard, ?_⟩, hi⟩
  rw [mul_div_cancel₀ _ hlr]
  simpa only [sq_abs] using pow_le_pow_left₀ hτ.le hcoeff 2

theorem cna_shift_energy {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (hF : ∀ x, |F x| ≤ 1) (y : ι) :
    ∑ S : Finset ι, coefficient F (S ∆ {y}) ^ 2 ≤ 1 := by
  have hG (x : Cube ι) : |F x * character {y} x| ≤ 1 := by
    have hy : |sign (x y)| = 1 := by cases x y <;> norm_num [sign]
    simpa only [character, Finset.prod_singleton, abs_mul, hy, mul_one] using hF x
  simpa only [Lax253009.FourierIdentities.character_shift] using Lax253009.BooleanFourier.bounded_energy _ hG

theorem cna_matches_sum {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (F : Cube ι → ℝ) (n : ℕ) (hN : Fintype.card κ = 2 * n)
    (f : ι → κ) (y : ι) (hmatch : Matches F n f y) :
    normalizedSum Finset.univ (fun S ↦ coefficient F (S ∆ {y})) n f = 1 := by
  have : Nonempty (predicates κ n) := balanced_predicates_nonempty n hN
  unfold normalizedSum
  simp_rw [Finset.mul_expect]
  rw [← Finset.expect_sum_comm]
  have he (B : predicates κ n) :
      (∑ S : Finset ι, coefficient F (S ∆ {y}) * ∏ i ∈ S, sign (B.val (f i))) = 1 := by
    have hi := Lax253009.BooleanFourier.inversion (fun x ↦ F x * character {y} x) (fun i ↦ B.val (f i))
    simp_rw [Lax253009.FourierIdentities.character_shift] at hi
    simp only [character, Finset.prod_singleton, hmatch B] at hi
    rw [← hi, sign_sq]
  simp_rw [he]
  rw [Fintype.expect_const]

private theorem normalized_sum_partition {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (c : Finset ι → ℝ) (l n : ℕ) (τ : ℝ) (f : ι → κ) :
    normalizedSum Finset.univ c n f =
      normalizedSum (Finset.univ.filter fun S ↦ l ≤ S.card) c n f +
      normalizedSum (Finset.univ.filter fun S ↦ S.card < l ∧ τ ≤ |c S|) c n f +
      normalizedSum Finset.univ (fun S ↦ if S.card < l ∧ |c S| < τ then c S else 0) n f := by
  unfold normalizedSum
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hd : l ≤ S.card <;> by_cases hc : τ ≤ |c S| <;>
    simp [hd, hc, not_lt.mpr, lt_of_not_ge]

/--
---
conclusion: Lax253009.CNAPointSoundness.point_soundness
---
Agreement forces the full Fourier sum to equal one. Split by degree and
coefficient size. Avoidance of the decoding set isolates the distinguished
label in each large support, making that term at most one third. Therefore
one of the two remaining terms is at least one third; use their proved tails.
-/
theorem cna_point_soundness {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (F : Cube ι → ℝ) (hF : ∀ x, |F x| ≤ 1)
    (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (l m r : ℕ) (hl : 0 < l) (hlN : l < Fintype.card κ)
    (τ q : ℝ) (hτ : 0 < τ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hr : 2 * r ≤ m) (hm : Even m)
    (hlarge : (l : ℝ) / ((Fintype.card κ : ℝ) - l) / τ ≤ 1 / 3)
    (y : ι) :
    probability (fun f : ι → κ ↦ Matches F n f y ∧ Avoids (decoding F l τ) f y) ≤
      pointBound l m r (Fintype.card κ) τ q := by
  let c := fun S ↦ coefficient F (S ∆ {y})
  let H := Finset.univ.filter fun S : Finset ι ↦ l ≤ S.card
  let L := Finset.univ.filter fun S : Finset ι ↦ S.card < l ∧ τ ≤ |c S|
  let d := fun S ↦ if S.card < l ∧ |c S| < τ then c S else 0
  have henergy : ∑ S, c S ^ 2 ≤ 1 := cna_shift_energy F hF y
  have hpartial (T : Finset (Finset ι)) : ∑ S ∈ T, c S ^ 2 ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun S _ _ ↦ sq_nonneg _)).trans henergy
  have hdsmall (S : Finset ι) : |d S| ≤ τ := by
    dsimp only [d]
    split_ifs with h
    · exact h.2.le
    · simpa using hτ.le
  have hddegree (S : Finset ι) (hS : l < S.card) : d S = 0 := by
    simp [d, show ¬ S.card < l by omega]
  have hdenergy : ∑ S, d S ^ 2 ≤ 1 := by
    apply le_trans _ henergy
    apply Finset.sum_le_sum
    intro S _
    dsimp only [d]
    split_ifs <;> simp [sq_nonneg]
  have hevent (f : ι → κ) (hf : Matches F n f y ∧ Avoids (decoding F l τ) f y) :
      (1 : ℝ) / 3 ≤ normalizedSum H c n f ∨ (1 : ℝ) / 3 ≤ normalizedSum Finset.univ d n f := by
    have hy : y ∉ decoding F l τ := fun hy ↦ hf.2 y hy rfl
    have hs (S : Finset ι) (hS : S ∈ L) :
        y ∈ S ∧ S.card ≤ l ∧ ∀ i ∈ S, i ≠ y → f i ≠ f y := by
      obtain ⟨hcard, hcoeff⟩ := (Finset.mem_filter.mp hS).2
      have hshiftcard : (S ∆ {y}).card ≤ l := by
        have h1 := Finset.card_le_card (Finset.symmDiff_subset_union (s := S) (t := {y}))
        have h2 := Finset.card_union_le S {y}
        simp only [Finset.card_singleton] at h2
        omega
      have hsub : S ∆ {y} ⊆ decoding F l τ :=
        cna_large_support_subset F l hl τ hτ _ hshiftcard hcoeff
      have hyS : y ∈ S := by
        by_contra h
        exact hy (hsub (by simp [Finset.mem_symmDiff, h]))
      refine ⟨hyS, hcard.le, fun i hi hiy ↦ ?_⟩
      exact hf.2 i (hsub (by simp [Finset.mem_symmDiff, hi, hiy]))
    have hL := Lax253009.LargeCoefficientSoundness.bound n hN L c l f y τ hτ hlN hs
      (fun S hS ↦ (Finset.mem_filter.mp hS).2.2) (hpartial L)
    have hL' : normalizedSum L c n f ≤ 1 / 3 := (le_abs_self _).trans (hL.trans hlarge)
    have hsum : normalizedSum H c n f + normalizedSum L c n f +
        normalizedSum Finset.univ d n f = 1 := by
      rw [← normalized_sum_partition]
      exact cna_matches_sum F n hN f y hf.1
    by_contra h
    push Not at h
    linarith
  have hhigh := Lax253009.HighDegreeSoundness.tail_bound n hn hN H c l
    (fun S hS ↦ (Finset.mem_filter.mp hS).2) (hpartial H) q hq (1 / 3) (by norm_num)
  have hsmall := Lax253009.SmallCoefficientSoundness.tail_bound n hn hN d l m r τ q hdsmall hτ.le hq hq1
    hddegree hdenergy hr hm (1 / 3) (by norm_num)
  calc
    _ ≤ probability (fun f : ι → κ ↦ (1 : ℝ) / 3 ≤ normalizedSum H c n f ∨
        (1 : ℝ) / 3 ≤ normalizedSum Finset.univ d n f) := Lax253009.FiniteProbability.monotone _ _ hevent
    _ ≤ probability (fun f : ι → κ ↦ (1 : ℝ) / 3 ≤ normalizedSum H c n f) +
        probability (fun f : ι → κ ↦ (1 : ℝ) / 3 ≤ normalizedSum Finset.univ d n f) :=
      Lax253009.FiniteProbability.union_bound _ _
    _ ≤ _ := add_le_add hhigh hsmall
    _ = pointBound l m r (Fintype.card κ) τ q := by
      unfold pointBound
      simp only [one_div, inv_pow, div_inv_eq_mul]
      norm_num
      ring

end Lax253009Proofs
