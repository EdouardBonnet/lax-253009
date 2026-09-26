import Lax253009.BalancedCancellation
import Lax253009Proofs.BalancedPredicates

namespace Lax253009Proofs

open Lax253009.BooleanFourier Lax253009.BalancedPredicates
open scoped BigOperators

private theorem true_count_reindex {κ : Type} [Fintype κ] [DecidableEq κ]
    (B : Cube κ) (e : κ ≃ κ) :
    (Finset.univ.filter fun z ↦ B (e z) = true).card =
      (Finset.univ.filter fun z ↦ B z = true).card := by
  classical
  refine Finset.card_bij (fun z _ ↦ e z) ?_ ?_ ?_
  · intro z hz
    simpa using hz
  · intro x _ y _ h
    exact e.injective h
  · intro z hz
    exact ⟨e.symm z, by simpa using hz, e.apply_symm_apply z⟩

private def reindexBalanced {κ : Type} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (e : κ ≃ κ) : predicates κ n ≃ predicates κ n where
  toFun B := ⟨fun z ↦ B.val (e z), by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [true_count_reindex]
    exact (Finset.mem_filter.mp B.property).2⟩
  invFun B := ⟨fun z ↦ B.val (e.symm z), by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [true_count_reindex]
    exact (Finset.mem_filter.mp B.property).2⟩
  left_inv B := by apply Subtype.ext; funext z; simp
  right_inv B := by apply Subtype.ext; funext z; simp

theorem balanced_sign_sum {κ : Type} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hN : Fintype.card κ = 2 * n) (B : predicates κ n) :
    (∑ z, sign (B.val z)) = 0 := by
  have hb := (Finset.mem_filter.mp B.property).2
  have hi (b : Bool) : sign b = 1 - 2 * (if b = true then (1 : ℝ) else 0) := by
    cases b <;> norm_num [sign]
  simp_rw [hi, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
  simp [hb, hN]

private theorem balanced_outside_symmetry {κ : Type} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (S : Finset κ) (F : Cube κ → ℝ)
    (hdepends : ∀ B C, (∀ z ∈ S, B z = C z) → F B = F C)
    (y z : κ) (hy : y ∉ S) (hz : z ∉ S) :
    (𝔼 B : predicates κ n, sign (B.val z) * F B.val) =
      (𝔼 B : predicates κ n, sign (B.val y) * F B.val) := by
  classical
  apply Fintype.expect_equiv (reindexBalanced n (Equiv.swap y z))
  intro B
  change sign (B.val z) * F B.val =
    sign (B.val (Equiv.swap y z y)) * F (fun a ↦ B.val (Equiv.swap y z a))
  rw [Equiv.swap_apply_left]
  congr 1
  apply hdepends
  intro a ha
  have hay : a ≠ y := fun h ↦ hy (h ▸ ha)
  have haz : a ≠ z := fun h ↦ hz (h ▸ ha)
  rw [Equiv.swap_apply_of_ne_of_ne hay haz]

private theorem absolute_character {κ : Type} (S : Finset κ) (B : Cube κ) :
    |character S B| = 1 := by
  have hb (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]
  simp [character, Finset.abs_prod, hb]

/--
---
conclusion: Lax253009.BalancedCancellation.bounded_support_correlation
---
Multiply the balanced zero-sum identity by a bounded function supported on S. All outside
coordinates have the same mean by a transposition; the inside sum is at
most |S| in absolute value.
-/
theorem balanced_bounded_support_correlation {κ : Type} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hN : Fintype.card κ = 2 * n) (S : Finset κ)
    (F : Cube κ → ℝ) (hF : ∀ B, |F B| ≤ 1)
    (hdepends : ∀ B C, (∀ z ∈ S, B z = C z) → F B = F C)
    (y : κ) (hy : y ∉ S) :
    |𝔼 B : predicates κ n, sign (B.val y) * F B.val| ≤
      (S.card : ℝ) / ((Fintype.card κ : ℝ) - S.card) := by
  classical
  have hp : (predicates κ n).Nonempty := by
    rw [← Finset.card_pos, balanced_predicate_count, hN]
    exact Nat.choose_pos (by omega)
  have : Nonempty (predicates κ n) := ⟨⟨hp.choose, hp.choose_spec⟩⟩
  let R : κ → ℝ := fun z ↦ 𝔼 B : predicates κ n, sign (B.val z) * F B.val
  have hzero : ∑ z, R z = 0 := by
    dsimp [R]
    rw [← Finset.expect_sum_comm]
    have hz (B : predicates κ n) : (∑ z, sign (B.val z) * F B.val) = 0 := by
      rw [← Finset.sum_mul, balanced_sign_sum n hN B, zero_mul]
    simp_rw [hz]
    simp
  have hR (z : κ) : |R z| ≤ 1 := by
    apply le_trans (Finset.abs_expect_le _ _)
    apply Finset.expect_le Finset.univ_nonempty
    intro B _
    have hs : |sign (B.val z)| = 1 := by cases B.val z <;> norm_num [sign]
    simpa only [abs_mul, hs, one_mul] using hF B.val
  have hsame (z : κ) (hz : z ∈ Finset.univ \ S) : R z = R y :=
    balanced_outside_symmetry n S F hdepends y z hy (Finset.mem_sdiff.mp hz).2
  have hcard : S.card < Fintype.card κ := by
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, fun he ↦ hy (he.symm ▸ Finset.mem_univ y)⟩)
  have hd : (0 : ℝ) < (Fintype.card κ : ℝ) - S.card := sub_pos.mpr (by exact_mod_cast hcard)
  have hNcard : S.card ≤ Fintype.card κ := hcard.le
  have hout : ((Fintype.card κ : ℝ) - S.card) * R y = -(∑ z ∈ S, R z) := by
    have hs := Finset.sum_sdiff (f := R) (Finset.subset_univ S)
    rw [hzero] at hs
    have houtsum : (∑ z ∈ Finset.univ \ S, R z) =
        ((Fintype.card κ : ℝ) - S.card) * R y := by
      rw [Finset.sum_congr rfl hsame, Finset.sum_const, nsmul_eq_mul,
        Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Nat.cast_sub hNcard]
    rw [houtsum] at hs
    linarith
  have hinside : |∑ z ∈ S, R z| ≤ (S.card : ℝ) := by
    calc
      _ ≤ ∑ z ∈ S, |R z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _z ∈ S, (1 : ℝ) := Finset.sum_le_sum fun z _ ↦ hR z
      _ = _ := by simp
  have hb : |R y| ≤ (S.card : ℝ) / ((Fintype.card κ : ℝ) - S.card) := by
    apply (le_div_iff₀ hd).mpr
    have he := congrArg abs hout
    rw [abs_mul, abs_of_pos hd, abs_neg] at he
    nlinarith
  exact hb

/--
---
conclusion: Lax253009.BalancedCancellation.small_support_correlation
---
Apply bounded-support cancellation to the character on S.
-/
theorem balanced_small_support_correlation {κ : Type} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hN : Fintype.card κ = 2 * n) (S : Finset κ) (y : κ) (hy : y ∉ S) :
    |𝔼 B : predicates κ n, character (insert y S) B.val| ≤
      (S.card : ℝ) / ((Fintype.card κ : ℝ) - S.card) := by
  have hb := balanced_bounded_support_correlation n hN S (character S)
    (fun B ↦ (absolute_character S B).le)
    (fun B C h ↦ Finset.prod_congr rfl (fun z hz ↦ congrArg sign (h z hz))) y hy
  simpa only [character, Finset.prod_insert hy] using hb

end Lax253009Proofs
