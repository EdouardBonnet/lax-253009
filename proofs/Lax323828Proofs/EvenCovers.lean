import Lax323828.EvenCovers
import Lax323828Proofs.HigherMoments

namespace Lax323828Proofs

open Lax323828.BooleanFourier Lax323828.HigherMoments Lax323828.EvenCovers
open scoped BigOperators

private theorem mean_sign_pow (n : ℕ) :
    (𝔼 b : Bool, sign b ^ n) = if Even n then 1 else 0 := by
  rw [Fintype.expect_eq_sum_div_card]
  by_cases h : Even n
  · simp [h, sign, h.neg_one_pow]
  · have hn : Odd n := Nat.not_even_iff_odd.mp h
    simp [h, sign, hn.neg_one_pow]

/--
---
conclusion: Lax323828.EvenCovers.character_moment
---
Factor by coordinates. A coordinate with odd multiplicity has zero mean;
every even multiplicity contributes one.
-/
theorem even_cover_character_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (S : Fin m → Finset ι) :
    (𝔼 x : Cube ι, ∏ j, character (S j) x) =
      if EvenCover S then 1 else 0 := by
  classical
  unfold character
  rw [Lax323828.HigherMoments.factorization S (fun _ ↦ sign)]
  simp_rw [Finset.prod_const, mean_sign_pow]
  by_cases h : EvenCover S
  · rw [if_pos h]
    exact Finset.prod_eq_one fun i _ ↦ if_pos (h i)
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/--
---
conclusion: Lax323828.EvenCovers.polynomial_moment
---
Expand the power as a sum over ordered tuples and apply the character
moment identity to each tuple.
-/
theorem even_cover_polynomial_moment {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] (S : α → Finset ι) (c : α → ℝ) (m : ℕ) :
    (𝔼 x : Cube ι, (∑ a, c a * character (S a) x) ^ m) =
      ∑ a : Fin m → α, if EvenCover (fun j ↦ S (a j)) then ∏ j, c (a j) else 0 := by
  classical
  simp_rw [Fintype.sum_pow, Finset.prod_mul_distrib, Finset.expect_sum_comm,
    ← Finset.mul_expect, Lax323828.EvenCovers.character_moment]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

/--
---
conclusion: Lax323828.EvenCovers.even_implies_double
---
A positive even multiplicity is at least two.
-/
theorem even_cover_is_double {ι : Type} [DecidableEq ι] {m : ℕ}
    (S : Fin m → Finset ι) (hS : EvenCover S) : DoubleCover S := by
  intro i hi
  obtain ⟨j, _, hij⟩ := Finset.mem_biUnion.mp hi
  have hp : 0 < (Finset.univ.filter fun j ↦ i ∈ S j).card :=
    Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
  obtain ⟨k, hk⟩ := hS i
  omega

end Lax323828Proofs
