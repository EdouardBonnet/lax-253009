import Lax323828.FourierIdentities
import Lax323828Proofs.FourierProjection

namespace Lax323828Proofs

open Lax323828.BooleanFourier Lax323828.FourierIdentities
open scoped symmDiff

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem character_mul (S T : Finset ι) (x : Cube ι) :
    character S x * character T x = character (S ∆ T) x := by
  simp_rw [character_univ, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [Finset.mem_symmDiff, hS, hT, sign_sq]

/--
---
conclusion: Lax323828.FourierIdentities.character_shift
---
The factors on the common coordinates square to one; the remaining support
is the symmetric difference.
-/
theorem fourier_character_shift (F : Cube ι → ℝ) (S T : Finset ι) :
    coefficient (fun x ↦ F x * character T x) S = coefficient F (S ∆ T) := by
  simp only [coefficient, mul_assoc, character_mul, symmDiff_comm T S]

private theorem sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

omit [Fintype ι] [DecidableEq ι] in
private theorem character_flip (S : Finset ι) (x : Cube ι) :
    character S (bitFlip x) = (-1 : ℝ) ^ S.card * character S x := by
  simp [character, bitFlip, sign_not, Finset.prod_neg]

private theorem average_flip (F : Cube ι → ℝ) :
    average (fun x ↦ F (bitFlip x)) = average F := by
  have hi : Function.Involutive (bitFlip (ι := ι)) := by intro x; funext i; simp [bitFlip]
  unfold average
  congr 1
  exact Equiv.sum_comp (hi.toPerm bitFlip) F

/--
---
conclusion: Lax323828.FourierIdentities.odd_even_vanish
---
Pair every input with its bitwise complement. For an even support its
character is unchanged, whereas the table value changes sign.
-/
theorem fourier_odd_even (F : Cube ι → ℝ) (hF : ∀ x, F (bitFlip x) = -F x)
    (S : Finset ι) (hS : Even S.card) : coefficient F S = 0 := by
  have h := average_flip (fun x ↦ F x * character S x)
  have hn : average (fun x ↦ -(F x * character S x)) =
      -average (fun x ↦ F x * character S x) := by
    simp [average, Finset.sum_neg_distrib, neg_div]
  simp_rw [hF, character_flip, hS.neg_one_pow, one_mul, neg_mul] at h
  rw [hn] at h
  change -coefficient F S = coefficient F S at h
  linarith

/--
---
conclusion: Lax323828.FourierIdentities.disagreement_indicator
---
Check the two possible signs of each Boolean value.
-/
theorem fourier_disagreement_indicator {κ : Type} (A : Cube κ → Bool) (y : κ) (x : Cube κ) :
    disagreement A y x = if A x = x y then 0 else 1 := by
  cases ha : A x <;> cases hx : x y <;> norm_num [disagreement, ha, hx, sign]

/--
---
conclusion: Lax323828.FourierIdentities.disagreement_coefficient
---
Use linearity, the coefficient of the constant function, and the singleton
character shift.
-/
theorem fourier_disagreement (A : Cube ι → Bool) (y : ι) (S : Finset ι) :
    coefficient (disagreement A y) S =
      ((if S = ∅ then 1 else 0) - coefficient (fun x ↦ sign (A x)) (S ∆ {y})) / 2 := by
  have hconst : coefficient (fun _ : Cube ι ↦ (1 : ℝ)) S =
      if S = ∅ then 1 else 0 := by
    simpa [coefficient, character, eq_comm] using Lax323828.BooleanFourier.orthogonality ∅ S
  have hlinear : coefficient (disagreement A y) S =
      (coefficient (fun _ : Cube ι ↦ (1 : ℝ)) S -
        coefficient (fun x ↦ sign (A x) * character {y} x) S) / 2 := by
    simp only [coefficient, disagreement, div_mul_eq_mul_div, sub_mul, one_mul]
    rw [average_div, average_sub]
    simp [character]
    rfl
  rw [hlinear, hconst, Lax323828.FourierIdentities.character_shift]

end Lax323828Proofs
