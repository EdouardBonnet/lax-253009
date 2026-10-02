import Lax323828.HighDegreeSoundness
import Lax323828Proofs.BalancedCancellation
import Lax323828Proofs.ProductMoments

namespace Lax323828Proofs

open Lax323828.BooleanFourier Lax323828.BalancedPredicates
open Lax323828.FiniteProbability Lax323828.HighDegreeSoundness
open scoped BigOperators

private theorem balanced_mean_zero {κ : Type} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hN : Fintype.card κ = 2 * n) (B : predicates κ n) :
    (𝔼 z, sign (B.val z)) = 0 := by
  rw [Fintype.expect_eq_sum_div_card, balanced_sign_sum n hN B, zero_div]

private theorem sign_abs_le_one (b : Bool) : |sign b| ≤ 1 := by
  cases b <;> norm_num [sign]

private theorem normalized_second_moment {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (n : ℕ) (hN : Fintype.card κ = 2 * n)
    (supports : Finset (Finset ι)) (c : Finset ι → ℝ) :
    (𝔼 f : ι → κ, normalizedSum supports c n f ^ 2) =
      ∑ S ∈ supports, c S ^ 2 *
        (𝔼 B : predicates κ n, 𝔼 C : predicates κ n, (𝔼 z, sign (B.val z) * sign (C.val z)) ^ S.card) := by
  classical
  have hfeatures (S T : Finset ι) :
      (𝔼 f : ι → κ, (𝔼 B : predicates κ n, ∏ i ∈ S, sign (B.val (f i))) *
        (𝔼 C : predicates κ n, ∏ i ∈ T, sign (C.val (f i)))) =
      if S = T then
        (𝔼 B : predicates κ n, 𝔼 C : predicates κ n, (𝔼 z, sign (B.val z) * sign (C.val z)) ^ S.card)
      else 0 := by
    simp_rw [Fintype.expect_mul_expect]
    rw [Finset.expect_comm]
    have hi (B : predicates κ n) :
        (𝔼 f : ι → κ, 𝔼 C : predicates κ n,
          (∏ i ∈ S, sign (B.val (f i))) * (∏ i ∈ T, sign (C.val (f i)))) =
        (𝔼 C : predicates κ n, if S = T then
          (𝔼 z, sign (B.val z) * sign (C.val z)) ^ S.card else 0) := by
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro C _
      exact Lax323828.ProductMoments.mixed_moment _ _ (balanced_mean_zero n hN B) (balanced_mean_zero n hN C) S T
    simp_rw [hi]
    split_ifs <;> simp
  unfold normalizedSum
  rw [weighted_sum_second_moment]
  simp_rw [hfeatures, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro S hS
  simp [hS, pow_two]

private theorem normalized_correlation_tail {κ : Type} [Fintype κ] [DecidableEq κ]
    [Nonempty κ] (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (B : predicates κ n) (q : ℝ) (hq : 0 ≤ q) :
    probability (fun C : predicates κ n ↦ q < |𝔼 z, sign (B.val z) * sign (C.val z)|) ≤
      2 * (Fintype.card κ + 1 : ℝ) * Real.exp (-(Fintype.card κ : ℝ) * q ^ 2 / 2) := by
  have hM : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ probability (fun C : predicates κ n ↦
        (Fintype.card κ : ℝ) * q ≤ |∑ z, sign (B.val z) * sign (C.val z)|) := by
      apply Lax323828.FiniteProbability.monotone
      intro C hC
      rw [Fintype.expect_eq_sum_div_card, abs_div, abs_of_pos hM] at hC
      simpa only [mul_comm q] using ((lt_div_iff₀ hM).mp hC).le
    _ ≤ 2 * (Fintype.card κ + 1 : ℝ) *
        Real.exp (-((Fintype.card κ : ℝ) * q) ^ 2 / (2 * Fintype.card κ)) :=
      Lax323828.BalancedPredicates.absolute_correlation_tail n hn hN B.val _ (mul_nonneg hM.le hq)
    _ = _ := by
      congr 2
      field_simp

/--
---
conclusion: Lax323828.HighDegreeSoundness.second_moment_bound
---
Cancel unequal supports. For each fixed predicate, split correlation powers
at q, apply balanced concentration, and sum the squared coefficients.
-/
theorem high_degree_second_moment {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (supports : Finset (Finset ι)) (c : Finset ι → ℝ) (l : ℕ)
    (hdegree : ∀ S ∈ supports, l ≤ S.card) (henergy : ∑ S ∈ supports, c S ^ 2 ≤ 1)
    (q : ℝ) (hq : 0 ≤ q) :
    (𝔼 f : ι → κ, normalizedSum supports c n f ^ 2) ≤
      q ^ l + 2 * (Fintype.card κ + 1 : ℝ) * Real.exp (-(Fintype.card κ : ℝ) * q ^ 2 / 2) := by
  classical
  have hp : (predicates κ n).Nonempty := by
    rw [← Finset.card_pos, Lax323828.BalancedPredicates.count, hN]
    exact Nat.choose_pos (by omega)
  have : Nonempty (predicates κ n) := ⟨⟨hp.choose, hp.choose_spec⟩⟩
  let K := q ^ l + 2 * (Fintype.card κ + 1 : ℝ) * Real.exp (-(Fintype.card κ : ℝ) * q ^ 2 / 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hterm (S : Finset ι) (hS : S ∈ supports) :
      (𝔼 B : predicates κ n, 𝔼 C : predicates κ n,
        (𝔼 z, sign (B.val z) * sign (C.val z)) ^ S.card) ≤ K := by
    apply Finset.expect_le Finset.univ_nonempty
    intro B _
    let X : predicates κ n → ℝ := fun C ↦ |𝔼 z, sign (B.val z) * sign (C.val z)|
    have hX (C : predicates κ n) : 0 ≤ X C ∧ X C ≤ 1 :=
      ⟨abs_nonneg _, correlation_abs_le_one _ _ (fun _ ↦ sign_abs_le_one _) (fun _ ↦ sign_abs_le_one _)⟩
    calc
      _ ≤ 𝔼 C : predicates κ n, X C ^ l := by
        apply Finset.expect_le_expect
        intro C _
        calc
          _ ≤ X C ^ S.card := (le_abs_self _).trans_eq (abs_pow _ _)
          _ ≤ X C ^ l := pow_le_pow_of_le_one (hX C).1 (hX C).2 (hdegree S hS)
      _ ≤ q ^ l + probability (fun C ↦ q < X C) := Lax323828.FiniteProbability.bounded_power_mean X hX q hq l
      _ ≤ K := add_le_add (le_refl _) (normalized_correlation_tail n hn hN B q hq)
  rw [normalized_second_moment n hN]
  calc
    _ ≤ ∑ S ∈ supports, c S ^ 2 * K :=
      Finset.sum_le_sum fun S hS ↦ mul_le_mul_of_nonneg_left (hterm S hS) (sq_nonneg _)
    _ = (∑ S ∈ supports, c S ^ 2) * K := (Finset.sum_mul ..).symm
    _ ≤ 1 * K := mul_le_mul_of_nonneg_right henergy hK
    _ = K := one_mul _

/--
---
conclusion: Lax323828.HighDegreeSoundness.tail_bound
---
Apply the even-moment tail inequality with exponent two.
-/
theorem high_degree_tail {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (supports : Finset (Finset ι)) (c : Finset ι → ℝ) (l : ℕ)
    (hdegree : ∀ S ∈ supports, l ≤ S.card) (henergy : ∑ S ∈ supports, c S ^ 2 ≤ 1)
    (q : ℝ) (hq : 0 ≤ q) (a : ℝ) (ha : 0 < a) :
    probability (fun f : ι → κ ↦ a ≤ normalizedSum supports c n f) ≤
      (q ^ l + 2 * (Fintype.card κ + 1 : ℝ) *
        Real.exp (-(Fintype.card κ : ℝ) * q ^ 2 / 2)) / a ^ 2 := by
  apply (Lax323828.FiniteProbability.even_moment_bound _ a ha 2 (by decide)).trans
  exact div_le_div_of_nonneg_right
    (Lax323828.HighDegreeSoundness.second_moment_bound n hn hN supports c l hdegree henergy q hq) (sq_nonneg a)

end Lax323828Proofs
