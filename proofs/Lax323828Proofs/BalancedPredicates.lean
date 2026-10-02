import Lax323828.BalancedPredicates
import Lax323828Proofs.ExponentialBounds

namespace Lax323828Proofs

open Lax323828.BooleanFourier Lax323828.FiniteProbability Lax323828.BalancedPredicates
open scoped BigOperators

/--
---
conclusion: Lax323828.BalancedPredicates.count
---
Map a predicate to its set of true inputs, a bijection with n-element subsets.
-/
theorem balanced_predicate_count {κ : Type} [Fintype κ] [DecidableEq κ] (n : ℕ) :
    (predicates κ n).card = (Fintype.card κ).choose n := by
  classical
  rw [← Finset.card_univ, ← Finset.card_powersetCard]
  refine Finset.card_bij (fun B _ ↦ Finset.univ.filter fun z ↦ B z = true) ?_ ?_ ?_
  · intro B hB
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hB).2⟩
  · intro B _ C _ heq
    funext z
    have hm := Finset.ext_iff.mp heq z
    simpa using hm
  · intro S hS
    refine ⟨fun z ↦ decide (z ∈ S), ?_, ?_⟩
    · simp [predicates, (Finset.mem_powersetCard.mp hS).2]
    · ext z
      simp

/--
---
conclusion: Lax323828.BalancedPredicates.central_mass
---
The largest binomial layer has at least the average size of the N+1 layers.
-/
theorem balanced_predicate_mass {κ : Type} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hN : Fintype.card κ = 2 * n) :
    Fintype.card (Cube κ) ≤ (Fintype.card κ + 1) * (predicates κ n).card := by
  rw [Lax323828.BalancedPredicates.count, Fintype.card_fun, Fintype.card_bool, hN]
  convert Nat.four_pow_le_two_mul_add_one_mul_central_binom n using 1
  rw [pow_mul]
  norm_num

/--
---
conclusion: Lax323828.BalancedPredicates.absolute_correlation_tail
---
Condition the independent-sign tail bound on the central binomial layer.
-/
theorem balanced_correlation_tail {κ : Type} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (G : Cube κ) (t : ℝ) (ht : 0 ≤ t) :
    probability (fun B : predicates κ n ↦ t ≤ |∑ z, sign (G z) * sign (B.val z)|) ≤
      2 * (Fintype.card κ + 1 : ℝ) * Real.exp (-t ^ 2 / (2 * Fintype.card κ)) := by
  classical
  have hnonempty : (predicates κ n).Nonempty := by
    rw [← Finset.card_pos, Lax323828.BalancedPredicates.count, hN]
    exact Nat.choose_pos (by omega)
  have hsize : (Fintype.card (Cube κ) : ℝ) ≤
      (Fintype.card κ + 1 : ℝ) * (predicates κ n).card := by
    exact_mod_cast Lax323828.BalancedPredicates.central_mass n hN
  have hv : (0 : ℝ) < Fintype.card κ := by rw [hN]; positivity
  have hvar : ∑ z, sign (G z) ^ 2 ≤ (Fintype.card κ : ℝ) := by
    have hz (z : κ) : sign (G z) ^ 2 = 1 := by cases G z <;> norm_num [sign]
    simp [hz]
  calc
    _ ≤ (Fintype.card κ + 1 : ℝ) *
        probability (fun B : Cube κ ↦ t ≤ |∑ z, sign (G z) * sign (B z)|) :=
      Lax323828.FiniteProbability.restriction_bound _ hnonempty _ hsize _
    _ ≤ (Fintype.card κ + 1 : ℝ) *
        (2 * Real.exp (-t ^ 2 / (2 * Fintype.card κ))) :=
      mul_le_mul_of_nonneg_left (Lax323828.ExponentialBounds.rademacher_abs_tail _ _ hv hvar t ht) (by positivity)
    _ = _ := by ring

end Lax323828Proofs
