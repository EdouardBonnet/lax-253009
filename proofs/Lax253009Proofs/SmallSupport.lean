import Lax253009.SmallSupport
import Mathlib.Tactic

namespace Lax253009Proofs

open Lax253009.SmallSupport

/--
---
conclusion: Lax253009.SmallSupport.decodingSet_bound
---
Bound the union by the sum of support sizes, charge each support at least
ℓδ squared mass, and use the total squared-mass bound.
-/
theorem small_support_bound {n : ℕ} (c : Finset (Fin n) → ℝ) (l : ℕ)
    (δ : ℝ) (hδ : 0 < δ) (henergy : ∑ a, c a ^ 2 ≤ 1) :
    ((decodingSet c l δ).card : ℝ) ≤ 1 / δ := by
  classical
  have hcard : (decodingSet c l δ).card ≤ (largeSets c l δ).card * l := by
    apply Finset.card_biUnion_le_card_mul
    intro a ha
    exact (Finset.mem_filter.mp ha).2.1
  have hmass : ((largeSets c l δ).card : ℝ) * ((l : ℝ) * δ) ≤
      ∑ a ∈ largeSets c l δ, c a ^ 2 := by
    calc
      _ = ∑ _a ∈ largeSets c l δ, (l : ℝ) * δ := by simp
      _ ≤ _ := Finset.sum_le_sum fun a ha ↦ (Finset.mem_filter.mp ha).2.2
  have hsub : (∑ a ∈ largeSets c l δ, c a ^ 2) ≤ ∑ a, c a ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ ↦ sq_nonneg (c a))
  apply (le_div_iff₀ hδ).mpr
  have hcast : ((decodingSet c l δ).card : ℝ) ≤
      ((largeSets c l δ).card : ℝ) * (l : ℝ) := by exact_mod_cast hcard
  calc
    ((decodingSet c l δ).card : ℝ) * δ ≤
        (((largeSets c l δ).card : ℝ) * (l : ℝ)) * δ :=
      mul_le_mul_of_nonneg_right hcast hδ.le
    _ = ((largeSets c l δ).card : ℝ) * ((l : ℝ) * δ) := mul_assoc _ _ _
    _ ≤ ∑ a ∈ largeSets c l δ, c a ^ 2 := hmass
    _ ≤ 1 := hsub.trans henergy

end Lax253009Proofs
