import Lax253009.HigherMoments
import Lax253009Proofs.ProductMoments

namespace Lax253009Proofs

open scoped BigOperators
open Lax253009.HigherMoments

/--
---
conclusion: Lax253009.HigherMoments.factorization
---
Reorder the product by coordinates, then use independence of the labels.
-/
theorem higher_moment_factorization {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] {m : ℕ} (S : Fin m → Finset ι) (B : Fin m → κ → ℝ) :
    (𝔼 f : ι → κ, ∏ j, ∏ i ∈ S j, B j (f i)) =
      ∏ i, (𝔼 z, ∏ j with i ∈ S j, B j z) := by
  classical
  have hprod (f : ι → κ) : (∏ j, ∏ i ∈ S j, B j (f i)) =
      ∏ i, ∏ j, if i ∈ S j then B j (f i) else 1 := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    simp
  simp_rw [hprod]
  rw [independent_product_average (fun (i : ι) (z : κ) ↦
    ∏ j, if i ∈ S j then B j z else 1)]
  simp only [Finset.prod_filter]

/--
---
conclusion: Lax253009.HigherMoments.singleton_cancellation
---
The unique-occurrence coordinate contributes the mean of one balanced predicate.
-/
theorem higher_moment_singleton {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] {m : ℕ} (S : Fin m → Finset ι) (B : Fin m → κ → ℝ)
    (hbalanced : ∀ j, (𝔼 z, B j z) = 0) (i : ι) (j : Fin m)
    (hij : i ∈ S j) (hunique : ∀ j', i ∈ S j' → j' = j) :
    (𝔼 f : ι → κ, ∏ j, ∏ i ∈ S j, B j (f i)) = 0 := by
  classical
  rw [higher_moment_factorization]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hfilter : (Finset.univ.filter fun j' ↦ i ∈ S j') = {j} := by
    ext j'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hunique j', fun h ↦ h ▸ hij⟩
  simp [hfilter, hbalanced]

/--
---
conclusion: Lax253009.HigherMoments.double_cover_union_bound
---
Count incidences first by points of the union and then by supports.
-/
theorem double_cover_card_bound {ι : Type} [DecidableEq ι] {m : ℕ}
    (S : Fin m → Finset ι) (hS : DoubleCover S) :
    2 * (Finset.univ.biUnion S).card ≤ ∑ j, (S j).card := by
  classical
  let U := Finset.univ.biUnion S
  have hinc : (∑ i ∈ U, (Finset.univ.filter fun j ↦ i ∈ S j).card) =
      ∑ j, (S j).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_filter]
    have heq : U.filter (fun i ↦ i ∈ S j) = S j := by
      ext i
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun hi ↦ ⟨Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩, hi⟩⟩
    rw [heq]
  calc
    2 * U.card = ∑ _i ∈ U, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ U, (Finset.univ.filter fun j ↦ i ∈ S j).card :=
      Finset.sum_le_sum fun i hi ↦ hS i hi
    _ = _ := hinc

end Lax253009Proofs
