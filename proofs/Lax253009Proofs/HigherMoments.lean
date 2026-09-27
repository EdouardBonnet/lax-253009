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
  rw [Lax253009.HigherMoments.factorization]
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

/--
---
conclusion: Lax253009.HigherMoments.double_subcover
---
Choose two distinct covering positions for each point, take their union,
and enlarge this selection to the requested cardinality. This extracts
the double subcover used in Lemma 4.16.
-/
theorem double_cover_subcover {ι : Type} [DecidableEq ι] {m : ℕ}
    (S : Fin m → Finset ι) (hS : DoubleCover S) (r : ℕ)
    (hr : 2 * (Finset.univ.biUnion S).card ≤ r) (hrm : r ≤ m) :
    ∃ J : Finset (Fin m), J.card = r ∧
      ∀ i ∈ Finset.univ.biUnion S, 2 ≤ (J.filter fun j ↦ i ∈ S j).card := by
  classical
  let U := Finset.univ.biUnion S
  have hex (i : U) : ∃ a : Fin m, ∃ b : Fin m, i.val ∈ S a ∧ i.val ∈ S b ∧ a ≠ b := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (hS i.val i.property)
    exact ⟨a, b, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, hab⟩
  choose a b ha hb hab using hex
  let J₀ := Finset.univ.biUnion fun i : U ↦ ({a i, b i} : Finset (Fin m))
  have hJ₀ : J₀.card ≤ 2 * U.card := by
    calc
      _ ≤ ∑ i : U, ({a i, b i} : Finset (Fin m)).card := Finset.card_biUnion_le
      _ = 2 * U.card := by simp [hab, Nat.mul_comm]
  obtain ⟨J, hsub, _, hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ J₀) (hJ₀.trans hr) (by simpa using hrm)
  refine ⟨J, hcard, ?_⟩
  intro i hi
  let u : U := ⟨i, hi⟩
  have hpair : ({a u, b u} : Finset (Fin m)) ⊆ J.filter (fun j ↦ i ∈ S j) := by
    intro j hj
    have hmem : j ∈ J := hsub (Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, hj⟩)
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ha u
    · rw [Finset.mem_singleton] at hj
      subst j
      exact hb u
  simpa [hab] using Finset.card_le_card hpair

end Lax253009Proofs
