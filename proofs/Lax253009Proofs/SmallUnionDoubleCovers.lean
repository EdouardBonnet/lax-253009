import Lax253009.SmallUnionDoubleCovers
import Lax253009Proofs.DoubleCoverBounds
import Mathlib.Logic.Equiv.Prod

namespace Lax253009Proofs

open Lax253009.HigherMoments
open scoped BigOperators
open scoped Classical

private theorem double_cover_reindex {ι α β : Type} [DecidableEq ι]
    [Fintype α] [Fintype β] (e : α ≃ β) (S : β → Finset ι) :
    DoubleCover (S ∘ e) ↔ DoubleCover S := by
  classical
  have hu : Finset.univ.biUnion (S ∘ e) = Finset.univ.biUnion S := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Function.comp_apply]
    exact ⟨fun ⟨a, ha⟩ ↦ ⟨e a, ha⟩, fun ⟨b, hb⟩ ↦ ⟨e.symm b, by simpa using hb⟩⟩
  have hc (i : ι) : (Finset.univ.filter fun a ↦ i ∈ S (e a)).card =
      (Finset.univ.filter fun b ↦ i ∈ S b).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
  simp only [DoubleCover, hu, Function.comp_apply, hc]

private theorem double_cover_weight_fintype {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (c : Finset ι → ℝ) (l : ℕ) (hc : ∀ S, 0 ≤ c S)
    (hdegree : ∀ S, l < S.card → c S = 0) (henergy : ∑ S, c S ^ 2 ≤ 1) :
    (∑ S : α → Finset ι, if DoubleCover S then ∏ j, c (S j) else 0) ≤
      1 + (3 : ℝ) ^ (l * (2 * Fintype.card α + 1) * 2 ^ Fintype.card α) := by
  classical
  let e := Fintype.equivFin α
  let E : (α → Finset ι) ≃ (Fin (Fintype.card α) → Finset ι) :=
    Equiv.arrowCongr e (Equiv.refl _)
  have he : (∑ S : α → Finset ι, if DoubleCover S then ∏ j, c (S j) else 0) =
      Lax253009.DoubleCoverBounds.weight c (Fintype.card α) := by
    unfold Lax253009.DoubleCoverBounds.weight
    apply Fintype.sum_equiv E
    intro S
    have hdc : DoubleCover (E S) ↔ DoubleCover S :=
      double_cover_reindex e.symm S
    rw [hdc]
    split_ifs
    · exact Fintype.prod_equiv e (fun j ↦ c (S j)) (fun j ↦ c (E S j)) (by intro j; simp [E])
    · rfl
  rw [he]
  exact Lax253009.DoubleCoverBounds.bound c l _ hc hdegree henergy

private theorem subset_coefficient_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (U : Finset ι) (δ : ℝ) (hsmall : ∀ S, c S ≤ δ) :
    (∑ S, if S ⊆ U then c S else 0) ≤ (2 : ℝ) ^ U.card * δ := by
  calc
    _ = ∑ S ∈ U.powerset, c S := by
      rw [← Finset.sum_filter]
      congr 1
      ext S
      simp
    _ ≤ ∑ _S ∈ U.powerset, δ := Finset.sum_le_sum fun S _ ↦ hsmall S
    _ = _ := by simp

private theorem completion_weight_bound {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (c : Finset ι → ℝ) (U : Finset ι) (δ : ℝ)
    (hc : ∀ S, 0 ≤ c S) (hsmall : ∀ S, c S ≤ δ) :
    (∑ B : α → Finset ι, if ∀ j, B j ⊆ U then ∏ j, c (B j) else 0) ≤
      ((2 : ℝ) ^ U.card * δ) ^ Fintype.card α := by
  have he (B : α → Finset ι) :
      (if ∀ j, B j ⊆ U then ∏ j, c (B j) else 0) =
        ∏ j, if B j ⊆ U then c (B j) else 0 := by
    split_ifs with hB
    · simp [hB]
    · obtain ⟨j, hj⟩ := not_forall.mp hB
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
  simp_rw [he]
  rw [← Fintype.prod_sum (fun (_ : α) S ↦ if S ⊆ U then c S else 0)]
  simp only [Finset.prod_const]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun S _ ↦ by split_ifs; exact hc S; exact le_rfl)
    (subset_coefficient_sum c U δ hsmall) _

private def selectedGood {ι α : Type} [Fintype α] [DecidableEq α] [DecidableEq ι]
    (J : Finset α) (S : α → Finset ι) (t : ℕ) : Prop :=
  DoubleCover (fun j : J ↦ S j) ∧
    (Finset.univ.biUnion fun j : J ↦ S j).card = t ∧
    ∀ j : {j // j ∉ J}, S j ⊆ Finset.univ.biUnion (fun j : J ↦ S j)

private theorem fixed_selection_bound {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (J : Finset α) (c : Finset ι → ℝ) (l t : ℕ) (δ : ℝ)
    (hc : ∀ S, 0 ≤ c S) (hsmall : ∀ S, c S ≤ δ) (hδ : 0 ≤ δ)
    (hdegree : ∀ S, l < S.card → c S = 0) (henergy : ∑ S, c S ^ 2 ≤ 1) :
    (∑ S : α → Finset ι, if selectedGood J S t then ∏ j, c (S j) else 0) ≤
      ((2 : ℝ) ^ t * δ) ^ (Fintype.card α - J.card) *
        (1 + (3 : ℝ) ^ (l * (2 * J.card + 1) * 2 ^ J.card)) := by
  let E := Equiv.piEquivPiSubtypeProd (fun j : α ↦ j ∈ J) (fun _ ↦ Finset ι)
  let K := ((2 : ℝ) ^ t * δ) ^ (Fintype.card α - J.card)
  have hK : 0 ≤ K := by positivity
  have hsplit : (∑ S : α → Finset ι, if selectedGood J S t then ∏ j, c (S j) else 0) =
      ∑ A : J → Finset ι, ∑ B : {j // j ∉ J} → Finset ι,
        if DoubleCover A ∧ (Finset.univ.biUnion A).card = t ∧
            ∀ j, B j ⊆ Finset.univ.biUnion A
        then (∏ j, c (A j)) * ∏ j, c (B j) else 0 := by
    rw [← Fintype.sum_prod_type (fun p : (J → Finset ι) × ({j // j ∉ J} → Finset ι) ↦
      if DoubleCover p.1 ∧ (Finset.univ.biUnion p.1).card = t ∧
          ∀ j, p.2 j ⊆ Finset.univ.biUnion p.1
      then (∏ j, c (p.1 j)) * ∏ j, c (p.2 j) else 0)]
    apply Fintype.sum_equiv E
    intro S
    simp only [E, Equiv.piEquivPiSubtypeProd_apply, selectedGood]
    have hp := (Fintype.prod_subtype_mul_prod_subtype (fun j : α ↦ j ∈ J) (fun j ↦ c (S j))).symm
    rw [hp]
    congr!
    congr 1
  rw [hsplit]
  calc
    _ ≤ ∑ A : J → Finset ι, K * (if DoubleCover A then ∏ j, c (A j) else 0) := by
      apply Finset.sum_le_sum
      intro A _
      by_cases hA : DoubleCover A ∧ (Finset.univ.biUnion A).card = t
      · simp only [hA.1, hA.2, true_and, if_true]
        have he (B : {j // j ∉ J} → Finset ι) :
            (if ∀ j, B j ⊆ Finset.univ.biUnion A then (∏ j, c (A j)) * ∏ j, c (B j) else 0) =
              (∏ j, c (A j)) * (if ∀ j, B j ⊆ Finset.univ.biUnion A then ∏ j, c (B j) else 0) := by
          split_ifs <;> simp
        simp_rw [he]
        rw [← Finset.mul_sum, mul_comm K]
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun j _ ↦ hc _)
        have hb := completion_weight_bound (α := {j // j ∉ J}) c (Finset.univ.biUnion A) δ hc hsmall
        rw [hA.2] at hb
        simpa only [K, Fintype.card_subtype_compl, Fintype.card_coe] using hb
      · have hz : ∀ B : {j // j ∉ J} → Finset ι,
            ¬ (DoubleCover A ∧ (Finset.univ.biUnion A).card = t ∧ ∀ j, B j ⊆ Finset.univ.biUnion A) :=
          fun _ h ↦ hA ⟨h.1, h.2.1⟩
        simp only [hz, if_false, Finset.sum_const_zero]
        exact mul_nonneg hK (by split_ifs; exact Finset.prod_nonneg fun j _ ↦ hc _; exact le_rfl)
    _ = K * ∑ A : J → Finset ι, if DoubleCover A then ∏ j, c (A j) else 0 :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hK
      simpa using double_cover_weight_fintype (α := J) c l hc hdegree henergy

private theorem exists_good_selection {ι : Type} [DecidableEq ι] {m t : ℕ}
    (S : Fin m → Finset ι) (hS : DoubleCover S)
    (ht : (Finset.univ.biUnion S).card = t) (hmt : 2 * t ≤ m) :
    ∃ J : Finset (Fin m), J.card = 2 * t ∧ selectedGood J S t := by
  obtain ⟨J, hJ, hcover⟩ := Lax253009.HigherMoments.double_subcover S hS (2 * t) (by omega) hmt
  have hu : Finset.univ.biUnion (fun j : J ↦ S j) = Finset.univ.biUnion S := by
    apply Finset.Subset.antisymm
    · intro i hi
      obtain ⟨j, _, hij⟩ := Finset.mem_biUnion.mp hi
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hij⟩
    · intro i hi
      obtain ⟨j, hj⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) (hcover i hi))
      obtain ⟨hjJ, hij⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_biUnion.mpr ⟨⟨j, hjJ⟩, Finset.mem_univ _, hij⟩
  refine ⟨J, hJ, ?_, by rw [hu]; exact ht, ?_⟩
  · intro i hi
    have he : (Finset.univ.filter fun j : J ↦ i ∈ S j).card =
        (J.filter fun j ↦ i ∈ S j).card := by
      apply Finset.card_bij (fun j _ ↦ j.val)
      · intro j hj
        exact Finset.mem_filter.mpr ⟨j.property, (Finset.mem_filter.mp hj).2⟩
      · intro a _ b _ h
        exact Subtype.ext h
      · intro j hj
        obtain ⟨hjJ, hij⟩ := Finset.mem_filter.mp hj
        exact ⟨⟨j, hjJ⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩
    rw [he]
    exact hcover i (hu ▸ hi)
  · intro j i hi
    rw [hu]
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩

/--
---
conclusion: Lax253009.SmallUnionDoubleCovers.bound
---
Extract a double subcover of size 2t, sum over the choices of its positions,
and bound each remaining support by the total coefficient mass on subsets
of its union. The extracted tuples are controlled by the double-cover bound.
-/
theorem small_union_double_cover_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (l m t : ℕ) (δ : ℝ)
    (hc : ∀ S, 0 ≤ c S) (hsmall : ∀ S, c S ≤ δ) (hδ : 0 ≤ δ)
    (hdegree : ∀ S, l < S.card → c S = 0) (henergy : ∑ S, c S ^ 2 ≤ 1)
    (hmt : 2 * t ≤ m) :
    Lax253009.SmallUnionDoubleCovers.weight c m t ≤
      (2 : ℝ) ^ m * ((2 : ℝ) ^ t * δ) ^ (m - 2 * t) *
        (1 + (3 : ℝ) ^ (l * (4 * t + 1) * 2 ^ (2 * t))) := by
  let choices := (Finset.univ : Finset (Fin m)).powersetCard (2 * t)
  let K := ((2 : ℝ) ^ t * δ) ^ (m - 2 * t) *
    (1 + (3 : ℝ) ^ (l * (4 * t + 1) * 2 ^ (2 * t)))
  have hK : 0 ≤ K := by positivity
  have hcount : (choices.card : ℝ) ≤ (2 : ℝ) ^ m := by
    have hsub : choices ⊆ (Finset.univ : Finset (Fin m)).powerset := by
      intro J hJ
      exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hJ).1
    have hn : choices.card ≤ 2 ^ m := by simpa using Finset.card_le_card hsub
    exact_mod_cast hn
  unfold Lax253009.SmallUnionDoubleCovers.weight
  calc
    _ ≤ ∑ S : Fin m → Finset ι, ∑ J ∈ choices,
        if selectedGood J S t then ∏ j, c (S j) else 0 := by
      apply Finset.sum_le_sum
      intro S _
      have hn (J : Finset (Fin m)) :
          0 ≤ (if selectedGood J S t then ∏ j, c (S j) else 0) := by
        split_ifs
        · exact Finset.prod_nonneg fun j _ ↦ hc _
        · exact le_rfl
      split_ifs with hS
      · obtain ⟨J, hJ, hg⟩ := exists_good_selection S hS.1 hS.2 hmt
        have hmem : J ∈ choices := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hJ⟩
        simpa only [hg, if_true] using Finset.single_le_sum (fun J _ ↦ hn J) hmem
      · exact Finset.sum_nonneg fun J _ ↦ hn J
    _ = ∑ J ∈ choices, ∑ S : Fin m → Finset ι,
        if selectedGood J S t then ∏ j, c (S j) else 0 := Finset.sum_comm
    _ ≤ ∑ _J ∈ choices, K := by
      apply Finset.sum_le_sum
      intro J hJ
      have hj := (Finset.mem_powersetCard.mp hJ).2
      have hb := fixed_selection_bound J c l t δ hc hsmall hδ hdegree henergy
      simpa only [Fintype.card_fin, hj, show 2 * (2 * t) + 1 = 4 * t + 1 by omega, K] using hb
    _ = choices.card * K := by simp
    _ ≤ (2 : ℝ) ^ m * K := mul_le_mul_of_nonneg_right hcount hK
    _ = _ := by dsimp [K]; ring

end Lax253009Proofs
