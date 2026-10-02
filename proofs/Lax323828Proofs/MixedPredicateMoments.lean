import Lax323828.MixedPredicateMoments
import Lax323828Proofs.BalancedPredicates
import Lax323828Proofs.HigherMoments
import Mathlib.Logic.Equiv.Prod

namespace Lax323828Proofs

open Lax323828.BooleanFourier Lax323828.BalancedPredicates Lax323828.FiniteProbability
open scoped BigOperators Classical

theorem balanced_predicates_nonempty {κ : Type} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hN : Fintype.card κ = 2 * n) : Nonempty (predicates κ n) := by
  have hp : (predicates κ n).Nonempty := by
    rw [← Finset.card_pos, Lax323828.BalancedPredicates.count, hN]
    exact Nat.choose_pos (by omega)
  exact ⟨⟨hp.choose, hp.choose_spec⟩⟩

private theorem balanced_weighted_sum_tail {κ : Type} [Fintype κ] [DecidableEq κ]
    [Nonempty κ] (n : ℕ) (hN : Fintype.card κ = 2 * n)
    (a : κ → ℝ) (ha : ∀ z, |a z| ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    probability (fun B : predicates κ n ↦ t ≤ |∑ z, a z * sign (B.val z)|) ≤
      2 * (Fintype.card κ + 1 : ℝ) * Real.exp (-t ^ 2 / (2 * Fintype.card κ)) := by
  have hp : Nonempty (predicates κ n) := balanced_predicates_nonempty n hN
  have hs : (predicates κ n).Nonempty := ⟨(Classical.choice hp).val, (Classical.choice hp).property⟩
  have hM : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hsize : (Fintype.card (Cube κ) : ℝ) ≤ (Fintype.card κ + 1 : ℝ) * (predicates κ n).card := by
    exact_mod_cast Lax323828.BalancedPredicates.central_mass n hN
  have hvar : ∑ z, a z ^ 2 ≤ (Fintype.card κ : ℝ) := by
    calc
      _ ≤ ∑ _z : κ, (1 : ℝ) := Finset.sum_le_sum fun z _ ↦ (sq_le_one_iff_abs_le_one _).mpr (ha z)
      _ = _ := by simp
  calc
    _ ≤ (Fintype.card κ + 1 : ℝ) * probability (fun B : Cube κ ↦
        t ≤ |∑ z, a z * sign (B z)|) :=
      Lax323828.FiniteProbability.restriction_bound (α := Cube κ) (predicates κ n) hs _ hsize _
    _ ≤ (Fintype.card κ + 1 : ℝ) * (2 * Real.exp (-t ^ 2 / (2 * Fintype.card κ))) :=
      mul_le_mul_of_nonneg_left (Lax323828.ExponentialBounds.rademacher_abs_tail a _ hM hvar t ht) (by positivity)
    _ = _ := by ring

private theorem balanced_weighted_tail {κ : Type} [Fintype κ] [DecidableEq κ]
    [Nonempty κ] (n : ℕ) (hN : Fintype.card κ = 2 * n)
    (a : κ → ℝ) (ha : ∀ z, |a z| ≤ 1) (q : ℝ) (hq : 0 ≤ q) :
    probability (fun B : predicates κ n ↦ q < |𝔼 z, a z * sign (B.val z)|) ≤
      2 * (Fintype.card κ + 1 : ℝ) * Real.exp (-(Fintype.card κ : ℝ) * q ^ 2 / 2) := by
  have hM : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ probability (fun B : predicates κ n ↦
        (Fintype.card κ : ℝ) * q ≤ |∑ z, a z * sign (B.val z)|) := by
      apply Lax323828.FiniteProbability.monotone
      intro B hB
      rw [Fintype.expect_eq_sum_div_card, abs_div, abs_of_pos hM] at hB
      simpa only [mul_comm q] using ((lt_div_iff₀ hM).mp hB).le
    _ ≤ 2 * (Fintype.card κ + 1 : ℝ) *
        Real.exp (-((Fintype.card κ : ℝ) * q) ^ 2 / (2 * Fintype.card κ)) :=
      balanced_weighted_sum_tail n hN a ha _ (mul_nonneg hM.le hq)
    _ = _ := by
      congr 2
      field_simp

private noncomputable def jointCorrelation {κ α : Type} [Fintype κ] [DecidableEq κ]
    (J : Finset α) {n : ℕ} (B : α → predicates κ n) : ℝ :=
  𝔼 z, ∏ j ∈ J, sign ((B j).val z)

private theorem joint_correlation_tail {κ α : Type} [Fintype κ] [DecidableEq κ]
    [Nonempty κ] [Fintype α] [DecidableEq α]
    (n : ℕ) (hN : Fintype.card κ = 2 * n) (J : Finset α) (hJ : J.Nonempty)
    (q : ℝ) (hq : 0 ≤ q) :
    probability (fun B : α → predicates κ n ↦ q < |jointCorrelation (n := n) J B|) ≤
      2 * (Fintype.card κ + 1 : ℝ) * Real.exp (-(Fintype.card κ : ℝ) * q ^ 2 / 2) := by
  have hp : Nonempty (predicates κ n) := balanced_predicates_nonempty n hN
  obtain ⟨j, hj⟩ := hJ
  let E := Equiv.funSplitAt j (predicates κ n)
  let event := fun B : α → predicates κ n ↦ q < |jointCorrelation (n := n) J B|
  rw [finite_probability_indicator]
  have he : (𝔼 B : α → predicates κ n, if event B then (1 : ℝ) else 0) =
      (𝔼 C : predicates κ n, 𝔼 D : {k // k ≠ j} → predicates κ n,
        if event (E.symm (C, D)) then (1 : ℝ) else 0) := by
    rw [← Finset.expect_product', Finset.univ_product_univ]
    exact Fintype.expect_equiv E _ _ (fun _ ↦ by simp)
  rw [he, Finset.expect_comm]
  apply Finset.expect_le Finset.univ_nonempty
  intro D _
  let C₀ := Classical.choice hp
  let a : κ → ℝ := fun z ↦ ∏ k ∈ J.erase j, sign (((E.symm (C₀, D)) k).val z)
  have ha (z : κ) : |a z| ≤ 1 := by
    dsimp [a]
    rw [Finset.abs_prod]
    have hs (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]
    simp [hs]
  have hc (C : predicates κ n) : jointCorrelation (n := n) J (E.symm (C, D)) =
      (𝔼 z, a z * sign (C.val z)) := by
    unfold jointCorrelation
    apply Finset.expect_congr rfl
    intro z _
    rw [← Finset.prod_erase_mul J _ hj]
    have hsame : (∏ k ∈ J.erase j, sign (((E.symm (C, D)) k).val z)) = a z := by
      apply Finset.prod_congr rfl
      intro k hk
      have hkj := (Finset.mem_erase.mp hk).1
      simp [E, Equiv.funSplitAt, Equiv.piSplitAt, hkj]
    rw [hsame]
    simp [E, Equiv.funSplitAt, Equiv.piSplitAt]
  change (𝔼 C : predicates κ n, if q < |jointCorrelation (n := n) J (E.symm (C, D))| then (1 : ℝ) else 0) ≤ _
  simp_rw [hc]
  rw [← finite_probability_indicator]
  exact balanced_weighted_tail n hN a ha q hq

private theorem joint_correlation_abs_le_one {κ α : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (J : Finset α) {n : ℕ} (B : α → predicates κ n) : |jointCorrelation (n := n) J B| ≤ 1 := by
  unfold jointCorrelation
  apply (Finset.abs_expect_le _ _).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro z _
  rw [Finset.abs_prod]
  have hs (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]
  simp [hs]

/--
---
conclusion: Lax323828.MixedPredicateMoments.bound
---
All nonempty subcollections simultaneously have small correlation outside
an event controlled by a union bound. Factor the mixed moment over its
coordinate union and bound each factor by q on that good event.
-/
theorem mixed_predicate_moment_bound {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (n : ℕ) (_hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (m : ℕ) (S : Fin m → Finset ι) (q : ℝ) (hq : 0 ≤ q) :
    |𝔼 B : Fin m → predicates κ n, 𝔼 f : ι → κ,
        ∏ j, ∏ i ∈ S j, sign ((B j).val (f i))| ≤
      q ^ (Finset.univ.biUnion S).card + (2 : ℝ) ^ m *
        (2 * (Fintype.card κ + 1 : ℝ) * Real.exp (-(Fintype.card κ : ℝ) * q ^ 2 / 2)) := by
  have : Nonempty (predicates κ n) := balanced_predicates_nonempty n hN
  let U := Finset.univ.biUnion S
  let J : ι → Finset (Fin m) := fun i ↦ Finset.univ.filter fun j ↦ i ∈ S j
  let R : (Fin m → predicates κ n) → ℝ := fun B ↦
    𝔼 f : ι → κ, ∏ j, ∏ i ∈ S j, sign ((B j).val (f i))
  let bad := fun B : Fin m → predicates κ n ↦
    ∃ T : Finset (Fin m), T.Nonempty ∧ q < |jointCorrelation (n := n) T B|
  let C := 2 * (Fintype.card κ + 1 : ℝ) * Real.exp (-(Fintype.card κ : ℝ) * q ^ 2 / 2)
  have hC : 0 ≤ C := by positivity
  have hprob : probability bad ≤ (2 : ℝ) ^ m * C := by
    calc
      _ ≤ ∑ T : Finset (Fin m), probability (fun B : Fin m → predicates κ n ↦
          T.Nonempty ∧ q < |jointCorrelation (n := n) T B|) := Lax323828.FiniteProbability.finite_union_bound _
      _ ≤ ∑ _T : Finset (Fin m), C := by
        apply Finset.sum_le_sum
        intro T _
        by_cases hT : T.Nonempty
        · simpa only [hT, true_and] using joint_correlation_tail n hN T hT q hq
        · simpa [hT, probability] using hC
      _ = _ := by simp [Fintype.card_finset]
  have hfactor (B : Fin m → predicates κ n) : R B = ∏ i ∈ U, jointCorrelation (n := n) (J i) B := by
    dsimp only [R]
    rw [Lax323828.HigherMoments.factorization S (fun j z ↦ sign ((B j).val z))]
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    have hz : J i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      exact hi (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩)
    change jointCorrelation (n := n) (J i) B = 1
    simp [hz, jointCorrelation]
  have hpoint (B : Fin m → predicates κ n) :
      |R B| ≤ q ^ U.card + if bad B then (1 : ℝ) else 0 := by
    rw [hfactor, Finset.abs_prod]
    by_cases hb : bad B
    · rw [if_pos hb]
      have hprod : (∏ i ∈ U, |jointCorrelation (n := n) (J i) B|) ≤ 1 :=
        Finset.prod_le_one (fun _ _ ↦ abs_nonneg _) (fun _ _ ↦ joint_correlation_abs_le_one _ _)
      linarith [pow_nonneg hq U.card]
    · rw [if_neg hb, add_zero, ← Finset.prod_const]
      apply Finset.prod_le_prod
      · intro i _
        exact abs_nonneg _
      · intro i hi
        have hj : (J i).Nonempty := by
          obtain ⟨j, _, hij⟩ := Finset.mem_biUnion.mp hi
          exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
        exact le_of_not_gt fun h ↦ hb ⟨J i, hj, h⟩
  calc
    _ ≤ 𝔼 B, |R B| := Finset.abs_expect_le _ _
    _ ≤ 𝔼 B, (q ^ U.card + if bad B then (1 : ℝ) else 0) :=
      Finset.expect_le_expect fun B _ ↦ hpoint B
    _ = q ^ U.card + probability bad := by
      rw [Finset.expect_add_distrib, Fintype.expect_const, finite_probability_indicator]
    _ ≤ _ := add_le_add (le_refl _) hprob

end Lax323828Proofs
