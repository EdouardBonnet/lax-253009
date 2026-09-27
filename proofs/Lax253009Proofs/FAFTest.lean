import Lax253009.FAFTest
import Lax253009Proofs.ManyTableConsistency
import Lax253009Proofs.CNASoundness

namespace Lax253009Proofs

open Lax253009.LongCode Lax253009.CNASoundness Lax253009.FiniteProbability
open Lax253009.FAFTest Lax253009.ManyTableConsistency
open scoped BigOperators Classical

/--
---
conclusion: Lax253009.FAFTest.perfect_completeness
---
Consistent satisfying assignments satisfy every side condition, and genuine
long codes pass every corresponding CNA test.
-/
theorem faf_perfect_completeness {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (x : Word u) (y : Ω → Word w)
    (hvalid : ∀ ω, valid ω (y ω) = true) (hproject : ∀ ω, ρ ω (y ω) = x)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u) (f : Fin n → Fin s → Coordinate w) :
    Lax253009.FAFTest.Accepts ρ valid (evaluation x) (fun ω ↦ evaluation (y ω)) ω g f := by
  intro i
  apply Lax253009.LongCodeCorrectness.side_condition_completeness
  simp [condition, hvalid, hproject, evaluation]

/--
---
conclusion: Lax253009.FAFTest.acceptance_bound
---
Outside the union of CNA decoding failures, each accepting table has a
decoded assignment satisfying its side condition. Their projections agree
on all reference functions, so the many-table agreement bound applies.
-/
theorem faf_acceptance_bound {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (u w n s q : ℕ) (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (R : Table u) (A : Ω → Table w) (D : Ω → Finset (Word w))
    (B k : ℕ) (p δ : ℝ) (hp : 0 ≤ p)
    (hB : ∀ ω, (D ω).card ≤ B)
    (hdecode : ∀ ω h, probability (BadWithCondition (s := s) (A ω) (D ω) h) ≤ δ)
    (hpoint : ∀ x, probability (fun ω ↦ x ∈ projected ρ valid D ω) ≤ p)
    (hsmall : (n : ℝ) * B * p ≤ 1) :
    probability (fun z : ((Fin n → Ω) × (Fin q → Coordinate u)) ×
        (Fin n → Fin s → Coordinate w) ↦ Lax253009.FAFTest.Accepts ρ valid R A z.1.1 z.1.2 z.2) ≤
      n * δ + (2 : ℝ) ^ n * ((n : ℝ) * B * p) ^ (n - k) +
        (B : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ (k + 1)) ^ q := by
  let Z := (Fin n → Ω) × (Fin q → Coordinate u)
  let F := Fin n → Fin s → Coordinate w
  let bad := fun (z : Z) (f : F) ↦ ∃ i, BadWithCondition
    (A (z.1 i)) (D (z.1 i)) (condition ρ valid R (z.1 i) z.2) (f i)
  let good := fun z : Z ↦ Agreement (projected ρ valid D) q z.1 z.2
  have hbad : probability (fun z : Z × F ↦ bad z.1 z.2) ≤ n * δ := by
    apply finite_probability_product_bound
    intro z
    calc
      _ ≤ ∑ i : Fin n, probability (fun f : F ↦ BadWithCondition
          (A (z.1 i)) (D (z.1 i)) (condition ρ valid R (z.1 i) z.2) (f i)) :=
        Lax253009.FiniteProbability.finite_union_bound _
      _ ≤ ∑ _i : Fin n, δ := by
        apply Finset.sum_le_sum
        intro i _
        rw [finite_probability_evaluation i]
        exact hdecode _ _
      _ = _ := by simp
  have hgood : probability (fun z : Z × F ↦ good z.1) = probability good := by
    rw [finite_probability_product (fun z (_f : F) ↦ good z)]
    simp_rw [finite_probability_indicator]
    simp only [Fintype.expect_const]
  have hcover (z : Z × F) (hz : Lax253009.FAFTest.Accepts ρ valid R A z.1.1 z.1.2 z.2) :
      bad z.1 z.2 ∨ good z.1 := by
    by_cases hb : bad z.1 z.2
    · exact Or.inl hb
    right
    have hdecoded (i : Fin n) : ∃ y ∈ D (z.1.1 i),
        condition ρ valid R (z.1.1 i) z.1.2 y = true ∧ LooksLike (A (z.1.1 i)) (z.2 i) y := by
      by_contra h
      exact hb ⟨i, hz i, h⟩
    choose y hy hcond hlook using hdecoded
    have hc (i : Fin n) : valid (z.1.1 i) (y i) = true ∧
        ∀ j, z.1.2 j (ρ (z.1.1 i) (y i)) = R (z.1.2 j) := by
      simpa only [condition, Bool.and_eq_true, decide_eq_true_eq] using hcond i
    refine ⟨fun i ↦ ρ (z.1.1 i) (y i), fun i ↦ ?_, fun j ↦ ⟨R (z.1.2 j), fun i ↦ (hc i).2 j⟩⟩
    exact Finset.mem_image.mpr ⟨y i, Finset.mem_filter.mpr ⟨hy i, (hc i).1⟩, rfl⟩
  have hsize (ω : Ω) : (projected ρ valid D ω).card ≤ B :=
    Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (hB ω))
  have hagree := Lax253009.ManyTableConsistency.agreement_bound (ι := Fin n) (projected ρ valid D) B k q p hp
    hsize hpoint (by simpa only [Fintype.card_fin] using hsmall)
  simp only [Fintype.card_fin] at hagree
  calc
    _ ≤ probability (fun z : Z × F ↦ bad z.1 z.2 ∨ good z.1) := Lax253009.FiniteProbability.monotone _ _ hcover
    _ ≤ probability (fun z : Z × F ↦ bad z.1 z.2) + probability (fun z : Z × F ↦ good z.1) :=
      Lax253009.FiniteProbability.union_bound _ _
    _ ≤ n * δ + probability good := add_le_add hbad hgood.le
    _ ≤ _ := by linarith

end Lax253009Proofs
