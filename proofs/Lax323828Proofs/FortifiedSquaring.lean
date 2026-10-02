import Lax323828.FortifiedSquaring
import Lax323828Proofs.FiniteProbability

namespace Lax323828Proofs

open Lax323828 Lax323828.FortifiedSquaring Lax323828.FiniteProbability
open scoped BigOperators

private theorem agreement_indicator {B : Type} [Fintype B] [DecidableEq B]
    (p q : Prop) [Decidable p] [Decidable q] (b c : B) :
    ∑ a : B, (if (p ∧ b = a) ∧ (q ∧ c = a) then (1 : ℝ) else 0) =
      if p ∧ q ∧ b = c then 1 else 0 := by
  classical
  by_cases hp : p
  · by_cases hq : q
    · by_cases hbc : b = c
      · subst c; simp [hp, hq]
      · have hn (a : B) : ¬ ((p ∧ b = a) ∧ (q ∧ c = a)) :=
          fun h ↦ hbc (h.1.2.trans h.2.2.symm)
        simp [hn, hbc]
    · simp [hq]
  · simp [hp]

/--
---
conclusion: Lax323828.FortifiedSquaring.soundness
---
Fix the first random test and partition its successful answers by their
common projection. Each part is a rectangle in the second questions.
Apply fortification on each part and average; first-copy success is at
most the original soundness by fixing the second random test.
-/
theorem fortified_squaring_sound {Z W A B : Type} [Fintype Z] [Nonempty Z] [Fintype B]
    (G : Game Z W A B) (s v η : ℝ) (hv : 0 ≤ v)
    (hs : G.Sound s) (hfort : G.Fortified v η)
    (P Q : W × W → A × A) :
    probability (G.DoubleWins P Q) ≤ v * s + (Fintype.card B : ℝ) * η := by
  classical
  let First := fun z x ↦
    G.Test z (P (G.left z, G.left x)).1 (Q (G.right z, G.right x)).1
  let S := fun z b w ↦ G.validLeft z (P (G.left z, w)).1 = true ∧
    G.projectLeft z (P (G.left z, w)).1 = b
  let T := fun z b w ↦ G.validRight z (Q (G.right z, w)).1 = true ∧
    G.projectRight z (Q (G.right z, w)).1 = b
  have hpart (z : Z) :
      (∑ b : B, probability (fun x ↦ S z b (G.left x) ∧ T z b (G.right x))) =
        probability (First z) := by
    simp_rw [finite_probability_indicator]
    rw [← Finset.expect_sum_comm]
    apply Finset.expect_congr rfl
    intro x _
    convert agreement_indicator
      (G.validLeft z (P (G.left z, G.left x)).1 = true)
      (G.validRight z (Q (G.right z, G.right x)).1 = true)
      (G.projectLeft z (P (G.left z, G.left x)).1)
      (G.projectRight z (Q (G.right z, G.right x)).1) using 1
    all_goals
      first
      | rfl
      | exact congrArg (fun d : Decidable (First z x) ↦ @ite ℝ (First z x) d 1 0)
          (Subsingleton.elim _ _)
  have hp (z : Z) : probability (fun x ↦ G.DoubleWins P Q (z, x)) ≤
      v * probability (First z) + (Fintype.card B : ℝ) * η := by
    let E := fun b x ↦ G.Wins (fun w ↦ (P (G.left z, w)).2)
      (fun w ↦ (Q (G.right z, w)).2) x ∧ S z b (G.left x) ∧ T z b (G.right x)
    have he : probability (fun x ↦ G.DoubleWins P Q (z, x)) ≤
        ∑ b : B, probability (E b) := by
      apply le_trans (Lax323828.FiniteProbability.monotone _ _ ?_) (Lax323828.FiniteProbability.finite_union_bound E)
      rintro x ⟨hfirst, hsecond⟩
      refine ⟨G.projectLeft z (P (G.left z, G.left x)).1, hsecond,
        ⟨hfirst.1, rfl⟩, hfirst.2.1, hfirst.2.2.symm⟩
    calc
      _ ≤ _ := he
      _ ≤ ∑ b : B, (v * probability (fun x ↦ S z b (G.left x) ∧ T z b (G.right x)) + η) :=
        Finset.sum_le_sum fun b _ ↦ hfort _ _ _ _
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hpart]; simp
  have hfirst : (𝔼 z, probability (First z)) ≤ s := by
    simp_rw [finite_probability_indicator]
    rw [Finset.expect_comm]
    apply Finset.expect_le Finset.univ_nonempty
    intro x _
    have h := hs (fun w ↦ (P (w, G.left x)).1) (fun w ↦ (Q (w, G.right x)).1)
    rw [finite_probability_indicator] at h
    convert h using 1 <;> rfl
  rw [finite_probability_product (fun z x ↦ G.DoubleWins P Q (z, x))]
  calc
    _ ≤ 𝔼 z, (v * probability (First z) + (Fintype.card B : ℝ) * η) :=
      Finset.expect_le_expect fun z _ ↦ hp z
    _ = v * (𝔼 z, probability (First z)) + (Fintype.card B : ℝ) * η := by
      rw [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hfirst hv) le_rfl

end Lax323828Proofs
