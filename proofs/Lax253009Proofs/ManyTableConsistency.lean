import Lax253009.ManyTableConsistency
import Lax253009Proofs.FiniteProbability
import Mathlib.Logic.Equiv.Prod

namespace Lax253009Proofs

open Lax253009.FiniteProbability Lax253009.ManyTableConsistency
open scoped BigOperators Classical

private def Covered {ι Ω X : Type} (S : Ω → Finset X) (J : Finset ι)
    (w : ι → Ω) : Prop :=
  ∀ i, i ∉ J → ∃ j ∈ J, ∃ x ∈ S (w j), x ∈ S (w i)

private theorem low_diversity_representatives {ι Ω X : Type}
    [Fintype ι] [DecidableEq ι] [DecidableEq X]
    (S : Ω → Finset X) (k : ℕ) (w : ι → Ω) (hw : LowDiversity S k w) :
    ∃ J : Finset ι, J.card ≤ k ∧ Covered S J w := by
  obtain ⟨y, hy, hc⟩ := hw
  let R := Finset.univ.image y
  have hreps (x : R) : ∃ i, y i = x.val := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.property
    exact ⟨i, hi⟩
  choose rep hrep using hreps
  let J := Finset.univ.image rep
  have hJ : J.card ≤ k := (Finset.card_image_le.trans (by simpa [R] using hc))
  refine ⟨J, hJ, fun i _ ↦ ?_⟩
  let x : R := ⟨y i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  refine ⟨rep x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, y i, ?_, hy i⟩
  change x.val ∈ S (w (rep x))
  rw [← hrep x]
  exact hy (rep x)

private theorem random_set_meets {Ω X : Type} [Fintype Ω]
    (S : Ω → Finset X) (p : ℝ) (hpoint : ∀ x, probability (fun w ↦ x ∈ S w) ≤ p)
    (U : Finset X) :
    probability (fun w ↦ ∃ x ∈ U, x ∈ S w) ≤ U.card * p := by
  calc
    _ ≤ ∑ x ∈ U, probability (fun w ↦ x ∈ S w) := finite_probability_finset_union U _
    _ ≤ ∑ _x ∈ U, p := Finset.sum_le_sum (fun x _ ↦ hpoint x)
    _ = _ := by simp

private theorem covered_probability {ι Ω X : Type} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Nonempty Ω] [Fintype X] [DecidableEq X]
    (S : Ω → Finset X) (B : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hB : ∀ w, (S w).card ≤ B)
    (hpoint : ∀ x, probability (fun w ↦ x ∈ S w) ≤ p) (J : Finset ι) :
    probability (Covered S J) ≤ ((Fintype.card ι : ℝ) * B * p) ^ (Fintype.card ι - J.card) := by
  let E := Equiv.piEquivPiSubtypeProd (fun i : ι ↦ i ∈ J) (fun _ ↦ Ω)
  let U (v : J → Ω) := Finset.univ.biUnion (fun j : J ↦ S (v j))
  let Q := fun (v : J → Ω) (v' : {i : ι // i ∉ J} → Ω) ↦
    ∀ i, ∃ x ∈ U v, x ∈ S (v' i)
  have he : probability (Covered S J) =
      probability (fun z : (J → Ω) × ({i : ι // i ∉ J} → Ω) ↦ Q z.1 z.2) := by
    apply finite_probability_equiv E
    intro w
    dsimp [Covered, Q, U, E, Equiv.piEquivPiSubtypeProd]
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists, Subtype.forall]
    constructor
    · intro h i hi
      obtain ⟨j, hj, x, hx, hxi⟩ := h i hi
      exact ⟨x, ⟨j, hj, hx⟩, hxi⟩
    · intro h i hi
      obtain ⟨x, ⟨j, hj, hx⟩, hxi⟩ := h i hi
      exact ⟨j, hj, x, hx, hxi⟩
  rw [he]
  apply finite_probability_product_bound
  intro v
  have hU : (U v).card ≤ Fintype.card ι * B := by
    calc
      _ ≤ ∑ j : J, (S (v j)).card := Finset.card_biUnion_le
      _ ≤ ∑ _j : J, B := Finset.sum_le_sum (fun j _ ↦ hB (v j))
      _ = J.card * B := by simp
      _ ≤ _ := Nat.mul_le_mul_right B (Finset.card_le_univ J)
  have hq : probability (fun v' ↦ ∃ x ∈ U v, x ∈ S v') ≤ Fintype.card ι * B * p :=
    (random_set_meets S p hpoint (U v)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hU) hp)
  dsimp only [Q]
  rw [finite_probability_pi (fun (_i : {i : ι // i ∉ J}) v' ↦ ∃ x ∈ U v, x ∈ S v')]
  calc
    _ ≤ ∏ _i : {i : ι // i ∉ J}, ((Fintype.card ι : ℝ) * B * p) :=
      Finset.prod_le_prod (fun _ _ ↦ finite_probability_nonneg _) (fun _ _ ↦ hq)
    _ = _ := by simp [Fintype.card_subtype_compl]

/--
---
conclusion: Lax253009.ManyTableConsistency.low_diversity_bound
---
Choose one representative table for each selected value. Conditional on
these tables, all remaining independent tables must hit their union. Sum
over the at most 2^n possible representative sets.
-/
theorem many_tables_low_diversity {ι Ω X : Type} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Nonempty Ω] [Fintype X] [DecidableEq X]
    (S : Ω → Finset X) (B k : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hB : ∀ w, (S w).card ≤ B)
    (hpoint : ∀ x, probability (fun w ↦ x ∈ S w) ≤ p)
    (hsmall : (Fintype.card ι : ℝ) * B * p ≤ 1) :
    probability (LowDiversity (ι := ι) S k) ≤
      (2 : ℝ) ^ Fintype.card ι * ((Fintype.card ι : ℝ) * B * p) ^ (Fintype.card ι - k) := by
  let b := (Fintype.card ι : ℝ) * B * p
  have hb : 0 ≤ b := by dsimp [b]; positivity
  calc
    _ ≤ probability (fun w ↦ ∃ J : Finset ι, J.card ≤ k ∧ Covered S J w) :=
      Lax253009.FiniteProbability.monotone _ _ (low_diversity_representatives S k)
    _ ≤ ∑ J : Finset ι, probability (fun w ↦ J.card ≤ k ∧ Covered S J w) :=
      Lax253009.FiniteProbability.finite_union_bound _
    _ ≤ ∑ _J : Finset ι, b ^ (Fintype.card ι - k) := by
      apply Finset.sum_le_sum
      intro J _
      by_cases hJ : J.card ≤ k
      · simp only [hJ, true_and]
        exact (covered_probability S B p hp hB hpoint J).trans
          (pow_le_pow_of_le_one hb hsmall (Nat.sub_le_sub_left hJ _))
      · simpa [hJ, probability] using pow_nonneg hb (Fintype.card ι - k)
    _ = _ := by simp [b]

private theorem random_function_fixed_on {X : Type} [Fintype X] [DecidableEq X]
    (K : Finset X) (b : Bool) :
    probability (fun g : X → Bool ↦ ∀ x ∈ K, g x = b) = (1 / 2 : ℝ) ^ K.card := by
  have he (x : X) : probability (fun v : Bool ↦ x ∈ K → v = b) =
      if x ∈ K then (1 / 2 : ℝ) else 1 := by
    by_cases hx : x ∈ K
    · simp only [hx, true_implies, if_true]
      rw [finite_probability_indicator, Fintype.expect_eq_sum_div_card]
      cases b <;> norm_num [Fintype.sum_bool]
    · simp only [hx, false_implies, if_false]
      rw [finite_probability_indicator, Fintype.expect_const]
      simp
  rw [finite_probability_pi (fun x v ↦ x ∈ K → v = b)]
  simp_rw [he]
  simp

private theorem random_functions_monochromatic {X : Type} [Fintype X] [DecidableEq X]
    (K : Finset X) (q : ℕ) :
    probability (fun g : Fin q → X → Bool ↦ ∀ j, ∃ b, ∀ x ∈ K, g j x = b) ≤
      (2 * (1 / 2 : ℝ) ^ K.card) ^ q := by
  rw [finite_probability_pi (fun (_j : Fin q) (g : X → Bool) ↦ ∃ b, ∀ x ∈ K, g x = b)]
  have hone : probability (fun g : X → Bool ↦ ∃ b, ∀ x ∈ K, g x = b) ≤
      2 * (1 / 2 : ℝ) ^ K.card := by
    calc
      _ ≤ ∑ b : Bool, probability (fun g : X → Bool ↦ ∀ x ∈ K, g x = b) :=
        Lax253009.FiniteProbability.finite_union_bound _
      _ = _ := by simp_rw [random_function_fixed_on]; simp
  calc
    _ ≤ ∏ _j : Fin q, (2 * (1 / 2 : ℝ) ^ K.card) :=
      Finset.prod_le_prod (fun _ _ ↦ finite_probability_nonneg _) (fun _ _ ↦ hone)
    _ = _ := by simp

private def HighAgreement {ι Ω X : Type} [Fintype ι] [DecidableEq X]
    (S : Ω → Finset X) (k q : ℕ) (w : ι → Ω) (g : Fin q → X → Bool) : Prop :=
  ∃ y : ι → X, (∀ i, y i ∈ S (w i)) ∧ k < (Finset.univ.image y).card ∧
    ∀ j, ∃ b, ∀ i, g j (y i) = b

private theorem high_agreement_probability {ι Ω X : Type} [Fintype ι] [DecidableEq ι]
    [Fintype X] [DecidableEq X] (S : Ω → Finset X) (B k q : ℕ)
    (hB : ∀ w, (S w).card ≤ B) (w : ι → Ω) :
    probability (HighAgreement S k q w) ≤
      (B : ℝ) ^ Fintype.card ι * (2 * (1 / 2 : ℝ) ^ (k + 1)) ^ q := by
  let T := (Fintype.piFinset (fun i ↦ S (w i))).filter
    (fun y : ι → X ↦ k < (Finset.univ.image y).card)
  let C := (2 * (1 / 2 : ℝ) ^ (k + 1)) ^ q
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hT : T.card ≤ B ^ Fintype.card ι := by
    calc
      _ ≤ (Fintype.piFinset (fun i ↦ S (w i))).card := Finset.card_filter_le _ _
      _ = ∏ i, (S (w i)).card := Fintype.card_piFinset _
      _ ≤ ∏ _i : ι, B := Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) (fun i _ ↦ hB (w i))
      _ = _ := by simp
  have hbound (y : ι → X) (hy : y ∈ T) :
      probability (fun g : Fin q → X → Bool ↦ ∀ j, ∃ b, ∀ i, g j (y i) = b) ≤ C := by
    have hk := (Finset.mem_filter.mp hy).2
    have he : (fun g : Fin q → X → Bool ↦ ∀ j, ∃ b, ∀ i, g j (y i) = b) =
        (fun g ↦ ∀ j, ∃ b, ∀ x ∈ Finset.univ.image y, g j x = b) := by
      funext g
      simp
    rw [he]
    exact (random_functions_monochromatic _ q).trans (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk) (by norm_num)) q)
  calc
    _ = probability (fun g : Fin q → X → Bool ↦ ∃ y ∈ T, ∀ j, ∃ b, ∀ i, g j (y i) = b) := by
      congr 1
      funext g
      simp only [HighAgreement, T, Finset.mem_filter, Fintype.mem_piFinset]
      aesop
    _ ≤ ∑ y ∈ T, probability (fun g : Fin q → X → Bool ↦ ∀ j, ∃ b, ∀ i, g j (y i) = b) :=
      finite_probability_finset_union _ _
    _ ≤ ∑ _y ∈ T, C := Finset.sum_le_sum hbound
    _ = T.card * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hT) hC

/--
---
conclusion: Lax253009.ManyTableConsistency.agreement_bound
---
Split selections according to their number of distinct projected assignments.
Few distinct assignments are rare by the representative-table bound. For
each remaining selection, each random function has to be constant on its
image; take the union bound over all selections and then average over tables.
-/
theorem many_tables_agreement {ι Ω X : Type} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Nonempty Ω] [Fintype X] [DecidableEq X]
    (S : Ω → Finset X) (B k q : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hB : ∀ w, (S w).card ≤ B)
    (hpoint : ∀ x, probability (fun w ↦ x ∈ S w) ≤ p)
    (hsmall : (Fintype.card ι : ℝ) * B * p ≤ 1) :
    probability (fun z : (ι → Ω) × (Fin q → X → Bool) ↦ Agreement S q z.1 z.2) ≤
      (2 : ℝ) ^ Fintype.card ι * ((Fintype.card ι : ℝ) * B * p) ^ (Fintype.card ι - k) +
      (B : ℝ) ^ Fintype.card ι * (2 * (1 / 2 : ℝ) ^ (k + 1)) ^ q := by
  have hlow : probability (fun z : (ι → Ω) × (Fin q → X → Bool) ↦ LowDiversity S k z.1) =
      probability (LowDiversity (ι := ι) S k) := by
    rw [finite_probability_product (fun w (_g : Fin q → X → Bool) ↦ LowDiversity S k w)]
    simp_rw [finite_probability_indicator]
    simp only [Fintype.expect_const]
  calc
    _ ≤ probability (fun z : (ι → Ω) × (Fin q → X → Bool) ↦
        LowDiversity S k z.1 ∨ HighAgreement S k q z.1 z.2) := by
      apply Lax253009.FiniteProbability.monotone
      rintro ⟨w, g⟩ ⟨y, hy, hg⟩
      by_cases hk : (Finset.univ.image y).card ≤ k
      · exact Or.inl ⟨y, hy, hk⟩
      · exact Or.inr ⟨y, hy, Nat.lt_of_not_ge hk, hg⟩
    _ ≤ probability (fun z : (ι → Ω) × (Fin q → X → Bool) ↦ LowDiversity S k z.1) +
        probability (fun z : (ι → Ω) × (Fin q → X → Bool) ↦ HighAgreement S k q z.1 z.2) :=
      Lax253009.FiniteProbability.union_bound _ _
    _ ≤ _ := add_le_add (hlow ▸ Lax253009.ManyTableConsistency.low_diversity_bound S B k p hp hB hpoint hsmall)
      (finite_probability_product_bound _ _ (high_agreement_probability S B k q hB))

end Lax253009Proofs
