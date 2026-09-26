import Lax253009.FiniteProbability
import Mathlib.Tactic

namespace Lax253009Proofs

open Lax253009.FiniteProbability
open scoped BigOperators

/--
---
conclusion: Lax253009.FiniteProbability.monotone
---
Count the included event and divide by the size of the common sample space.
-/
theorem finite_probability_mono {α : Type} [Fintype α]
    (P Q : α → Prop) (h : ∀ x, P x → Q x) : probability P ≤ probability Q := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show Finset.univ.filter P ⊆ Finset.univ.filter Q from
    fun x hx ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x (Finset.mem_filter.mp hx).2⟩)

/--
---
conclusion: Lax253009.FiniteProbability.union_bound
---
The cardinality of a union is at most the sum of the two cardinalities.
-/
theorem finite_probability_union {α : Type} [Fintype α] (P Q : α → Prop) :
    probability (fun x ↦ P x ∨ Q x) ≤ probability P + probability Q := by
  classical
  unfold probability
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := Finset.card_union_le (Finset.univ.filter P) (Finset.univ.filter Q)
  rw [← Finset.filter_or] at h
  norm_cast
  convert h using 1
  congr 1
  ext x
  simp

/--
---
conclusion: Lax253009.FiniteProbability.even_moment_bound
---
Every point of the tail contributes at least t^m to a nonnegative moment sum.
-/
theorem finite_even_moment_bound {α : Type} [Fintype α] [Nonempty α]
    (X : α → ℝ) (t : ℝ) (ht : 0 < t) (m : ℕ) (hm : Even m) :
    probability (fun x ↦ t ≤ X x) ≤ (𝔼 x, X x ^ m) / t ^ m := by
  classical
  let bad := Finset.univ.filter fun x ↦ t ≤ X x
  have hsum : (bad.card : ℝ) * t ^ m ≤ ∑ x, X x ^ m := by
    calc
      _ = ∑ _x ∈ bad, t ^ m := by simp
      _ ≤ ∑ x ∈ bad, X x ^ m := Finset.sum_le_sum fun x hx ↦
        pow_le_pow_left₀ ht.le (Finset.mem_filter.mp hx).2 m
      _ ≤ ∑ x, X x ^ m := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun x _ _ ↦ hm.pow_nonneg (X x))
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  unfold probability
  rw [Fintype.expect_eq_sum_div_card, le_div_iff₀ (pow_pos ht m), div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right hN).mpr hsum

/--
---
conclusion: Lax253009.FiniteProbability.restriction_bound
---
Restricting to a subset of mass at least 1/K inflates any event by at most K.
-/
theorem finite_probability_restriction {α : Type} [Fintype α] (s : Finset α)
    (hs : s.Nonempty) (K : ℝ) (hcard : (Fintype.card α : ℝ) ≤ K * s.card)
    (P : α → Prop) : probability (fun x : s ↦ P x.val) ≤ K * probability P := by
  classical
  have : Nonempty α := ⟨hs.choose⟩
  let bad := Finset.univ.filter P
  let restricted := Finset.univ.filter (fun x : s ↦ P x.val)
  have hc : restricted.card ≤ bad.card := by
    have hsub : restricted.image Subtype.val ⊆ bad := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using
      Finset.card_le_card hsub
  have hD : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hratio : 1 / (s.card : ℝ) ≤ K / (Fintype.card α : ℝ) :=
    (div_le_div_iff₀ hD hN).mpr (by simpa using hcard)
  change (restricted.card : ℝ) / (Fintype.card s : ℝ) ≤ K * ((bad.card : ℝ) / _)
  rw [Fintype.card_coe]
  calc
    _ ≤ (bad.card : ℝ) / s.card := div_le_div_of_nonneg_right (by exact_mod_cast hc) hD.le
    _ = (bad.card : ℝ) * (1 / s.card) := by ring
    _ ≤ (bad.card : ℝ) * (K / (Fintype.card α : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)
    _ = _ := by ring

theorem finite_probability_indicator {α : Type} [Fintype α] (P : α → Prop)
    [DecidablePred P] : probability P = (𝔼 x, if P x then (1 : ℝ) else 0) := by
  classical
  unfold probability
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  rw [← Finset.sum_filter]
  simp
  congr 1
  ext x
  simp

/--
---
conclusion: Lax253009.FiniteProbability.finite_union_bound
---
The indicator of a union is bounded by the sum of its member indicators.
-/
theorem finite_probability_finite_union {α ι : Type} [Fintype α] [Fintype ι]
    (P : ι → α → Prop) : probability (fun x ↦ ∃ i, P i x) ≤ ∑ i, probability (P i) := by
  classical
  simp_rw [finite_probability_indicator]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro x _
  by_cases h : ∃ i, P i x
  · obtain ⟨i, hi⟩ := h
    rw [if_pos ⟨i, hi⟩]
    simpa [hi] using (Finset.single_le_sum
      (f := fun j ↦ if P j x then (1 : ℝ) else 0)
      (fun j _ ↦ by positivity) (Finset.mem_univ i))
  · rw [if_neg h]
    exact Finset.sum_nonneg fun j _ ↦ by positivity

/--
---
conclusion: Lax253009.FiniteProbability.bounded_power_mean
---
Split a bounded moment into the part below q and the exceptional upper tail.
-/
theorem finite_bounded_power_mean {α : Type} [Fintype α] [Nonempty α]
    (X : α → ℝ) (hX : ∀ x, 0 ≤ X x ∧ X x ≤ 1) (q : ℝ) (hq : 0 ≤ q) (l : ℕ) :
    (𝔼 x, X x ^ l) ≤ q ^ l + probability (fun x ↦ q < X x) := by
  classical
  rw [finite_probability_indicator]
  calc
    _ ≤ 𝔼 x, (q ^ l + if q < X x then (1 : ℝ) else 0) := by
      apply Finset.expect_le_expect
      intro x _
      split_ifs with h
      · have hx : X x ^ l ≤ 1 := pow_le_one₀ (hX x).1 (hX x).2
        linarith [pow_nonneg hq l]
      · simpa using pow_le_pow_left₀ (hX x).1 (le_of_not_gt h) l
    _ = _ := by rw [Finset.expect_add_distrib, Fintype.expect_const]

theorem finite_probability_equiv {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (P : α → Prop) (Q : β → Prop) (h : ∀ x, P x ↔ Q (e x)) :
    probability P = probability Q := by
  classical
  simp_rw [finite_probability_indicator]
  exact Fintype.expect_equiv e _ _ (fun x ↦ by simp only [h x])

theorem finite_probability_counting {α ι : Type} [Fintype α] [Fintype ι]
    (P : α → Prop) (G : α → Finset ι) (t : ℝ) (ht : 0 < t)
    (hcount : ∀ x, P x → t ≤ (G x).card) :
    probability P ≤ (∑ i, probability (fun x ↦ i ∈ G x)) / t := by
  classical
  apply (le_div_iff₀ ht).mpr
  simp_rw [finite_probability_indicator]
  rw [Finset.expect_mul, ← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro x _
  by_cases hx : P x
  · simp only [hx, if_true, one_mul]
    simpa using hcount x hx
  · simp only [hx, if_false, zero_mul]
    exact Finset.sum_nonneg fun _ _ ↦ by positivity

theorem finite_probability_nonneg {α : Type} [Fintype α] (P : α → Prop) :
    0 ≤ probability P := by unfold probability; positivity

theorem finite_probability_le_one {α : Type} [Fintype α] (P : α → Prop) :
    probability P ≤ 1 := by
  classical
  unfold probability
  exact div_le_one_of_le₀ (by exact_mod_cast Finset.card_filter_le Finset.univ P)
    (Nat.cast_nonneg _)

theorem finite_probability_finset_union {α ι : Type} [Fintype α]
    (s : Finset ι) (P : ι → α → Prop) :
    probability (fun x ↦ ∃ i ∈ s, P i x) ≤ ∑ i ∈ s, probability (P i) := by
  classical
  have h := finite_probability_finite_union (fun i : s ↦ P i.val)
  have he : (∑ i : s, probability (P i.val)) = ∑ i ∈ s, probability (P i) :=
    Finset.sum_coe_sort s (fun i ↦ probability (P i))
  rw [he] at h
  simpa only [Subtype.exists, exists_prop] using h

theorem finite_probability_product {α β : Type} [Fintype α] [Fintype β]
    (P : α → β → Prop) :
    probability (fun z : α × β ↦ P z.1 z.2) = 𝔼 x, probability (P x) := by
  classical
  simp_rw [finite_probability_indicator]
  rw [← Finset.expect_product', Finset.univ_product_univ]

theorem finite_probability_product_bound {α β : Type} [Fintype α] [Nonempty α]
    [Fintype β] (P : α → β → Prop) (b : ℝ)
    (h : ∀ x, probability (P x) ≤ b) :
    probability (fun z : α × β ↦ P z.1 z.2) ≤ b := by
  rw [finite_probability_product]
  exact Finset.expect_le Finset.univ_nonempty (fun x _ ↦ h x)

theorem finite_probability_pi {ι Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (P : ι → Ω → Prop) :
    probability (fun w : ι → Ω ↦ ∀ i, P i (w i)) = ∏ i, probability (P i) := by
  classical
  have he (w : ι → Ω) : (if ∀ i, P i (w i) then (1 : ℝ) else 0) =
      ∏ i, if P i (w i) then (1 : ℝ) else 0 := by
    by_cases hw : ∀ i, P i (w i)
    · simp [hw]
    · obtain ⟨i, hi⟩ := not_forall.mp hw
      rw [if_neg hw]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  simp_rw [finite_probability_indicator, he]
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Nat.cast_pow,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.prod_sum]

theorem finite_probability_evaluation {ι Ω : Type} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Nonempty Ω] (i : ι) (P : Ω → Prop) :
    probability (fun w : ι → Ω ↦ P (w i)) = probability P := by
  classical
  let Q := fun j v ↦ j = i → P v
  have he : (fun w : ι → Ω ↦ P (w i)) = (fun w ↦ ∀ j, Q j (w j)) := by
    funext w
    simp [Q]
  rw [he, finite_probability_pi Q]
  have ht (j : ι) : probability (Q j) = if j = i then probability P else 1 := by
    by_cases hj : j = i
    · subst j; simp [Q]
    · simp only [Q, hj, false_implies, if_false]
      rw [finite_probability_indicator, Fintype.expect_const]
      simp
  simp_rw [ht]
  simp

end Lax253009Proofs
