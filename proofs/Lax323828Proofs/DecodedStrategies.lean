import Lax323828.DecodedStrategies
import Lax323828Proofs.FiniteProbability
import Mathlib.Data.Fintype.EquivFin

namespace Lax323828Proofs

open Lax323828.FiniteProbability Lax323828.DecodedStrategies
open scoped BigOperators Classical

private theorem decoded_enumeration {Y : Type} (D : Finset Y) (B : ℕ) (hB : D.card ≤ B) :
    ∃ reply : Fin (B + 1) → Option Y, ∀ y ∈ D, ∃ i, reply i = some y := by
  let e := D.equivFin
  let reply := fun i : Fin (B + 1) ↦ if h : i.val < D.card then
    some ((e.symm ⟨i.val, h⟩).val) else none
  refine ⟨reply, fun y hy ↦ ?_⟩
  let j := e ⟨y, hy⟩
  let i : Fin (B + 1) := ⟨j.val, lt_of_lt_of_le j.isLt (by omega)⟩
  refine ⟨i, ?_⟩
  dsimp only [reply]
  rw [dif_pos j.isLt]
  change some ((e.symm (e ⟨y, hy⟩)).val) = some y
  rw [Equiv.symm_apply_apply]

private theorem finite_singleton_probability {α : Type} [Fintype α] [DecidableEq α]
    (x : α) : probability (fun y ↦ y = x) = 1 / (Fintype.card α : ℝ) := by
  rw [finite_probability_indicator, Fintype.expect_eq_sum_div_card]
  simp

/--
---
conclusion: Lax323828.DecodedStrategies.extract_strategies
---
Fix a common answer separately for each second question. Randomly and
independently choose one of B+1 slots for every first question; every decoded
answer occupies a slot. Average over these global first-prover strategies
and fix one whose success is at least the average.
-/
theorem decoded_prover_strategies {U Ω W X Y : Type}
    [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
    [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y]
    (question : U → Ω → W) (V : U → Ω → Y → X → Prop)
    (D : W → Finset Y) (B : ℕ) (hB : ∀ w, (D w).card ≤ B)
    (p : ℝ) (_hp : 0 ≤ p) :
    ∃ P : W → Option Y, ∃ Q : U → Option X,
      probability (Common question V D p) * p / (B + 1) ≤ probability (Wins question V P Q) := by
  choose reply hreply using fun w ↦ decoded_enumeration (D w) B (hB w)
  let Q := fun u ↦ if h : Common question V D p u then some h.choose else none
  let P := fun (a : W → Fin (B + 1)) w ↦ reply w (a w)
  let I := fun u ω ↦ ∃ y x, y ∈ D (question u ω) ∧ Q u = some x ∧ V u ω y x
  have hden : (0 : ℝ) < B + 1 := by positivity
  have hpoint (z : U × Ω) :
      (if I z.1 z.2 then (1 : ℝ) / (B + 1) else 0) ≤
        probability (fun a : W → Fin (B + 1) ↦ Wins question V (P a) Q z) := by
    by_cases hz : I z.1 z.2
    · obtain ⟨y, x, hy, hx, hV⟩ := hz
      obtain ⟨i, hi⟩ := hreply (question z.1 z.2) y hy
      have he : probability (fun a : W → Fin (B + 1) ↦ a (question z.1 z.2) = i) = 1 / (B + 1) := by
        rw [finite_probability_evaluation (question z.1 z.2) (fun j ↦ j = i), finite_singleton_probability]
        simp
      rw [if_pos ⟨y, x, hy, hx, hV⟩, ← he]
      apply Lax323828.FiniteProbability.monotone
      intro a ha
      exact ⟨y, x, (congrArg (reply (question z.1 z.2)) ha).trans hi, hx, hV⟩
    · rw [if_neg hz]
      exact finite_probability_nonneg _
  have hinner (u : U) : (if Common question V D p u then p else 0) ≤
      probability (I u) := by
    by_cases hu : Common question V D p u
    · rw [if_pos hu]
      apply le_trans hu.choose_spec
      apply Lax323828.FiniteProbability.monotone
      rintro ω ⟨y, hy, hV⟩
      exact ⟨y, hu.choose, hy, by simp [Q, hu], hV⟩
    · rw [if_neg hu]
      exact finite_probability_nonneg _
  have hmass : probability (Common question V D p) * p ≤ probability (fun z : U × Ω ↦ I z.1 z.2) := by
    rw [finite_probability_product I, finite_probability_indicator, Finset.expect_mul]
    apply Finset.expect_le_expect
    intro u _
    simpa only [ite_mul, one_mul, zero_mul] using hinner u
  have havg : probability (Common question V D p) * p / (B + 1) ≤
      𝔼 a : W → Fin (B + 1), probability (Wins question V (P a) Q) := by
    calc
      _ ≤ probability (fun z : U × Ω ↦ I z.1 z.2) / (B + 1) :=
        div_le_div_of_nonneg_right hmass hden.le
      _ = 𝔼 z : U × Ω, if I z.1 z.2 then (1 : ℝ) / (B + 1) else 0 := by
        rw [finite_probability_indicator, Finset.expect_div]
        apply Finset.expect_congr rfl
        intro z _
        split_ifs <;> simp
      _ ≤ 𝔼 z : U × Ω, probability (fun a : W → Fin (B + 1) ↦ Wins question V (P a) Q z) :=
        Finset.expect_le_expect (fun z _ ↦ hpoint z)
      _ = _ := by
        simp_rw [finite_probability_indicator]
        exact Finset.expect_comm _ _ _
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty havg
  exact ⟨P a, Q, ha⟩

end Lax323828Proofs
