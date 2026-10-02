import Lax323828.TestRepetition
import Lax323828Proofs.FiniteProbability

namespace Lax323828Proofs

open Lax323828.LocalTests Lax323828.TestSampling Lax323828.TestRepetition
open Lax323828.FiniteProbability
open scoped Classical BigOperators

private theorem merge_source {m k : ℕ} (a : Fin k → View m) (i : Fin m) (b : Bool)
    (h : merge a i = some b) : ∃ j, a j i = some b := by
  induction k with
  | zero => simp [merge] at h
  | succ k ih =>
    cases hzero : a 0 i with
    | none =>
      have ht : merge (fun j : Fin k ↦ a j.succ) i = some b := by simpa [merge, hzero] using h
      obtain ⟨j, hj⟩ := ih (fun j ↦ a j.succ) ht
      exact ⟨j.succ, hj⟩
    | some c =>
      have he : c = b := by simpa [merge, hzero] using h
      exact ⟨0, he ▸ hzero⟩

private theorem merge_none {m k : ℕ} (a : Fin k → View m) (i : Fin m) :
    merge a i = none ↔ ∀ j, a j i = none := by
  induction k with
  | zero => simp [merge]
  | succ k ih =>
    cases hzero : a 0 i <;> simp [merge, hzero, ih, Fin.forall_fin_succ]

theorem extends_merge_iff {m k : ℕ} (a : Fin k → View m)
    (ha : Coherent a) (π : Oracle m) : Extends π (merge a) ↔ ∀ j, Extends π (a j) := by
  constructor
  · intro h j i b hij
    cases hm : merge a i with
    | none => have hn := (merge_none a i).mp hm j; rw [hij] at hn; cases hn
    | some c =>
      obtain ⟨j', hj'⟩ := merge_source a i c hm
      exact (h i c hm).trans ((ha j j' i b c hij hj').symm)
  · intro h i b hi
    obtain ⟨j, hj⟩ := merge_source a i b hi
    exact h j i b hj

/--
---
conclusion: Lax323828.TestRepetition.passes_iff
---
Compatible views merge exactly when they are jointly extended. Conversely,
views accepted by a single global proof are automatically compatible.
-/
theorem repeated_passes {r m : ℕ} (C : System r m) (k : ℕ) (π : Oracle m) (z : Fin (r ^ k)) :
    Passes (repeated C k) π z ↔ ∀ i, Passes C π ((seedEquiv r k).symm z i) := by
  constructor
  · rintro ⟨v, hv, he⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨ha, hcoh⟩ := Finset.mem_filter.mp ha
    intro i
    exact ⟨a i, Fintype.mem_piFinset.mp ha i, (extends_merge_iff a hcoh π).mp he i⟩
  · intro h
    choose a ha he using h
    have hcoh : Coherent a := fun i j x b c hb hc ↦ (he i x b hb).symm.trans (he j x c hc)
    refine ⟨merge a, Finset.mem_image.mpr ⟨a, ?_, rfl⟩, (extends_merge_iff a hcoh π).mpr he⟩
    exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ha, hcoh⟩

/--
---
conclusion: Lax323828.TestRepetition.acceptance_probability
---
Transfer uniform seeds through their numbering equivalence and factor the
independent fixed-proof acceptance events.
-/
theorem repeated_probability {r m : ℕ} (C : System r m) (k : ℕ) (π : Oracle m) :
    probability (Passes (repeated C k) π) = probability (Passes C π) ^ k := by
  calc
    _ = probability (fun z : Fin k → Fin r ↦ ∀ i, Passes C π (z i)) :=
      finite_probability_equiv (seedEquiv r k).symm _ _ (Lax323828.TestRepetition.passes_iff C k π)
    _ = ∏ _i : Fin k, probability (Passes C π) :=
      finite_probability_pi (fun (_ : Fin k) z ↦ Passes C π z)
    _ = _ := by simp

/--
---
conclusion: Lax323828.TestRepetition.free_bits
---
Filtering for compatibility and merging cannot increase the product count.
-/
theorem repeated_free_bits {r m : ℕ} (C : System r m) (k A : ℕ)
    (hA : ∀ z, (C.accepting z).card ≤ A) :
    ∀ z, ((repeated C k).accepting z).card ≤ A ^ k := by
  intro z
  apply Finset.card_image_le.trans
  apply (Finset.card_filter_le _ _).trans
  rw [Fintype.card_piFinset]
  calc
    _ ≤ ∏ _i : Fin k, A := Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) (fun i _ ↦ hA _)
    _ = _ := by simp

/--
---
conclusion: Lax323828.TestRepetition.perfect_completeness
---
The same perfect proof works in every repetition.
-/
theorem repeated_perfect_completeness {r m : ℕ} (C : System r m) (k : ℕ) (hC : Complete C) :
    Complete (repeated C k) := by
  obtain ⟨π, hπ⟩ := hC
  exact ⟨π, fun z ↦ (Lax323828.TestRepetition.passes_iff C k π z).mpr (fun i ↦ hπ _)⟩

/--
---
conclusion: Lax323828.TestRepetition.soundness
---
Apply the exact probability identity to every fixed proof.
-/
theorem repeated_soundness {r m : ℕ} (C : System r m) (k : ℕ) (p : ℝ) (_hp : 0 ≤ p)
    (hC : Sound C p) : Sound (repeated C k) (p ^ k) := by
  intro π
  rw [Lax323828.TestRepetition.acceptance_probability]
  exact pow_le_pow_left₀ (finite_probability_nonneg _) (hC π) k

end Lax323828Proofs
