import Lax253009.FAFPatterns
import Lax253009Proofs.LongCodePatterns

namespace Lax253009Proofs

open Lax253009.LongCode Lax253009.LongCodePatterns Lax253009.FAFPatterns
open scoped BigOperators Classical

/--
---
conclusion: Lax253009.FAFPatterns.transcript_mem
---
Use the actual reference answers and the accepting pattern of each CNA test.
-/
theorem faf_transcript_mem {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w) (R : Table u) (A : Ω → Table w)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u) (f : Fin n → Fin s → Coordinate w)
    (h : Lax253009.FAFTest.Accepts ρ valid R A ω g f) :
    transcript ρ valid R A ω g f ∈ Lax253009.FAFPatterns.patterns ρ valid ω g f := by
  apply Finset.mem_biUnion.mpr
  refine ⟨fun j ↦ R (g j), Finset.mem_univ _, Finset.mem_image.mpr ⟨_, ?_, rfl⟩⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_image.mpr
  exact ⟨A (ω i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h i⟩, rfl⟩

/--
---
conclusion: Lax253009.FAFPatterns.free_bits
---
Sum over 2^q reference answer strings, and use the proved bound of 2^s
accepting side-condition patterns for each of the n tables.
-/
theorem faf_free_bits {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u) (f : Fin n → Fin s → Coordinate w) :
    (Lax253009.FAFPatterns.patterns ρ valid ω g f).card ≤ 2 ^ (q + n * s) := by
  calc
    _ ≤ ∑ b : Word q,
        ((Fintype.piFinset (fun i ↦ sidePatterns (f i) (conditionOfAnswers ρ valid (ω i) g b))).image
          (fun a ↦ (b, a))).card := Finset.card_biUnion_le
    _ ≤ ∑ _b : Word q, (2 ^ s) ^ n := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.card_image_le.trans
      rw [Fintype.card_piFinset]
      calc
        _ ≤ ∏ _i : Fin n, 2 ^ s :=
          Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) (fun i _ ↦ Lax253009.LongCodePatterns.side_free_bits _ _)
        _ = _ := by simp
    _ = _ := by simp [Word, ← pow_mul, pow_add, Nat.mul_comm]

end Lax253009Proofs
