import Lax253009Proofs.SlotGraph
import Lax253009Proofs.FAFLocalTests

namespace Lax253009Proofs.FAFSlots

open Lax253009 LocalTests LongCodePatterns FAFLocalTests TestRepetition
open scoped Classical

/-- Fill a fixed array from a finite set; excess positions are absent. -/
noncomputable def listSlot {X : Type} (s : Finset X) {A : ℕ} (_h : s.card ≤ A)
    (j : Fin A) : Option X :=
  if hj : j.val < s.card then some ((s.equivFin).symm ⟨j.val, hj⟩).val else none

theorem listSlot_sound {X : Type} (s : Finset X) {A : ℕ} (h : s.card ≤ A)
    (j : Fin A) (x : X) (hx : listSlot s h j = some x) : x ∈ s := by
  unfold listSlot at hx
  split_ifs at hx with hj
  exact Option.some.inj hx ▸ ((s.equivFin).symm ⟨j.val, hj⟩).property

theorem listSlot_complete {X : Type} (s : Finset X) {A : ℕ} (h : s.card ≤ A)
    (x : X) (hx : x ∈ s) : ∃ j, listSlot s h j = some x := by
  let j := s.equivFin ⟨x, hx⟩
  refine ⟨Fin.castLE h j, ?_⟩
  simp only [listSlot, Fin.val_castLE, dif_pos j.isLt]
  exact congrArg (fun y : s ↦ some y.val) ((s.equivFin).symm_apply_apply ⟨x, hx⟩)

/-- All data that determine the finite set of possible FAF transcripts.
The type is fixed once the verifier constants are fixed. -/
abbrev Data (u w n s q : ℕ) :=
  (Fin n → LongCode.Word w → LongCode.Word u) ×
  (Fin n → LongCode.Coordinate w) ×
  (Fin q → LongCode.Coordinate u) × (Fin n → Fin s → LongCode.Coordinate w)

noncomputable def dataPatterns {u w n s q : ℕ} (d : Data u w n s q) :
    Finset (LongCode.Word q × (Fin n → Pattern w)) :=
  FAFPatterns.patterns d.1 d.2.1 id d.2.2.1 d.2.2.2

theorem dataPatterns_bound {u w n s q : ℕ} (d : Data u w n s q) :
    (dataPatterns d).card ≤ 2 ^ (q + n * s) := Lax253009.FAFPatterns.free_bits _ _ _ _ _

noncomputable def patternSlot {u w n s q : ℕ} (d : Data u w n s q)
    (j : Fin (2 ^ (q + n * s))) : Option (LongCode.Word q × (Fin n → Pattern w)) :=
  listSlot (dataPatterns d) (dataPatterns_bound d) j

def data {U Ω : Type} {u w n s q : ℕ}
    (ρ : U → Ω → LongCode.Word w → LongCode.Word u)
    (valid : U → Ω → LongCode.Coordinate w) (z : Randomness U Ω u w n s q) :
    Data u w n s q :=
  (fun i ↦ ρ z.1 (z.2.1.1 i), fun i ↦ valid z.1 (z.2.1.1 i), z.2.1.2, z.2.2)

theorem dataPatterns_eq {U Ω : Type} {u w n s q : ℕ}
    (ρ : U → Ω → LongCode.Word w → LongCode.Word u)
    (valid : U → Ω → LongCode.Coordinate w) (z : Randomness U Ω u w n s q) :
    dataPatterns (data ρ valid z) = FAFPatterns.patterns (ρ z.1) (valid z.1) z.2.1.1 z.2.1.2 z.2.2 := rfl

/-- The finite local-test system has exactly 2^(q+ns) candidate slots per seed.
Selecting a candidate depends only on fixed finite data; consistency uses the
actual question names and is checked separately. -/
noncomputable def enumeration {U Ω W : Type} [Fintype U] [Fintype Ω] [Fintype W]
    {u w n s q : ℕ} (question : U → Ω → W)
    (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → LongCode.Coordinate w) :
    SlotGraph.Enumeration (FAFLocalTests.system (n := n) (s := s) (q := q) question ρ valid)
      (2 ^ (q + n * s)) where
  valid seed j :=
    let z := (randomEquiv U Ω u w n s q).symm seed
    match patternSlot (data ρ valid z) j with
    | none => false
    | some p => decide (Coherent (parts question z p))
  view seed j :=
    let z := (randomEquiv U Ω u w n s q).symm seed
    match patternSlot (data ρ valid z) j with
    | none => fun _ ↦ none
    | some p => merge (parts question z p)
  sound seed j h := by
    dsimp only at h ⊢
    split at h
    · cases h
    · rename_i p hp
      apply Finset.mem_image.mpr
      refine ⟨p, Finset.mem_filter.mpr ⟨?_, of_decide_eq_true h⟩, rfl⟩
      have hh := listSlot_sound _ _ j p hp
      exact hh
  complete seed a ha := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hp, hc⟩ := Finset.mem_filter.mp hp
    obtain ⟨j, hj⟩ := listSlot_complete
      (dataPatterns (data ρ valid ((randomEquiv U Ω u w n s q).symm seed)))
      (dataPatterns_bound _) p hp
    refine ⟨j, ?_, ?_⟩ <;> simp only [patternSlot, hj, decide_eq_true_eq]
    exact hc

end Lax253009Proofs.FAFSlots
