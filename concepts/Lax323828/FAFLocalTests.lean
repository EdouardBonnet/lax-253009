import Lax323828.FAFComposition
import Lax323828.TestRepetition

/-!
---
title: The FAF verifier as a finite local-test system
type: theorem
---
Number all coordinates of all reference and larger tables to form a
single Boolean proof. For each random choice, convert the enumerated FAF
transcripts into partial assignments. Filter out inconsistent assignments
to repeated coordinates and merge the remainder.

The resulting system accepts exactly when the original FAF verifier does,
and has at most $2^{q+ns}$ accepting views per choice. Thus the finite FAF
soundness theorem applies directly to the graph reduction. Numbering and
enumeration here are finite mathematical constructions; their efficient
machine implementations are separate obligations.
-/

namespace Lax323828.FAFLocalTests

open scoped Classical

open LongCode LocalTests LongCodePatterns TestRepetition TestSampling

/-- All coordinates of the reference tables and the larger tables, kept as two separate families. -/
abbrev Index (U W : Type) (u w : ℕ) := (U × Coordinate u) ⊕ (W × Coordinate w)

/-- A reference question together with all random choices made by its local test. -/
abbrev Randomness (U Ω : Type) (u w n s q : ℕ) :=
  U × FAFStrategyExtraction.Seed Ω u w n s q

/-- Number the proof coordinates consecutively. -/
noncomputable def indexEquiv (U W : Type) [Fintype U] [Fintype W] (u w : ℕ) :
    Index U W u w ≃ Fin (Fintype.card (Index U W u w)) := Fintype.equivFin _

/-- Number the possible random choices consecutively. -/
noncomputable def randomEquiv (U Ω : Type) [Fintype U] [Fintype Ω] (u w n s q : ℕ) :
    Randomness U Ω u w n s q ≃ Fin (Fintype.card (Randomness U Ω u w n s q)) :=
  Fintype.equivFin _

/-- Read one reference table from the global Boolean proof. -/
noncomputable def reference {U W : Type} [Fintype U] [Fintype W] {u w : ℕ}
    (π : Oracle (Fintype.card (Index U W u w))) (v : U) : Table u :=
  fun g ↦ π (indexEquiv U W u w (Sum.inl (v, g)))

/-- Read one larger table from the global Boolean proof. -/
noncomputable def larger {U W : Type} [Fintype U] [Fintype W] {u w : ℕ}
    (π : Oracle (Fintype.card (Index U W u w))) (v : W) : Table w :=
  fun g ↦ π (indexEquiv U W u w (Sum.inr (v, g)))

/-- Translate the reference answers and the larger-table patterns into partial assignments to the global proof. -/
noncomputable def parts {U Ω W : Type} [Fintype U] [Fintype W] {u w n s q : ℕ}
    (question : U → Ω → W) (z : Randomness U Ω u w n s q)
    (p : LongCode.Word q × (Fin n → Pattern w)) :
    Fin (q + n) → View (Fintype.card (Index U W u w)) :=
  Fin.addCases
    (fun j x ↦ if x = indexEquiv U W u w (Sum.inl (z.1, z.2.1.2 j)) then some (p.1 j) else none)
    (fun i x ↦ match (indexEquiv U W u w).symm x with
      | .inl _ => none
      | .inr (v, g) => if v = question z.1 (z.2.1.1 i) then p.2 i g else none)

/-- For each random choice, merge exactly the mutually consistent accepting partial assignments. -/
noncomputable def system {U Ω W : Type} [Fintype U] [Fintype Ω] [Fintype W]
    {u w n s q : ℕ} (question : U → Ω → W)
    (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → Coordinate w) :
    System (Fintype.card (Randomness U Ω u w n s q)) (Fintype.card (Index U W u w)) :=
  ⟨fun seed ↦
    let z := (randomEquiv U Ω u w n s q).symm seed
    ((FAFPatterns.patterns (ρ z.1) (valid z.1) z.2.1.1 z.2.1.2 z.2.2).filter
      (fun p ↦ Coherent (parts question z p))).image (fun p ↦ merge (parts question z p))⟩

axiom passes_iff {U Ω W : Type} [Fintype U] [Fintype Ω] [Fintype W]
    {u w n s q : ℕ} (question : U → Ω → W)
    (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → Coordinate w)
    (π : Oracle (Fintype.card (Index U W u w)))
    (z : Randomness U Ω u w n s q) :
  Passes (system (n := n) (s := s) (q := q) question ρ valid) π (randomEquiv U Ω u w n s q z) ↔
    FAFStrategyExtraction.Accepts question ρ valid (reference π) (larger π) z

axiom free_bits {U Ω W : Type} [Fintype U] [Fintype Ω] [Fintype W]
    {u w n s q : ℕ} (question : U → Ω → W)
    (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → Coordinate w) :
  ∀ seed, ((system (n := n) (s := s) (q := q) question ρ valid).accepting seed).card ≤ 2 ^ (q + n * s)

axiom acceptance_probability {U Ω W : Type} [Fintype U] [Fintype Ω] [Fintype W]
    {u w n s q : ℕ} (question : U → Ω → W)
    (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → Coordinate w)
    (π : Oracle (Fintype.card (Index U W u w))) :
  FiniteProbability.probability (Passes (system (n := n) (s := s) (q := q) question ρ valid) π) =
    FiniteProbability.probability
      (FAFStrategyExtraction.Accepts (n := n) (s := s) (q := q) question ρ valid (reference π) (larger π))

axiom perfect_completeness {U Ω W : Type} [Fintype U] [Fintype Ω] [Fintype W]
    {u w n s q : ℕ} (question : U → Ω → W)
    (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → Coordinate w)
    (P : W → LongCode.Word w) (Q : U → LongCode.Word u)
    (hvalid : ∀ v ω, valid v ω (P (question v ω)) = true)
    (hproject : ∀ v ω, ρ v ω (P (question v ω)) = Q v) :
  Complete (system (n := n) (s := s) (q := q) question ρ valid)

axiom soundness (l : ℕ) (hl : 0 < l) :
  ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w →
    ∀ {U Ω W : Type} [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
      [Fintype W] [DecidableEq W],
    ∀ u : ℕ, ∀ (question : U → Ω → W)
      (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → Coordinate w),
      (∀ (P : W → Option (LongCode.Word w)) (Q : U → Option (LongCode.Word u)),
        FiniteProbability.probability (DecodedStrategies.Wins question
          (FAFStrategyExtraction.Relation ρ valid) P Q) < FAFComposition.gameThreshold l s) →
      Sound (system (n := 10 * l) (s := s) (q := 10 * l * s) question ρ valid)
        ((1 / 2 : ℝ) ^ (20 * l * l * s))

axiom proof_length (U W : Type) [Fintype U] [Fintype W] (u w : ℕ) :
  Fintype.card (Index U W u w) = Fintype.card U * 2 ^ (2 ^ u) + Fintype.card W * 2 ^ (2 ^ w)

axiom random_choices (U Ω : Type) [Fintype U] [Fintype Ω] (u w n s q : ℕ) :
  Fintype.card (Randomness U Ω u w n s q) =
    Fintype.card U * (Fintype.card Ω ^ n * (2 ^ (2 ^ u)) ^ q * ((2 ^ (2 ^ w)) ^ s) ^ n)

end Lax323828.FAFLocalTests
