import Lax323828.FAFLocalTests
import Lax323828Proofs.FAFComposition
import Lax323828Proofs.FAFPatterns
import Lax323828Proofs.TestRepetition

namespace Lax323828Proofs

open Lax323828 Lax323828.LongCode Lax323828.LocalTests Lax323828.LongCodePatterns
open Lax323828.TestRepetition Lax323828.TestSampling Lax323828.FAFLocalTests
open Lax323828.FiniteProbability
open scoped Classical

private theorem side_acceptance_transfer {w s : ℕ} (A B : Table w)
    (f : Fin s → Coordinate w) (h : Coordinate w)
    (heq : ∀ g, SideQueried f h g → B g = A g)
    (ha : AcceptsWithCondition A f h) : AcceptsWithCondition B f h := by
  have hq (g : Coordinate w) (hg : Queried f g) : B g = A g :=
    heq g ⟨g, hg, fun _ _ ↦ rfl⟩
  constructor
  · intro p
    rw [hq (compose f p) (Or.inr ⟨p, rfl⟩), ha.1 p]
    congr 1
    funext i
    exact (hq (f i) (Or.inl ⟨i, rfl⟩)).symm
  · intro g hg g' hgg'
    rw [hq g hg, heq g' ⟨g, hg, hgg'⟩]
    exact ha.2 g hg g' hgg'

private theorem parts_extend_iff {U Ω W : Type} [Fintype U] [Fintype W]
    {u w n s q : ℕ} (question : U → Ω → W) (z : Randomness U Ω u w n s q)
    (p : LongCode.Word q × (Fin n → Pattern w))
    (π : Oracle (Fintype.card (Index U W u w))) :
    (∀ j, Extends π (parts question z p j)) ↔
      (∀ j, reference π z.1 (z.2.1.2 j) = p.1 j) ∧
      (∀ i g b, p.2 i g = some b → larger π (question z.1 (z.2.1.1 i)) g = b) := by
  rw [Fin.forall_fin_add]
  simp only [parts, Fin.addCases_left, Fin.addCases_right]
  constructor
  · rintro ⟨hleft, hright⟩
    constructor
    · intro j
      exact hleft j _ _ (if_pos rfl)
    · intro i g b hb
      apply hright i (indexEquiv U W u w (Sum.inr (question z.1 (z.2.1.1 i), g))) b
      simpa using hb
  · rintro ⟨hleft, hright⟩
    constructor
    · intro j x b hx
      dsimp only at hx
      split_ifs at hx with he
      subst x
      exact (hleft j).trans (Option.some.inj hx)
    · intro i x b hx
      dsimp only at hx
      generalize he : (indexEquiv U W u w).symm x = y at hx
      have hx' : x = indexEquiv U W u w y := by rw [← he]; simp
      subst x
      cases y with
      | inl y => cases hx
      | inr y =>
        rcases y with ⟨v, g⟩
        dsimp only at hx
        split_ifs at hx with hv
        subst v
        exact hright i g b hx

private theorem coherent_of_extensions {m k : ℕ} (π : Oracle m) (a : Fin k → View m)
    (h : ∀ i, Extends π (a i)) : Coherent a :=
  fun i j x b c hb hc ↦ (h i x b hb).symm.trans (h j x c hc)

/--
---
conclusion: Lax323828.FAFLocalTests.passes_iff
---
An extending proof supplies exactly the recorded reference and queried
table answers. Conversely, an actual accepting transcript is coherent
because every recorded bit comes from the same proof coordinate.
-/
theorem faf_local_passes {U Ω W : Type} [Fintype U] [Fintype Ω] [Fintype W]
    {u w n s q : ℕ} (question : U → Ω → W)
    (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → Coordinate w)
    (π : Oracle (Fintype.card (Index U W u w)))
    (z : Randomness U Ω u w n s q) :
    Passes (system (n := n) (s := s) (q := q) question ρ valid) π (randomEquiv U Ω u w n s q z) ↔
      FAFStrategyExtraction.Accepts question ρ valid (reference π) (larger π) z := by
  unfold Passes system
  simp only [Equiv.symm_apply_apply]
  constructor
  · rintro ⟨v, hv, he⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hp, hcoh⟩ := Finset.mem_filter.mp hp
    have hext := (parts_extend_iff question z p π).mp
      ((extends_merge_iff _ hcoh π).mp he)
    obtain ⟨b, _, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨a, ha, hpa⟩ := Finset.mem_image.mp hp
    subst p
    intro i
    have hai := Fintype.mem_piFinset.mp ha i
    obtain ⟨B, hB, hpattern⟩ := Finset.mem_image.mp hai
    have hBacc := (Finset.mem_filter.mp hB).2
    have hb : b = fun j ↦ reference π z.1 (z.2.1.2 j) := funext fun j ↦ (hext.1 j).symm
    subst b
    apply side_acceptance_transfer B (larger π (question z.1 (z.2.1.1 i))) _ _ ?_ hBacc
    intro g hg
    apply hext.2 i g (B g)
    change a i g = some (B g)
    rw [← hpattern]
    exact if_pos hg
  · intro h
    let R := reference π z.1
    let A := fun ω ↦ larger π (question z.1 ω)
    let p := FAFPatterns.transcript (ρ z.1) (valid z.1) R A z.2.1.1 z.2.1.2 z.2.2
    have hp : p ∈ FAFPatterns.patterns (ρ z.1) (valid z.1) z.2.1.1 z.2.1.2 z.2.2 :=
      Lax323828.FAFPatterns.transcript_mem _ _ R A _ _ _ h
    have hext : ∀ j, Extends π (parts question z p j) := by
      apply (parts_extend_iff question z p π).mpr
      refine ⟨fun _ ↦ rfl, ?_⟩
      intro i g b hb
      dsimp [p, FAFPatterns.transcript, restrict] at hb
      split_ifs at hb with hg
      exact Option.some.inj hb
    have hc := coherent_of_extensions π _ hext
    exact ⟨merge (parts question z p),
      Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hc⟩, rfl⟩,
      (extends_merge_iff _ hc π).mpr hext⟩

/--
---
conclusion: Lax323828.FAFLocalTests.free_bits
---
Filtering for consistency and merging views only decrease the number of
enumerated transcripts.
-/
theorem faf_local_free_bits {U Ω W : Type} [Fintype U] [Fintype Ω] [Fintype W]
    {u w n s q : ℕ} (question : U → Ω → W)
    (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → Coordinate w) :
    ∀ seed, ((system (n := n) (s := s) (q := q) question ρ valid).accepting seed).card ≤
      2 ^ (q + n * s) := by
  intro seed
  exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (Lax323828.FAFPatterns.free_bits _ _ _ _ _))

/--
---
conclusion: Lax323828.FAFLocalTests.acceptance_probability
---
The random-choice numbering is a bijection, and acceptance agrees pointwise.
-/
theorem faf_local_probability {U Ω W : Type} [Fintype U] [Fintype Ω] [Fintype W]
    {u w n s q : ℕ} (question : U → Ω → W)
    (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → Coordinate w)
    (π : Oracle (Fintype.card (Index U W u w))) :
    probability (Passes (system (n := n) (s := s) (q := q) question ρ valid) π) =
      probability (FAFStrategyExtraction.Accepts (n := n) (s := s) (q := q)
        question ρ valid (reference π) (larger π)) := by
  symm
  exact finite_probability_equiv (randomEquiv U Ω u w n s q) _ _
    (fun z ↦ (Lax323828.FAFLocalTests.passes_iff question ρ valid π z).symm)

/--
---
conclusion: Lax323828.FAFLocalTests.perfect_completeness
---
Encode the evaluation tables of perfect prover strategies as one proof.
-/
theorem faf_local_perfect_completeness {U Ω W : Type} [Fintype U] [Fintype Ω] [Fintype W]
    {u w n s q : ℕ} (question : U → Ω → W)
    (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → Coordinate w)
    (P : W → LongCode.Word w) (Q : U → LongCode.Word u)
    (hvalid : ∀ v ω, valid v ω (P (question v ω)) = true)
    (hproject : ∀ v ω, ρ v ω (P (question v ω)) = Q v) :
    Complete (system (n := n) (s := s) (q := q) question ρ valid) := by
  let π : Oracle (Fintype.card (Index U W u w)) := fun i ↦
    match (indexEquiv U W u w).symm i with
    | .inl (v, g) => g (Q v)
    | .inr (v, g) => g (P v)
  refine ⟨π, ?_⟩
  intro seed
  obtain ⟨z, rfl⟩ := (randomEquiv U Ω u w n s q).surjective seed
  apply (Lax323828.FAFLocalTests.passes_iff question ρ valid π z).mpr
  have hR : reference π = fun v ↦ evaluation (Q v) := by
    funext v g
    simp [reference, π, evaluation]
  have hA : larger π = fun v ↦ evaluation (P v) := by
    funext v g
    simp [larger, π, evaluation]
  rw [hR, hA]
  exact Lax323828.FAFTest.perfect_completeness _ _ (Q z.1) (fun ω ↦ P (question z.1 ω))
    (hvalid z.1) (hproject z.1) _ _ _

/--
---
conclusion: Lax323828.FAFLocalTests.soundness
---
Apply finite FAF soundness to the two table families decoded from each
global proof, and use the exact acceptance-probability identity.
-/
theorem faf_local_soundness (l : ℕ) (hl : 0 < l) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w →
      ∀ {U Ω W : Type} [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
        [Fintype W] [DecidableEq W],
      ∀ u : ℕ, ∀ (question : U → Ω → W)
        (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → Coordinate w),
        (∀ (P : W → Option (LongCode.Word w)) (Q : U → Option (LongCode.Word u)),
          probability (DecodedStrategies.Wins question (FAFStrategyExtraction.Relation ρ valid) P Q) <
            FAFComposition.gameThreshold l s) →
        Sound (system (n := 10 * l) (s := s) (q := 10 * l * s) question ρ valid)
          ((1 / 2 : ℝ) ^ (20 * l * l * s)) := by
  obtain ⟨s₀, hs₀⟩ := Lax323828.FAFComposition.soundness l hl
  refine ⟨s₀, fun s hs ↦ ?_⟩
  obtain ⟨w₀, hw₀⟩ := hs₀ s hs
  refine ⟨w₀, fun w hw ↦ ?_⟩
  intro U Ω W _ _ _ _ _ _ u question ρ valid hgame π
  rw [Lax323828.FAFLocalTests.acceptance_probability]
  exact (hw₀ w hw u question ρ valid (reference π) (larger π) hgame).le

/--
---
conclusion: Lax323828.FAFLocalTests.proof_length
---
Count one Boolean coordinate for every entry in every long-code table.
-/
theorem faf_local_proof_length (U W : Type) [Fintype U] [Fintype W] (u w : ℕ) :
    Fintype.card (Index U W u w) =
      Fintype.card U * 2 ^ (2 ^ u) + Fintype.card W * 2 ^ (2 ^ w) := by
  simp [Index, Coordinate, LongCode.Word]

/--
---
conclusion: Lax323828.FAFLocalTests.random_choices
---
Multiply the independent choices of the reference question, extensions,
reference functions, and CNA functions.
-/
theorem faf_local_random_choices (U Ω : Type) [Fintype U] [Fintype Ω] (u w n s q : ℕ) :
    Fintype.card (Randomness U Ω u w n s q) =
      Fintype.card U * (Fintype.card Ω ^ n * (2 ^ (2 ^ u)) ^ q * ((2 ^ (2 ^ w)) ^ s) ^ n) := by
  simp [Randomness, FAFStrategyExtraction.Seed, Coordinate, LongCode.Word]

end Lax323828Proofs
