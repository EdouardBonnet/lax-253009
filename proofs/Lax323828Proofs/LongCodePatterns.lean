import Lax323828.LongCodePatterns
import Mathlib.Tactic

namespace Lax323828Proofs

open Lax323828.LongCode Lax323828.LongCodePatterns

private theorem answers_determine_queries {w s : ℕ} (f : Fin s → Coordinate w)
    {A A' : Table w} (ha : Accepts A f) (ha' : Accepts A' f)
    (heq : ∀ i, A (f i) = A' (f i)) :
    ∀ g, Queried f g → A g = A' g := by
  intro g hg
  rcases hg with ⟨i, rfl⟩ | ⟨B, rfl⟩
  · exact heq i
  · rw [ha B, ha' B]
    exact congrArg B (funext heq)

private theorem pattern_count {w s : ℕ} (f : Fin s → Coordinate w)
    (Q : Coordinate w → Prop) (P : Table w → Prop) [DecidablePred P]
    (hquery : ∀ i, Q (f i))
    (hdet : ∀ A A', P A → P A' → (∀ i, A (f i) = A' (f i)) →
      ∀ g, Q g → A g = A' g) :
    ((Finset.univ.filter P).image (restrict Q)).card ≤ 2 ^ s := by
  classical
  let initial (t : Pattern w) : Word s := fun i ↦ (t (f i)).getD false
  have hinj : Set.InjOn initial
      (((Finset.univ.filter P).image (restrict Q)) : Set (Pattern w)) := by
    intro t ht t' ht' heq
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp ht'
    have hinit : ∀ i, A (f i) = A' (f i) := by
      intro i
      have hi := congrFun heq i
      simpa [initial, restrict, hquery i] using hi
    funext g
    by_cases hg : Q g
    · simp only [restrict, if_pos hg]
      exact congrArg some (hdet A A' (Finset.mem_filter.mp hA).2
        (Finset.mem_filter.mp hA').2 hinit g hg)
    · simp [restrict, hg]
  have hcard := Finset.card_le_card_of_injOn initial
    (t := (Finset.univ : Finset (Word s))) (fun _ _ ↦ Finset.mem_univ _) hinj
  simpa using hcard

/--
---
conclusion: Lax323828.LongCodePatterns.free_bits
---
The map from an accepting pattern to its initial s answers is injective.
-/
theorem longCode_free_bits {w s : ℕ} (f : Fin s → Coordinate w) :
    (patterns f).card ≤ 2 ^ s := by
  classical
  exact pattern_count f (Queried f) (fun A ↦ Accepts A f)
    (fun i ↦ Or.inl ⟨i, rfl⟩)
    (fun _ _ ha ha' heq ↦ answers_determine_queries f ha ha' heq)

/--
---
conclusion: Lax323828.LongCodePatterns.side_free_bits
---
Each added query is constrained to equal a base query, so the initial
s answers still determine every answer in an accepting pattern.
-/
theorem longCode_side_free_bits {w s : ℕ} (f : Fin s → Coordinate w)
    (h : Coordinate w) : (sidePatterns f h).card ≤ 2 ^ s := by
  classical
  apply pattern_count f (SideQueried f h) (fun A ↦ AcceptsWithCondition A f h)
  · intro i
    exact ⟨f i, Or.inl ⟨i, rfl⟩, fun _ _ ↦ rfl⟩
  · intro A A' ha ha' heq g' hg'
    obtain ⟨g, hg, hgg'⟩ := hg'
    rw [← ha.2 g hg g' hgg', ← ha'.2 g hg g' hgg']
    exact answers_determine_queries f ha.1 ha'.1 heq g hg

end Lax323828Proofs
