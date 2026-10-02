import Lax323828.OddNormalization
import Mathlib.Tactic

namespace Lax323828Proofs

open Lax323828.LongCode Lax323828.OddNormalization

private theorem negate_negate {w : ℕ} (g : Coordinate w) : negate (negate g) = g := by
  funext x
  simp [negate]

private theorem queried_composition {w s : ℕ} (f : Fin s → Coordinate w)
    (g : Coordinate w) (hg : Queried f g) : ∃ B, g = compose f B := by
  rcases hg with ⟨i, rfl⟩ | h
  · exact ⟨fun v ↦ v i, rfl⟩
  · exact h

private theorem queried_negate {w s : ℕ} (f : Fin s → Coordinate w)
    (g : Coordinate w) (hg : Queried f g) : Queried f (negate g) := by
  obtain ⟨B, rfl⟩ := queried_composition f g hg
  exact Or.inr ⟨fun v ↦ !(B v), rfl⟩

private theorem accepts_negate {w s : ℕ} (A : Table w)
    (f : Fin s → Coordinate w) (hA : Accepts A f)
    (g : Coordinate w) (hg : Queried f g) : A (negate g) = !(A g) := by
  obtain ⟨B, rfl⟩ := queried_composition f g hg
  change A (compose f (fun v ↦ !(B v))) = !(A (compose f B))
  rw [hA, hA]

/--
---
conclusion: Lax323828.OddNormalization.odd
---
Both members of a complementary pair are either kept or replaced by evaluation.
-/
theorem normalized_table_odd {w : ℕ} (x₀ : Word w) (A : Table w)
    (g : Coordinate w) : oddify x₀ A (negate g) = !(oddify x₀ A g) := by
  simp only [oddify, negate_negate]
  cases A g <;> cases A (negate g) <;> simp [negate]

/--
---
conclusion: Lax323828.OddNormalization.same_queries
---
Acceptance checks the predicate defining a query and its Boolean complement.
-/
theorem normalized_same_queries {w s : ℕ} (x₀ : Word w) (A : Table w)
    (f : Fin s → Coordinate w) (hA : Accepts A f)
    (g : Coordinate w) (hg : Queried f g) : oddify x₀ A g = A g := by
  exact if_pos (accepts_negate A f hA g hg)

/--
---
conclusion: Lax323828.OddNormalization.preserves_acceptance
---
Every answer involved in the acceptance equations is unchanged.
-/
theorem normalized_acceptance {w s : ℕ} (x₀ : Word w) (A : Table w)
    (f : Fin s → Coordinate w) (hA : Accepts A f) :
    Accepts (oddify x₀ A) f := by
  intro B
  rw [Lax323828.OddNormalization.same_queries x₀ A f hA _ (Or.inr ⟨B, rfl⟩)]
  have hi (i : Fin s) := Lax323828.OddNormalization.same_queries x₀ A f hA _ (Or.inl ⟨i, rfl⟩)
  simp_rw [hi]
  exact hA B

/--
---
conclusion: Lax323828.OddNormalization.preserves_side_acceptance
---
The side condition identifies both a function and its complement with
queried functions. Such pairs are already consistent and are also kept.
-/
theorem normalized_side_acceptance {w s : ℕ} (x₀ : Word w) (A : Table w)
    (f : Fin s → Coordinate w) (h : Coordinate w) (hA : AcceptsWithCondition A f h) :
    AcceptsWithCondition (oddify x₀ A) f h := by
  refine ⟨Lax323828.OddNormalization.preserves_acceptance x₀ A f hA.1, ?_⟩
  intro g hg g' hgg'
  have heq := hA.2 g hg g' hgg'
  have hneg := hA.2 (negate g) (queried_negate f g hg) (negate g')
    (fun x hx ↦ congrArg Bool.not (hgg' x hx))
  have hpair : A (negate g') = !(A g') := by
    rw [← hneg, ← heq]
    exact accepts_negate A f hA.1 g hg
  rw [Lax323828.OddNormalization.same_queries x₀ A f hA.1 g hg]
  simpa only [oddify, if_pos hpair] using heq

end Lax323828Proofs
