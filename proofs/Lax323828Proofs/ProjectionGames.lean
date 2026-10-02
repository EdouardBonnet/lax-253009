import Lax323828.ProjectionGames
import Lax323828Proofs.FiniteProbability

namespace Lax323828Proofs

open Lax323828 Lax323828.ProjectionGames Lax323828.FiniteProbability
open scoped BigOperators

@[simp] theorem projection_reverse_reverse {V D A : Type} (C : System V D A)
    (z : V × D) : C.reverse (C.reverse z) = z := C.reverse_involutive z

/--
---
conclusion: Lax323828.ProjectionGames.completeness
---
Give the first prover the two labels supplied by a satisfying assignment.
-/
theorem projection_game_complete {V D A : Type} (C : System V D A)
    (h : C.Satisfiable) :
    ∃ P : V × D → A × A, ∃ Q : V → A,
      ∀ v ω, C.Test v ω (P (C.question v ω)) (Q v) := by
  classical
  obtain ⟨a, ha⟩ := h
  refine ⟨fun z ↦ (a z.1, a (C.reverse z).1), a, ?_⟩
  intro v ω
  constructor
  · exact not_not.mp (ha (C.question v ω))
  · rcases ω with ⟨d, b⟩
    cases b <;> simp [System.project, System.question]

private def dartFlip {V D A : Type} (C : System V D A) :
    ((V × D) × Bool) ≃ ((V × D) × Bool) where
  toFun z := (if z.2 then C.reverse z.1 else z.1, z.2)
  invFun z := (if z.2 then C.reverse z.1 else z.1, z.2)
  left_inv := by rintro ⟨z, b⟩; cases b <;> simp
  right_inv := by rintro ⟨z, b⟩; cases b <;> simp

private def dartEquiv {V D A : Type} (C : System V D A) :
    (V × (D × Bool)) ≃ ((V × D) × Bool) :=
  (Equiv.prodAssoc V D Bool).symm.trans (dartFlip C)

private def DartWins {V D A : Type} (C : System V D A)
    (P : V × D → A × A) (Q : V → A) (z : V × D) (b : Bool) : Prop :=
  C.relation z (P z).1 (P z).2 = true ∧ System.project b (P z) = Q (C.endpoint z b)

private theorem dart_wins_both {V D A : Type} (C : System V D A)
    (P : V × D → A × A) (Q : V → A) (z : V × D)
    (hf : DartWins C P Q z false) (ht : DartWins C P Q z true) :
    ¬ C.Violated Q z := by
  have hf' : (P z).1 = Q z.1 := hf.2
  have ht' : (P z).2 = Q (C.reverse z).1 := ht.2
  unfold System.Violated
  rw [← hf', ← ht', hf.1]
  simp

private theorem total_projection_game_sound {V D A : Type}
    [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
    (C : System V D A) (γ : ℝ) (h : C.Sound γ)
    (P : V × D → A × A) (Q : V → A) :
    probability (fun z : V × (D × Bool) ↦ C.Test z.1 z.2 (P (C.question z.1 z.2)) (Q z.1))
      ≤ 1 - γ / 2 := by
  classical
  have he := finite_probability_equiv (dartEquiv C)
    (fun z : V × (D × Bool) ↦ C.Test z.1 z.2 (P (C.question z.1 z.2)) (Q z.1))
    (fun z : (V × D) × Bool ↦ DartWins C P Q z.1 z.2) (by
      rintro ⟨v, d, b⟩
      cases b <;> simp [dartEquiv, dartFlip, DartWins, System.Test, System.question,
        System.endpoint])
  rw [he, finite_probability_product]
  have hp (z : V × D) : probability (DartWins C P Q z) ≤
      1 - (if C.Violated Q z then (1 : ℝ) else 0) / 2 := by
    rw [finite_probability_indicator, Fintype.expect_eq_sum_div_card]
    simp only [Fintype.sum_bool, Fintype.card_bool, Nat.cast_ofNat]
    by_cases hv : C.Violated Q z
    · have hn : ¬ (DartWins C P Q z false ∧ DartWins C P Q z true) :=
        fun hh ↦ dart_wins_both C P Q z hh.1 hh.2 hv
      by_cases hf : DartWins C P Q z false <;>
        by_cases ht : DartWins C P Q z true <;> norm_num [hf, ht, hv] at *
    · by_cases hf : DartWins C P Q z false <;>
        by_cases ht : DartWins C P Q z true <;> norm_num [hf, ht, hv]
  calc
    _ ≤ 𝔼 z, (1 - (if C.Violated Q z then (1 : ℝ) else 0) / 2) :=
      Finset.expect_le_expect fun z _ ↦ hp z
    _ = 1 - probability (C.Violated Q) / 2 := by
      rw [Finset.expect_sub_distrib, Fintype.expect_const, ← Finset.expect_div,
        ← finite_probability_indicator]
    _ ≤ 1 - γ / 2 := by linarith [h Q]

/--
---
conclusion: Lax323828.ProjectionGames.soundness
---
Complete partial answers arbitrarily. Every violated constraint forces a
rejection on at least one of its two endpoint tests. The dart involution
identifies this sampling rule with uniform vertex and extension sampling.
-/
theorem projection_game_sound {V D A : Type} [Fintype V] [Nonempty V]
    [Fintype D] [Nonempty D] [Nonempty A]
    (C : System V D A) (γ : ℝ) (h : C.Sound γ)
    (P : V × D → Option (A × A)) (Q : V → Option A) :
    probability (DecodedStrategies.Wins C.question C.Test P Q) ≤ 1 - γ / 2 := by
  classical
  let a : A := Classical.arbitrary A
  let P' := fun z ↦ (P z).getD (a, a)
  let Q' := fun v ↦ (Q v).getD a
  apply le_trans (Lax323828.FiniteProbability.monotone _ _ ?_) (total_projection_game_sound C γ h P' Q')
  rintro z ⟨p, x, hp, hx, ht⟩
  simpa [P', Q', hp, hx] using ht

end Lax323828Proofs
