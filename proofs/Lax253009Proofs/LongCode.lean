import Lax253009.LongCodeCorrectness
import Mathlib.Tactic

namespace Lax253009Proofs

open Lax253009.LongCode

/--
---
conclusion: Lax253009.LongCodeCorrectness.perfect_completeness
---
Evaluation commutes with Boolean composition.
-/
theorem longCode_completeness {w s : ℕ} (x : Word w) (f : Fin s → Coordinate w) :
    Accepts (evaluation x) f := by
  intro B
  rfl

private theorem looksLike_of_initial {w s : ℕ} (A : Table w)
    (f : Fin s → Coordinate w) (h : Accepts A f) (x : Word w)
    (hx : ∀ i, A (f i) = f i x) : LooksLike A f x := by
  refine ⟨hx, fun B ↦ ?_⟩
  rw [h B]
  exact congrArg B (funext hx)

/--
---
conclusion: Lax253009.LongCodeCorrectness.local_decoding
---
If no word produces the initial answer vector, the predicate recognizing
that vector composes to the constant false function, contradicting acceptance.
-/
theorem longCode_local_decoding {w s : ℕ} (A : Table w)
    (f : Fin s → Coordinate w) (h : Accepts A f) :
    ∃ x : Word w, LooksLike A f x := by
  classical
  have hex : ∃ x : Word w, ∀ i, A (f i) = f i x := by
    by_contra hn
    let a : Word s := fun i ↦ A (f i)
    let B : Word s → Bool := fun y ↦ decide (y = a)
    have hzero : compose f B = fun _ ↦ false := by
      funext x
      apply decide_eq_false
      intro heq
      exact hn ⟨x, fun i ↦ (congrFun heq i).symm⟩
    have htrue := h B
    have hfalse := h (fun _ ↦ false)
    change A (fun _ ↦ false) = false at hfalse
    rw [hzero, hfalse] at htrue
    simp [B, a] at htrue
  obtain ⟨x, hx⟩ := hex
  exact ⟨x, looksLike_of_initial A f h x hx⟩

/--
---
conclusion: Lax253009.LongCodeCorrectness.side_condition_completeness
---
Functions agreeing on the side condition have equal values at a satisfying word.
-/
theorem longCode_side_completeness {w s : ℕ} (x : Word w)
    (f : Fin s → Coordinate w) (h : Coordinate w) (hx : h x = true) :
    AcceptsWithCondition (evaluation x) f h := by
  refine ⟨Lax253009.LongCodeCorrectness.perfect_completeness x f, ?_⟩
  intro g _ g' hgg'
  exact hgg' x hx

/--
---
conclusion: Lax253009.LongCodeCorrectness.side_condition_decoding
---
The predicate recognizing the initial answer vector cannot vanish on every
satisfying word: step (3) would identify its accepted answer with false.
-/
theorem longCode_side_decoding {w s : ℕ} (A : Table w)
    (f : Fin s → Coordinate w) (h : Coordinate w)
    (haccept : AcceptsWithCondition A f h) :
    ∃ x : Word w, h x = true ∧ LooksLike A f x := by
  classical
  have hex : ∃ x : Word w, h x = true ∧ ∀ i, A (f i) = f i x := by
    by_contra hn
    let a : Word s := fun i ↦ A (f i)
    let B : Word s → Bool := fun y ↦ decide (y = a)
    have hagree : AgreesOn h (compose f B) (fun _ ↦ false) := by
      intro x hx
      apply decide_eq_false
      intro heq
      exact hn ⟨x, hx, fun i ↦ (congrFun heq i).symm⟩
    have hsame := haccept.2 (compose f B) (Or.inr ⟨B, rfl⟩) _ hagree
    have htrue := haccept.1 B
    have hfalse := haccept.1 (fun _ ↦ false)
    change A (fun _ ↦ false) = false at hfalse
    rw [hsame, hfalse] at htrue
    simp [B, a] at htrue
  obtain ⟨x, hx, hf⟩ := hex
  exact ⟨x, hx, looksLike_of_initial A f haccept.1 x hf⟩

end Lax253009Proofs
