import Lax253009.CNASoundness
import Lax253009Proofs.FiniteProbability

namespace Lax253009Proofs

open Lax253009.LongCode Lax253009.CNASoundness Lax253009.FiniteProbability

/--
---
conclusion: Lax253009.CNASoundness.without_side_conditions
---
Use the side-condition theorem with the constant true condition. Agreement
on that condition is equality of functions, so its extra checks are automatic.
The analytic side-condition theorem remains an explicit open assumption;
there is no dependency in the reverse direction.
-/
theorem cna_soundness_from_side_conditions (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (hk : 0 < k) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w →
      ∀ A : Table w, ∃ S : Finset (Word w),
        (S.card : ℝ) ≤ Real.rpow 2 (ε * (s : ℝ)) ∧
        probability (Bad (s := s) A S) ≤ Real.rpow 2 (-(k : ℝ) * (s : ℝ)) := by
  obtain ⟨s₀, hs₀⟩ := Lax253009.CNASoundness.with_side_conditions ε hε k hk
  refine ⟨s₀, fun s hs ↦ ?_⟩
  obtain ⟨w₀, hw₀⟩ := hs₀ s hs
  refine ⟨w₀, fun w hw A ↦ ?_⟩
  obtain ⟨S, hcard, hsound⟩ := hw₀ w hw A
  refine ⟨S, hcard, ?_⟩
  apply le_trans (finite_probability_mono _ (BadWithCondition A S (fun _ ↦ true)) ?_)
    (hsound (fun _ ↦ true))
  intro f hf
  refine ⟨⟨hf.1, ?_⟩, ?_⟩
  · intro g _ g' hgg'
    exact congrArg A (funext fun x ↦ hgg' x rfl)
  · rintro ⟨x, hx, _, hlook⟩
    exact hf.2 ⟨x, hx, hlook⟩

end Lax253009Proofs
