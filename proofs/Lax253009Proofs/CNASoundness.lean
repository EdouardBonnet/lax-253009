import Lax253009.CNASoundness
import Lax253009Proofs.FiniteProbability
import Lax253009Proofs.CNAParameters

namespace Lax253009Proofs

open Lax253009.LongCode Lax253009.CNASoundness Lax253009.FiniteProbability
open Lax253009.BooleanFourier Lax253009.CNAPointSoundness
open Lax253009.CNAQuantitativeSoundness Filter

/--
---
conclusion: Lax253009.CNASoundness.with_side_conditions
---
Choose a coefficient threshold that decays slowly enough to keep the decoding
set small. Fixed moment and degree cutoffs make the pointwise error decay
faster than the requested exponential rate. Finally increase the word width
to control small fibers. The decoding set is independent of the side condition.
-/
theorem cna_soundness_with_side_conditions (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (_hk : 0 < k) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w →
      ∀ A : Table w, ∃ S : Finset (Word w),
        (S.card : ℝ) ≤ Real.rpow 2 (ε * (s : ℝ)) ∧
        ∀ h : Coordinate w,
          probability (BadWithCondition (s := s) A S h) ≤ Real.rpow 2 (-(k : ℝ) * (s : ℝ)) := by
  classical
  obtain ⟨l, m, r, α, hl, hα, hα1, hr, hm, hs⟩ := cna_parameter_choice ε hε k
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.mp hs
  refine ⟨s₀, fun s hs ↦ ?_⟩
  obtain ⟨hspos, hlN, hcard, hlarge, hpoint⟩ := hs₀ s hs
  obtain ⟨w₀, hw₀⟩ := eventually_atTop.mp
    (cna_fiber_bound_eventually s (((2 : ℝ) ^ (k * s))⁻¹ / 2) (by positivity))
  refine ⟨w₀, fun w hw A ↦ ?_⟩
  have hF (g : Cube (Word w)) : |sign (A g)| ≤ 1 := by cases A g <;> norm_num [sign]
  refine ⟨decoding (fun g ↦ sign (A g)) l (α ^ s),
    (cna_decoding_card _ hF l hl _ (pow_pos hα s)).trans hcard, fun h ↦ ?_⟩
  have hb := cna_quantitative_soundness w s l m r hspos hl hlN
    (α ^ s) (((3 : ℝ) / 4) ^ s) (pow_pos hα s) (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num)) hr hm hlarge A h
  have he : Real.rpow 2 (-(k : ℝ) * (s : ℝ)) = ((2 : ℝ) ^ (k * s))⁻¹ := by
    change (2 : ℝ) ^ (-(k : ℝ) * (s : ℝ)) = _
    rw [show -(k : ℝ) * (s : ℝ) = -((k * s : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [he]
  apply hb.trans
  dsimp only [totalBound]
  have hfiber := hw₀ w hw
  linarith

/--
---
conclusion: Lax253009.CNASoundness.without_side_conditions
---
Use the side-condition theorem with the constant true condition. Agreement
on that condition is equality of functions, so its extra checks are automatic.
Use the proved side-condition theorem directly, with no archive statement
assumption.
-/
theorem cna_soundness_from_side_conditions (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (hk : 0 < k) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w →
      ∀ A : Table w, ∃ S : Finset (Word w),
        (S.card : ℝ) ≤ Real.rpow 2 (ε * (s : ℝ)) ∧
        probability (Bad (s := s) A S) ≤ Real.rpow 2 (-(k : ℝ) * (s : ℝ)) := by
  obtain ⟨s₀, hs₀⟩ := cna_soundness_with_side_conditions ε hε k hk
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
