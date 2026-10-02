import Lax323828.FAFStrategyExtraction
import Lax323828Proofs.FAFTest
import Lax323828Proofs.DecodedStrategies

namespace Lax323828Proofs

open Lax323828.LongCode Lax323828.FiniteProbability
open Lax323828.FAFStrategyExtraction Lax323828.DecodedStrategies
open scoped BigOperators Classical

/--
---
conclusion: Lax323828.FAFStrategyExtraction.finite_extraction
---
Noncommon questions contribute at most the finite FAF error. Therefore
common questions have mass at least acceptance minus that error. Apply the
proved rounding theorem to their decoded assignments.
-/
theorem faf_strategy_extraction {U Ω W : Type}
    [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
    [Fintype W] [DecidableEq W]
    (u w n s q : ℕ) (question : U → Ω → W)
    (ρ : U → Ω → Word w → Word u) (valid : U → Ω → Coordinate w)
    (R : U → Table u) (A : W → Table w) (D : W → Finset (Word w))
    (B k : ℕ) (p δ : ℝ) (hp : 0 ≤ p) (hδ : 0 ≤ δ)
    (hB : ∀ a, (D a).card ≤ B)
    (hdecode : ∀ a h, probability (Lax323828.CNASoundness.BadWithCondition (s := s) (A a) (D a) h) ≤ δ)
    (hsmall : (n : ℝ) * B * p ≤ 1) :
    ∃ P : W → Option (Word w), ∃ Q : U → Option (Word u),
      (probability (Lax323828.FAFStrategyExtraction.Accepts (n := n) (s := s) (q := q) question ρ valid R A) -
        errorBound n B k q p δ) * p / (B + 1) ≤
      probability (Wins question (Relation ρ valid) P Q) := by
  let C := Common question (Relation ρ valid) D p
  let E := errorBound n B k q p δ
  have hE : 0 ≤ E := by dsimp [E, errorBound]; positivity
  have hcond (v : U) :
      probability (fun z : Seed Ω u w n s q ↦
        Lax323828.FAFStrategyExtraction.Accepts question ρ valid R A (v, z)) ≤
      (if C v then (1 : ℝ) else 0) + E := by
    by_cases hv : C v
    · rw [if_pos hv]
      exact (finite_probability_le_one _).trans (by linarith)
    · rw [if_neg hv, zero_add]
      have hpoint (x : Word u) : probability (fun ω ↦ x ∈
          Lax323828.FAFTest.projected (ρ v) (valid v) (fun ω ↦ D (question v ω)) ω) ≤ p := by
        apply le_of_not_ge
        intro hx
        apply hv
        refine ⟨x, ?_⟩
        convert hx using 1
        congr 1
        apply congrArg probability
        funext ω
        simp only [Lax323828.FAFTest.projected, Finset.mem_image, Finset.mem_filter, Relation]
        aesop
      exact Lax323828.FAFTest.acceptance_bound u w n s q (ρ v) (valid v) (R v)
        (fun ω ↦ A (question v ω)) (fun ω ↦ D (question v ω)) B k p δ hp
        (fun ω ↦ hB _) (fun ω h ↦ hdecode _ h) hpoint hsmall
  have hmass : probability (Lax323828.FAFStrategyExtraction.Accepts
      (n := n) (s := s) (q := q) question ρ valid R A) ≤ probability C + E := by
    rw [finite_probability_product (fun v z ↦
      Lax323828.FAFStrategyExtraction.Accepts question ρ valid R A (v, z))]
    calc
      _ ≤ 𝔼 v : U, ((if C v then (1 : ℝ) else 0) + E) :=
        Finset.expect_le_expect (fun v _ ↦ hcond v)
      _ = _ := by rw [Finset.expect_add_distrib, Fintype.expect_const, ← finite_probability_indicator]
  obtain ⟨P, Q, hPQ⟩ := Lax323828.DecodedStrategies.extract_strategies question (Relation ρ valid) D B hB p hp
  refine ⟨P, Q, le_trans ?_ hPQ⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right (by linarith) hp

/--
---
conclusion: Lax323828.FAFStrategyExtraction.uniform_extraction
---
Choose every decoding set from the proved CNA soundness theorem with
epsilon one, then instantiate the finite extraction theorem. The thresholds
are independent of all tables, reference answers, projections and constraints.
-/
theorem faf_uniform_strategy_extraction (K : ℕ) (hK : 0 < K) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w →
      ∀ {U Ω W : Type} [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
        [Fintype W] [DecidableEq W],
      ∀ u n q k : ℕ, ∀ (question : U → Ω → W)
        (ρ : U → Ω → Word w → Word u) (valid : U → Ω → Coordinate w)
        (R : U → Table u) (A : W → Table w) (p : ℝ),
        0 ≤ p → (n : ℝ) * (2 : ℝ) ^ s * p ≤ 1 →
        ∃ P : W → Option (Word w), ∃ Q : U → Option (Word u),
          (probability (Lax323828.FAFStrategyExtraction.Accepts (n := n) (s := s) (q := q) question ρ valid R A) -
            errorBound n (2 ^ s) k q p (Real.rpow 2 (-(K : ℝ) * (s : ℝ)))) * p / ((2 : ℝ) ^ s + 1) ≤
          probability (Wins question (Relation ρ valid) P Q) := by
  obtain ⟨s₀, hs₀⟩ := Lax323828.CNASoundness.with_side_conditions 1 (by norm_num) K hK
  refine ⟨s₀, fun s hs ↦ ?_⟩
  obtain ⟨w₀, hw₀⟩ := hs₀ s hs
  refine ⟨w₀, fun w hw ↦ ?_⟩
  intro U Ω W _ _ _ _ _ _ u n q k question ρ valid R A p hp hsmall
  choose D hcard hdecode using fun a ↦ hw₀ w hw (A a)
  have hB (a : W) : (D a).card ≤ 2 ^ s := by
    have hc := hcard a
    change ((D a).card : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) * (s : ℝ)) at hc
    simp only [one_mul, Real.rpow_natCast] at hc
    exact_mod_cast hc
  have hres := Lax323828.FAFStrategyExtraction.finite_extraction u w n s q question ρ valid R A D (2 ^ s) k p
    (Real.rpow 2 (-(K : ℝ) * (s : ℝ))) hp (Real.rpow_pos_of_pos (by norm_num) _).le
    hB hdecode (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hsmall)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hres

end Lax323828Proofs
