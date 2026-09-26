import Lax253009.FAFTest
import Lax253009.DecodedStrategies

/-!
---
title: From FAF acceptance to two-prover success
type: theorem
---
Combine the finite FAF soundness bound with extraction of two globally
consistent prover strategies. If the FAF test accepts with probability
$a$ and its no-common-answer error bound is $E$, the two-prover game has
strategies succeeding with probability at least $(a-E)p/(B+1)$.

The bound is quantitative and applies to arbitrary finite question spaces.
The CNA error and decoding-set bounds are explicit hypotheses so that
the independently proved CNA theorem can be applied uniformly to all tables.
-/

namespace Lax253009.FAFStrategyExtraction

open LongCode FiniteProbability

abbrev Seed (Ω : Type) (u w n s q : ℕ) :=
  ((Fin n → Ω) × (Fin q → Coordinate u)) × (Fin n → Fin s → Coordinate w)

def Relation {U Ω : Type} {u w : ℕ}
    (ρ : U → Ω → Word w → Word u) (valid : U → Ω → Coordinate w)
    (v : U) (ω : Ω) (y : Word w) (x : Word u) : Prop :=
  valid v ω y = true ∧ ρ v ω y = x

def Accepts {U Ω W : Type} {u w n s q : ℕ} (question : U → Ω → W)
    (ρ : U → Ω → Word w → Word u) (valid : U → Ω → Coordinate w)
    (R : U → Table u) (A : W → Table w) (z : U × Seed Ω u w n s q) : Prop :=
  FAFTest.Accepts (ρ z.1) (valid z.1) (R z.1) (fun ω ↦ A (question z.1 ω))
    z.2.1.1 z.2.1.2 z.2.2

noncomputable def errorBound (n B k q : ℕ) (p δ : ℝ) : ℝ :=
  n * δ + (2 : ℝ) ^ n * ((n : ℝ) * B * p) ^ (n - k) +
    (B : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ (k + 1)) ^ q

axiom finite_extraction {U Ω W : Type}
    [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
    [Fintype W] [DecidableEq W]
    (u w n s q : ℕ) (question : U → Ω → W)
    (ρ : U → Ω → Word w → Word u) (valid : U → Ω → Coordinate w)
    (R : U → Table u) (A : W → Table w) (D : W → Finset (Word w))
    (B k : ℕ) (p δ : ℝ) (hp : 0 ≤ p) (hδ : 0 ≤ δ)
    (hB : ∀ a, (D a).card ≤ B)
    (hdecode : ∀ a h, probability (CNASoundness.BadWithCondition (s := s) (A a) (D a) h) ≤ δ)
    (hsmall : (n : ℝ) * B * p ≤ 1) :
    ∃ P : W → Option (Word w), ∃ Q : U → Option (Word u),
      (probability (Accepts (n := n) (s := s) (q := q) question ρ valid R A) -
        errorBound n B k q p δ) * p / (B + 1) ≤
      probability (DecodedStrategies.Wins question (Relation ρ valid) P Q)

/-- Apply the proved asymptotic CNA theorem uniformly to the entire family
of first-prover tables. No decoding or soundness hypothesis is required. -/
axiom uniform_extraction (K : ℕ) (hK : 0 < K) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w →
      ∀ {U Ω W : Type} [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
        [Fintype W] [DecidableEq W],
      ∀ u n q k : ℕ, ∀ (question : U → Ω → W)
        (ρ : U → Ω → Word w → Word u) (valid : U → Ω → Coordinate w)
        (R : U → Table u) (A : W → Table w) (p : ℝ),
        0 ≤ p → (n : ℝ) * (2 : ℝ) ^ s * p ≤ 1 →
        ∃ P : W → Option (Word w), ∃ Q : U → Option (Word u),
          (probability (Accepts (n := n) (s := s) (q := q) question ρ valid R A) -
            errorBound n (2 ^ s) k q p (Real.rpow 2 (-(K : ℝ) * (s : ℝ)))) * p / ((2 : ℝ) ^ s + 1) ≤
          probability (DecodedStrategies.Wins question (Relation ρ valid) P Q)

end Lax253009.FAFStrategyExtraction
