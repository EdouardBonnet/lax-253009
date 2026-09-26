import Lax253009.LongCode
import Lax253009.CNASoundness
import Lax253009.ManyTableConsistency

/-!
---
title: The finite few-amortized-free-bits test
type: theorem
---
Fix a small variable set and a distribution of larger sets. Each larger
set carries a purported long code and a constraint predicate. The verifier
reads $q$ random functions on the small set, then checks $n$ independently
chosen larger tables using the CNA test with side conditions enforcing both
the constraints and agreement with the reference answers.

The rejection bound combines CNA decoding errors and the many-table
agreement estimate. It is uniform in the reference table, which need not
be a genuine long code. The projections and constraints are explicit finite
data; efficient construction from an NP input is a separate obligation.
-/

namespace Lax253009.FAFTest

open LongCode FiniteProbability CNASoundness

noncomputable def condition {Ω : Type} {u w q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (R : Table u) (ω : Ω) (g : Fin q → Coordinate u) : Coordinate w :=
  fun y ↦ valid ω y && decide (∀ j, g j (ρ ω y) = R (g j))

def Accepts {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (R : Table u) (A : Ω → Table w)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u)
    (f : Fin n → Fin s → Coordinate w) : Prop :=
  ∀ i, AcceptsWithCondition (A (ω i)) (f i) (condition ρ valid R (ω i) g)

axiom perfect_completeness {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (x : Word u) (y : Ω → Word w)
    (hvalid : ∀ ω, valid ω (y ω) = true) (hproject : ∀ ω, ρ ω (y ω) = x)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u) (f : Fin n → Fin s → Coordinate w) :
    Accepts ρ valid (evaluation x) (fun ω ↦ evaluation (y ω)) ω g f

noncomputable def projected {Ω : Type} {u w : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (D : Ω → Finset (Word w)) (ω : Ω) : Finset (Word u) :=
  ((D ω).filter (fun y ↦ valid ω y = true)).image (ρ ω)

axiom acceptance_bound {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (u w n s q : ℕ) (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (R : Table u) (A : Ω → Table w) (D : Ω → Finset (Word w))
    (B k : ℕ) (p δ : ℝ) (hp : 0 ≤ p)
    (hB : ∀ ω, (D ω).card ≤ B)
    (hdecode : ∀ ω h, probability (BadWithCondition (s := s) (A ω) (D ω) h) ≤ δ)
    (hpoint : ∀ x, probability (fun ω ↦ x ∈ projected ρ valid D ω) ≤ p)
    (hsmall : (n : ℝ) * B * p ≤ 1) :
    probability (fun z : ((Fin n → Ω) × (Fin q → Coordinate u)) ×
        (Fin n → Fin s → Coordinate w) ↦ Accepts ρ valid R A z.1.1 z.1.2 z.2) ≤
      n * δ + (2 : ℝ) ^ n * ((n : ℝ) * B * p) ^ (n - k) +
        (B : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ (k + 1)) ^ q

end Lax253009.FAFTest
