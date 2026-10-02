import Lax323828.FiniteProbability
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset

/-!
---
title: Agreement among many decoded tables
type: theorem
---
The finite counting argument behind Lemmas 5.7 and 5.8. Each independently
sampled table supplies at most $B$ projected assignments, and each fixed
assignment occurs with probability at most $p$. A selection with at most
$k$ distinct assignments forces all remaining tables to meet the union
of at most $k$ representative tables. Random Boolean functions are unlikely
to be constant on a selection with many distinct assignments.

These bounds concern finite probability spaces. They do not assert a PCP
construction or its computational complexity.
-/

namespace Lax323828.ManyTableConsistency

open FiniteProbability

def LowDiversity {ι Ω X : Type} [Fintype ι] [DecidableEq X]
    (S : Ω → Finset X) (k : ℕ) (w : ι → Ω) : Prop :=
  ∃ y : ι → X, (∀ i, y i ∈ S (w i)) ∧ (Finset.univ.image y).card ≤ k

def Agreement {ι Ω X : Type} (S : Ω → Finset X) (q : ℕ)
    (w : ι → Ω) (g : Fin q → X → Bool) : Prop :=
  ∃ y : ι → X, (∀ i, y i ∈ S (w i)) ∧ ∀ j, ∃ b, ∀ i, g j (y i) = b

axiom low_diversity_bound {ι Ω X : Type} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Nonempty Ω] [Fintype X] [DecidableEq X]
    (S : Ω → Finset X) (B k : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hB : ∀ w, (S w).card ≤ B)
    (hpoint : ∀ x, probability (fun w ↦ x ∈ S w) ≤ p)
    (hsmall : (Fintype.card ι : ℝ) * B * p ≤ 1) :
    probability (LowDiversity (ι := ι) S k) ≤
      (2 : ℝ) ^ Fintype.card ι * ((Fintype.card ι : ℝ) * B * p) ^ (Fintype.card ι - k)

axiom agreement_bound {ι Ω X : Type} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Nonempty Ω] [Fintype X] [DecidableEq X]
    (S : Ω → Finset X) (B k q : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hB : ∀ w, (S w).card ≤ B)
    (hpoint : ∀ x, probability (fun w ↦ x ∈ S w) ≤ p)
    (hsmall : (Fintype.card ι : ℝ) * B * p ≤ 1) :
    probability (fun z : (ι → Ω) × (Fin q → X → Bool) ↦ Agreement S q z.1 z.2) ≤
      (2 : ℝ) ^ Fintype.card ι * ((Fintype.card ι : ℝ) * B * p) ^ (Fintype.card ι - k) +
      (B : ℝ) ^ Fintype.card ι * (2 * (1 / 2 : ℝ) ^ (k + 1)) ^ q

end Lax323828.ManyTableConsistency
