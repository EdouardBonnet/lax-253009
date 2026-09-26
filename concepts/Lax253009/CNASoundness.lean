import Lax253009.LongCode
import Lax253009.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi

/-!
---
title: Soundness of the complete nonadaptive long-code test
type: theorem
---
For every $\varepsilon>0$ and positive integer $k$, and all sufficiently
large $s$ and then $w$, each purported long code $A$ has a set $S$ of at
most $2^{\varepsilon s}$ words such that the CNA test, except with
probability $2^{-ks}$, either rejects or agrees with evaluation at a word
in $S$. This is Theorem 4.2 of Håstad's paper.

The stronger Theorem 4.17 uses the same quantifiers and a set $S$ chosen
independently of the side condition $h$. For every $h$, except with the
same probability, the extended test rejects or agrees with evaluation at
some $x\in S$ satisfying $h(x)$.

The probability is uniform over the $s$ independently chosen Boolean
functions. The thresholds for $s$ depend only on $\varepsilon,k$; the
threshold for $w$ may additionally depend on $s$. Both statements concern
arbitrary tables, without assuming they are genuine long codes.
-/

namespace Lax253009.CNASoundness

open LongCode FiniteProbability

def Bad {w s : ℕ} (A : Table w) (S : Finset (Word w))
    (f : Fin s → Coordinate w) : Prop :=
  Accepts A f ∧ ¬ ∃ x ∈ S, LooksLike A f x

def BadWithCondition {w s : ℕ} (A : Table w) (S : Finset (Word w))
    (h : Coordinate w) (f : Fin s → Coordinate w) : Prop :=
  AcceptsWithCondition A f h ∧ ¬ ∃ x ∈ S, h x = true ∧ LooksLike A f x

axiom with_side_conditions (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 0 < k) :
  ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w →
    ∀ A : Table w, ∃ S : Finset (Word w),
      (S.card : ℝ) ≤ Real.rpow 2 (ε * (s : ℝ)) ∧
      ∀ h : Coordinate w,
        probability (BadWithCondition (s := s) A S h) ≤ Real.rpow 2 (-(k : ℝ) * (s : ℝ))

axiom without_side_conditions (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 0 < k) :
  ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w →
    ∀ A : Table w, ∃ S : Finset (Word w),
      (S.card : ℝ) ≤ Real.rpow 2 (ε * (s : ℝ)) ∧
      probability (Bad (s := s) A S) ≤ Real.rpow 2 (-(k : ℝ) * (s : ℝ))

end Lax253009.CNASoundness
