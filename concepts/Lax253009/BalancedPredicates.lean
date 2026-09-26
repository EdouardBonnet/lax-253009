import Lax253009.ExponentialBounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

/-!
---
title: Counting and concentration of uniformly balanced predicates
type: theorem
---
Predicates with exactly $n$ true values on an $N$-element set are counted
by $\binom{N}{n}$. When $N=2n$, they constitute at least a fraction
$1/(N+1)$ of all predicates.

For a fixed sign-valued function $G$ and a uniform balanced predicate $B$,
the absolute correlation sum has tail at most
$2(N+1)e^{-t^2/(2N)}$ at $t\geq0$, for $N>0$.
This bound is obtained by conditioning independent signs on balance.
It has an extra factor $N+1$ compared with the paper's pairing argument
in Lemma 4.7, but gives the same required asymptotic decay at
$t=N^{3/4}$ in the soundness proof.
-/

namespace Lax253009.BalancedPredicates

open BooleanFourier FiniteProbability
open scoped BigOperators

def predicates (κ : Type) [Fintype κ] [DecidableEq κ] (n : ℕ) : Finset (Cube κ) :=
  Finset.univ.filter fun B ↦ (Finset.univ.filter fun z ↦ B z = true).card = n

axiom count {κ : Type} [Fintype κ] [DecidableEq κ] (n : ℕ) :
  (predicates κ n).card = (Fintype.card κ).choose n

axiom central_mass {κ : Type} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hN : Fintype.card κ = 2 * n) :
  Fintype.card (Cube κ) ≤ (Fintype.card κ + 1) * (predicates κ n).card

axiom absolute_correlation_tail {κ : Type} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (G : Cube κ) (t : ℝ) (ht : 0 ≤ t) :
  probability (fun B : predicates κ n ↦ t ≤ |∑ z, sign (G z) * sign (B.val z)|) ≤
    2 * (Fintype.card κ + 1 : ℝ) * Real.exp (-t ^ 2 / (2 * Fintype.card κ))

end Lax253009.BalancedPredicates
