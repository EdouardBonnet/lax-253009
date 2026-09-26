import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity

/-!
---
title: Uniform finite probability and even-moment tail bounds
type: theorem
---
An event in a finite sample space has probability equal to its cardinality
divided by the cardinality of the space. Event inclusion preserves this
probability, and the probability of a finite union is at most the sum of
the member probabilities. Restriction to a subset of mass at least $1/K$
increases event probabilities by at most a factor $K$.

For a real random variable $X$ on a nonempty finite space, $t>0$, and even
$m$, Markov's inequality applied to $X^m$ gives
$\Pr[X\geq t]\leq\mathbb E[X^m]/t^m$. This is the finite tail estimate
used in Corollaries 4.6 and 4.11. For $0\leq X\leq1$ and $q\geq0$, we
also prove $\mathbb E X^\ell\leq q^\ell+\Pr[X>q]$ by splitting at $q$.
-/

namespace Lax253009.FiniteProbability

open scoped BigOperators

noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

axiom monotone {α : Type} [Fintype α] (P Q : α → Prop) (h : ∀ x, P x → Q x) :
  probability P ≤ probability Q

axiom union_bound {α : Type} [Fintype α] (P Q : α → Prop) :
  probability (fun x ↦ P x ∨ Q x) ≤ probability P + probability Q

axiom even_moment_bound {α : Type} [Fintype α] [Nonempty α]
    (X : α → ℝ) (t : ℝ) (ht : 0 < t) (m : ℕ) (hm : Even m) :
  probability (fun x ↦ t ≤ X x) ≤ (𝔼 x, X x ^ m) / t ^ m

axiom restriction_bound {α : Type} [Fintype α] (s : Finset α) (hs : s.Nonempty)
    (K : ℝ) (hcard : (Fintype.card α : ℝ) ≤ K * s.card) (P : α → Prop) :
  probability (fun x : s ↦ P x.val) ≤ K * probability P

axiom finite_union_bound {α ι : Type} [Fintype α] [Fintype ι] (P : ι → α → Prop) :
  probability (fun x ↦ ∃ i, P i x) ≤ ∑ i, probability (P i)

axiom bounded_power_mean {α : Type} [Fintype α] [Nonempty α]
    (X : α → ℝ) (hX : ∀ x, 0 ≤ X x ∧ X x ≤ 1) (q : ℝ) (hq : 0 ≤ q) (l : ℕ) :
  (𝔼 x, X x ^ l) ≤ q ^ l + probability (fun x ↦ q < X x)

end Lax253009.FiniteProbability
