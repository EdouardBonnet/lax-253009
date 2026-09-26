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
probability, and a union has probability at most the sum of the two
probabilities.

For a real random variable $X$ on a nonempty finite space, $t>0$, and even
$m$, Markov's inequality applied to $X^m$ gives
$\Pr[X\geq t]\leq\mathbb E[X^m]/t^m$. This is the finite tail estimate
used in Corollaries 4.6 and 4.11.
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

end Lax253009.FiniteProbability
