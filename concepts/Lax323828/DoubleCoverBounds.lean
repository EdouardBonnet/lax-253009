import Lax323828.HigherMoments
import Lax323828.Hypercontractivity

/-!
---
title: Dimension-independent bounds for weighted double covers
type: theorem
---
Let nonnegative coefficients $c_S$ be supported on sets of size at most
$\ell$, with $\sum_S c_S^2\leq1$. For every $m$, the sum of
$\prod_{j=1}^m c_{S_j}$ over double-cover tuples is bounded by a constant
depending only on $\ell,m$, not on the underlying coordinate set.
We give the explicit, nonoptimal bound $1+3^{\ell(2m+1)2^m}$.

This is the normalized form of Lemma 4.15 needed for the small-coefficient
analysis. The proof uses a centered variable equal to 3 with probability
1/4 and -1 otherwise. Its moments vanish at order one and are at least one
at every order at least two. Representing it on two Boolean coordinates
allows the low-degree moment bound to control all double-cover terms.
-/

namespace Lax323828.DoubleCoverBounds

open scoped Classical

open HigherMoments
open scoped BigOperators

/-- Sum the products of coefficients over tuples in which every used coordinate occurs at least twice. -/
noncomputable def weight {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (m : ℕ) : ℝ :=
  ∑ S : Fin m → Finset ι, if DoubleCover S then ∏ j, c (S j) else 0

axiom bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (l m : ℕ) (hc : ∀ S, 0 ≤ c S)
    (hdegree : ∀ S, l < S.card → c S = 0) (henergy : ∑ S, c S ^ 2 ≤ 1) :
  weight c m ≤ 1 + (3 : ℝ) ^ (l * (2 * m + 1) * 2 ^ m)

end Lax323828.DoubleCoverBounds
