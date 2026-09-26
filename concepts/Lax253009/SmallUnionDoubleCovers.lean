import Lax253009.DoubleCoverBounds

/-!
---
title: Small-union weighted double-cover estimate
type: theorem
---
If every coefficient is at most $\delta$, double covers of a set of size
$t$ have total weight at most a dimension-independent constant times
$\delta^{m-2t}$. This is the estimate in Lemma 4.16. Extract $2t$
positions that still cover every point twice. Each remaining support is
one of at most $2^t$ subsets of their union.
-/

namespace Lax253009.SmallUnionDoubleCovers

open HigherMoments
open scoped BigOperators

noncomputable def weight {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (m t : ℕ) : ℝ := by
  classical
  exact ∑ S : Fin m → Finset ι,
    if DoubleCover S ∧ (Finset.univ.biUnion S).card = t then ∏ j, c (S j) else 0

axiom bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (l m t : ℕ) (δ : ℝ)
    (hc : ∀ S, 0 ≤ c S) (hsmall : ∀ S, c S ≤ δ) (hδ : 0 ≤ δ)
    (hdegree : ∀ S, l < S.card → c S = 0) (henergy : ∑ S, c S ^ 2 ≤ 1)
    (hmt : 2 * t ≤ m) :
  weight c m t ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ t * δ) ^ (m - 2 * t) *
    (1 + (3 : ℝ) ^ (l * (4 * t + 1) * 2 ^ (2 * t)))

end Lax253009.SmallUnionDoubleCovers
