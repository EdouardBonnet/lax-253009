import Lax253009.FiniteProbability
import Mathlib.Data.Fintype.Pi

/-!
---
title: Dimension-independent bounds for tuple averaging
type: theorem
---
The average of t independent samples of a function in [-1,1] has variance
at most 1/t. Restricting to any event cannot increase its unnormalized
correlation with the centered sample average beyond 1/sqrt(t).
These bounds do not depend on the size of the sample alphabet. They provide
the averaging estimate for fortifying projection games by tuple questions.
-/

namespace Lax253009.TupleAveraging

open scoped BigOperators

axiom variance_bound {A : Type} [Fintype A] [Nonempty A]
    (t : ℕ) (ht : 0 < t) (f : A → ℝ) (hf : ∀ a, |f a| ≤ 1) :
    (𝔼 z : Fin t → A, ((𝔼 i, f (z i)) - (𝔼 a, f a)) ^ 2) ≤ 1 / (t : ℝ)

axiom restriction_correlation {A : Type} [Fintype A] [Nonempty A]
    (t : ℕ) (ht : 0 < t) (f : A → ℝ) (hf : ∀ a, |f a| ≤ 1)
    (S : (Fin t → A) → Prop) [DecidablePred S] :
    |𝔼 z : Fin t → A, if S z then (𝔼 i, f (z i)) - (𝔼 a, f a) else 0| ^ 2 ≤
      1 / (t : ℝ)

end Lax253009.TupleAveraging
