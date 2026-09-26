import Lax253009.TupleAveraging

/-!
---
title: A tuple sampler with alphabet-independent mixing
type: theorem
---
For an event S on t-tuples, plant a specified letter in a uniformly chosen
coordinate and sample the remaining coordinates independently. Let p_S(a)
be the probability of S under this experiment. Its mean is Pr[S], and
the square of its mean absolute deviation from Pr[S] is at most 1/t.

The alphabet size does not enter the bound. Using all tuples as questions
therefore gives a polynomial-size sampler for each fixed accuracy.
-/

namespace Lax253009.TupleSampler

open FiniteProbability
open scoped BigOperators

noncomputable def indicator {A : Type} (S : A → Prop) (a : A) : ℝ := by
  classical
  exact if S a then 1 else 0

noncomputable def mass {A : Type} [Fintype A] (t : ℕ)
    (S : (Fin t → A) → Prop) (a : A) : ℝ := by
  classical
  exact 𝔼 i : Fin t, 𝔼 z : Fin t → A, indicator S (Function.update z i a)

axiom bounds {A : Type} [Fintype A] [Nonempty A] (t : ℕ) (ht : 0 < t)
    (S : (Fin t → A) → Prop) (a : A) : 0 ≤ mass t S a ∧ mass t S a ≤ 1

axiom mean {A : Type} [Fintype A] [Nonempty A] (t : ℕ) (ht : 0 < t)
    (S : (Fin t → A) → Prop) : (𝔼 a, mass t S a) = probability S

axiom mixing {A : Type} [Fintype A] [Nonempty A] (t : ℕ) (ht : 0 < t)
    (S : (Fin t → A) → Prop) :
    (𝔼 a, |mass t S a - probability S|) ^ 2 ≤ 1 / (t : ℝ)

end Lax253009.TupleSampler
