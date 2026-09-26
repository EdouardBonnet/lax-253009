import Lax253009.BalancedPredicates
import Lax253009.HigherMoments

/-!
---
title: Mixed moments of independently sampled balanced predicates
type: theorem
---
For a fixed tuple of supports with union of size $t$, the absolute mixed
moment is at most $q^t+2^m 2(N+1)e^{-Nq^2/2}$. Here $m$ is the number
of supports and $N$ is the size of the predicate domain. This is a
normalized version of Lemma 4.12, with a nonoptimal concentration factor.
Condition on all but one predicate in each nonempty subcollection; a
union bound controls their correlations simultaneously. Independence of
the coordinate labels then gives one factor $q$ per point of the union.
-/

namespace Lax253009.MixedPredicateMoments

open BooleanFourier BalancedPredicates
open scoped BigOperators

axiom bound {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (m : ℕ) (S : Fin m → Finset ι) (q : ℝ) (hq : 0 ≤ q) :
  |𝔼 B : Fin m → predicates κ n, 𝔼 f : ι → κ,
      ∏ j, ∏ i ∈ S j, sign ((B j).val (f i))| ≤
    q ^ (Finset.univ.biUnion S).card + (2 : ℝ) ^ m *
      (2 * (Fintype.card κ + 1 : ℝ) * Real.exp (-(Fintype.card κ : ℝ) * q ^ 2 / 2))

end Lax253009.MixedPredicateMoments
