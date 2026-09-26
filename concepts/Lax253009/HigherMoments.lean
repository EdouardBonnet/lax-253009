import Lax253009.ProductMoments
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
---
title: Cancellation outside double covers in higher moments
type: theorem
---
For a family of supports $S_j$ and independently sampled labels $f(i)$,
the expectation of $\prod_j\prod_{i\in S_j}B_j(f(i))$ factors over
coordinates $i$. If the predicates are balanced and a coordinate occurs
in exactly one support, the expectation vanishes. Thus only double covers
contribute to the higher-moment expansion in equation (12).

A double cover uses every point of its union at least twice, so
$2|\bigcup_jS_j|\leq\sum_j|S_j|$. This is the union-size bound used in
the reduction from double covers to even covers in Lemma 4.15.
-/

namespace Lax253009.HigherMoments

open scoped BigOperators

def DoubleCover {ι : Type} [DecidableEq ι] {m : ℕ} (S : Fin m → Finset ι) : Prop :=
  ∀ i ∈ Finset.univ.biUnion S, 2 ≤ (Finset.univ.filter fun j ↦ i ∈ S j).card

axiom factorization {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] {m : ℕ} (S : Fin m → Finset ι) (B : Fin m → κ → ℝ) :
  (𝔼 f : ι → κ, ∏ j, ∏ i ∈ S j, B j (f i)) =
    ∏ i, (𝔼 z, ∏ j with i ∈ S j, B j z)

axiom singleton_cancellation {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] {m : ℕ} (S : Fin m → Finset ι) (B : Fin m → κ → ℝ)
    (hbalanced : ∀ j, (𝔼 z, B j z) = 0) (i : ι) (j : Fin m)
    (hij : i ∈ S j) (hunique : ∀ j', i ∈ S j' → j' = j) :
  (𝔼 f : ι → κ, ∏ j, ∏ i ∈ S j, B j (f i)) = 0

axiom double_cover_union_bound {ι : Type} [DecidableEq ι] {m : ℕ}
    (S : Fin m → Finset ι) (hS : DoubleCover S) :
  2 * (Finset.univ.biUnion S).card ≤ ∑ j, (S j).card

end Lax253009.HigherMoments
