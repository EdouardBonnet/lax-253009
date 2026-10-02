import Lax323828.BalancedPredicates

/-!
---
title: Cancellation on a small set of distinct balanced-predicate inputs
type: theorem
---
Let $B$ be uniform among predicates with exactly half of their $N$ inputs
true. For $y\notin S$, the absolute mean of
$B(y)\prod_{z\in S} B(z)$, using sign values, is at most
$|S|/(N-|S|)$. This follows by multiplying the zero sum of all signs by
the character on $S$, then using permutation symmetry outside $S$.
The same bound holds with the character replaced by any function of
absolute value at most one that depends only on the coordinates in $S$.
This more general form also handles repeated predicate inputs.

For a fixed upper bound on $|S|$, this gives the $O(1/N)$ cancellation
needed for the large-coefficient term in Lemma 4.8. It replaces the exact
product formula of Lemma 4.9 with a sufficient bound.
-/

namespace Lax323828.BalancedCancellation

open BooleanFourier BalancedPredicates
open scoped BigOperators

axiom bounded_support_correlation {κ : Type} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hN : Fintype.card κ = 2 * n) (S : Finset κ)
    (F : Cube κ → ℝ) (hF : ∀ B, |F B| ≤ 1)
    (hdepends : ∀ B C, (∀ z ∈ S, B z = C z) → F B = F C)
    (y : κ) (hy : y ∉ S) :
  |𝔼 B : predicates κ n, sign (B.val y) * F B.val| ≤
    (S.card : ℝ) / ((Fintype.card κ : ℝ) - S.card)

axiom small_support_correlation {κ : Type} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hN : Fintype.card κ = 2 * n) (S : Finset κ) (y : κ) (hy : y ∉ S) :
  |𝔼 B : predicates κ n, character (insert y S) B.val| ≤
    (S.card : ℝ) / ((Fintype.card κ : ℝ) - S.card)

end Lax323828.BalancedCancellation
