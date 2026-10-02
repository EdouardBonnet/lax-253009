import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
---
title: Mixed moments of balanced predicates on independent coordinates
type: theorem
---
Choose independently and uniformly a label $f(i)$ from a nonempty finite
set for every coordinate $i$. If two real predicates $B,C$ have mean zero,
then
$\mathbb E_f\bigl[\prod_{i\in S}B(f(i))\prod_{i\in T}C(f(i))\bigr]$
is zero for $S\ne T$, and is
$(\mathbb E_z B(z)C(z))^{|S|}$ for $S=T$.

This is the independence and cancellation argument from equation (6) to
equation (7) in the proof of Lemma 4.5. For the application, labels are
$s$-bit words and the predicates are balanced sign-valued functions.

For a finite family of balanced predicates, the second moment of a weighted
sum over supports therefore contains only equal-support terms, weighted
by the squares of their coefficients. This yields the exact expression
in equation (7) before the correlation estimates are applied.
For supports of size at least $\ell$ and coefficients of total squared mass
at most one, this second moment is bounded by the sum of the absolute
correlations to the power $\ell$.
-/

namespace Lax323828.ProductMoments

open scoped BigOperators

noncomputable def weightedSum {ι κ : Type} (supports : Finset (Finset ι))
    (c : Finset ι → ℝ) (predicates : Finset (κ → ℝ)) (f : ι → κ) : ℝ :=
  ∑ S ∈ supports, c S * ∑ B ∈ predicates, ∏ i ∈ S, B (f i)

axiom mixed_moment {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (B C : κ → ℝ)
    (hB : (𝔼 z, B z) = 0) (hC : (𝔼 z, C z) = 0) (S T : Finset ι) :
  (𝔼 f : ι → κ, (∏ i ∈ S, B (f i)) * (∏ i ∈ T, C (f i))) =
    if S = T then (𝔼 z, B z * C z) ^ S.card else 0

axiom second_moment {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (supports : Finset (Finset ι))
    (c : Finset ι → ℝ) (predicates : Finset (κ → ℝ))
    (hbalanced : ∀ B ∈ predicates, (𝔼 z, B z) = 0) :
  (𝔼 f : ι → κ, weightedSum supports c predicates f ^ 2) =
    ∑ S ∈ supports, c S ^ 2 *
      ∑ B ∈ predicates, ∑ C ∈ predicates, (𝔼 z, B z * C z) ^ S.card

axiom high_degree_bound {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (supports : Finset (Finset ι))
    (c : Finset ι → ℝ) (predicates : Finset (κ → ℝ)) (l : ℕ)
    (hbalanced : ∀ B ∈ predicates, (𝔼 z, B z) = 0)
    (hbounded : ∀ B ∈ predicates, ∀ z, |B z| ≤ 1)
    (hdegree : ∀ S ∈ supports, l ≤ S.card)
    (henergy : ∑ S ∈ supports, c S ^ 2 ≤ 1) :
  (𝔼 f : ι → κ, weightedSum supports c predicates f ^ 2) ≤
    ∑ B ∈ predicates, ∑ C ∈ predicates, |𝔼 z, B z * C z| ^ l

end Lax323828.ProductMoments
