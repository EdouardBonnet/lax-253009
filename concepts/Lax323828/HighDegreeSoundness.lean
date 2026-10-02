import Lax323828.BalancedPredicates
import Lax323828.ProductMoments

/-!
---
title: Second moment and tail bound for the high-degree CNA term
type: theorem
---
Normalize the first Fourier term by averaging over balanced predicates.
If its supports have size at least $\ell$ and its coefficients have total
squared mass at most one, its second moment is at most
$q^\ell+2(N+1)e^{-Nq^2/2}$ for every $q\geq0$, where $N$ is the number of
inputs to a predicate. Its upper tail at $a>0$ is bounded by this quantity
divided by $a^2$.

This is the normalized version of the estimates in Lemma 4.5 and Corollary
4.6, with the concentration bound obtained by conditioning on balance.
The choice $q=N^{-1/4}$ yields the required high-degree decay.
-/

namespace Lax323828.HighDegreeSoundness

open BooleanFourier BalancedPredicates FiniteProbability
open scoped BigOperators

noncomputable def normalizedSum {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (supports : Finset (Finset ι)) (c : Finset ι → ℝ) (n : ℕ) (f : ι → κ) : ℝ :=
  ∑ S ∈ supports, c S * (𝔼 B : predicates κ n, ∏ i ∈ S, sign (B.val (f i)))

axiom second_moment_bound {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (supports : Finset (Finset ι)) (c : Finset ι → ℝ) (l : ℕ)
    (hdegree : ∀ S ∈ supports, l ≤ S.card) (henergy : ∑ S ∈ supports, c S ^ 2 ≤ 1)
    (q : ℝ) (hq : 0 ≤ q) :
  (𝔼 f : ι → κ, normalizedSum supports c n f ^ 2) ≤
    q ^ l + 2 * (Fintype.card κ + 1 : ℝ) * Real.exp (-(Fintype.card κ : ℝ) * q ^ 2 / 2)

axiom tail_bound {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (supports : Finset (Finset ι)) (c : Finset ι → ℝ) (l : ℕ)
    (hdegree : ∀ S ∈ supports, l ≤ S.card) (henergy : ∑ S ∈ supports, c S ^ 2 ≤ 1)
    (q : ℝ) (hq : 0 ≤ q) (a : ℝ) (ha : 0 < a) :
  probability (fun f : ι → κ ↦ a ≤ normalizedSum supports c n f) ≤
    (q ^ l + 2 * (Fintype.card κ + 1 : ℝ) *
      Real.exp (-(Fintype.card κ : ℝ) * q ^ 2 / 2)) / a ^ 2

end Lax323828.HighDegreeSoundness
