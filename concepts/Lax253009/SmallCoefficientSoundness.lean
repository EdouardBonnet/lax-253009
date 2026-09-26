import Lax253009.HighDegreeSoundness
import Lax253009.SmallUnionDoubleCovers
import Lax253009.MixedPredicateMoments

/-!
---
title: Higher-moment bound for the small-coefficient CNA term
type: theorem
---
For coefficients of degree at most $\ell$, squared mass at most one,
and absolute value at most $\delta$, split the mixed-moment expansion
according to the union size of its double covers. Small unions contribute
the bounds from Lemma 4.16; unions of size at least $r$ contribute at
most the total double-cover weight times the mixed-correlation bound.
This gives the normalized higher-moment estimate underlying Lemma 4.10
and, for even moments, its probability bound.
-/

namespace Lax253009.SmallCoefficientSoundness

open HighDegreeSoundness FiniteProbability
open scoped BigOperators

noncomputable def boundValue (l m r N : ℕ) (δ q : ℝ) : ℝ :=
  (∑ t ∈ Finset.range r, (2 : ℝ) ^ m * ((2 : ℝ) ^ t * δ) ^ (m - 2 * t) *
    (1 + (3 : ℝ) ^ (l * (4 * t + 1) * 2 ^ (2 * t)))) +
  (1 + (3 : ℝ) ^ (l * (2 * m + 1) * 2 ^ m)) *
    (q ^ r + (2 : ℝ) ^ m * (2 * (N + 1 : ℝ) * Real.exp (-(N : ℝ) * q ^ 2 / 2)))

axiom moment_bound {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (c : Finset ι → ℝ) (l m r : ℕ) (δ q : ℝ)
    (hsmall : ∀ S, |c S| ≤ δ) (hδ : 0 ≤ δ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hdegree : ∀ S, l < S.card → c S = 0) (henergy : ∑ S, c S ^ 2 ≤ 1)
    (hr : 2 * r ≤ m) :
  (𝔼 f : ι → κ, normalizedSum Finset.univ c n f ^ m) ≤
    boundValue l m r (Fintype.card κ) δ q

axiom tail_bound {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (c : Finset ι → ℝ) (l m r : ℕ) (δ q : ℝ)
    (hsmall : ∀ S, |c S| ≤ δ) (hδ : 0 ≤ δ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hdegree : ∀ S, l < S.card → c S = 0) (henergy : ∑ S, c S ^ 2 ≤ 1)
    (hr : 2 * r ≤ m) (hm : Even m) (a : ℝ) (ha : 0 < a) :
  probability (fun f : ι → κ ↦ a ≤ normalizedSum Finset.univ c n f) ≤
    boundValue l m r (Fintype.card κ) δ q / a ^ m

end Lax253009.SmallCoefficientSoundness
