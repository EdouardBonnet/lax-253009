import Lax253009.HighDegreeSoundness
import Lax253009.BalancedCancellation

/-!
---
title: Deterministic bound for the large-coefficient CNA term
type: theorem
---
Suppose every retained support contains a distinguished point $y$, has
size at most $\ell<N$, and contains no other point with the same label
as $y$. For coefficients of magnitude at least $\delta>0$ and total
squared mass at most one, the absolute normalized Fourier sum is at most
$\ell/((N-\ell)\delta)$. This supplies the deterministic cancellation
estimate for the second CNA term in Lemma 4.8.
-/

namespace Lax253009.LargeCoefficientSoundness

open HighDegreeSoundness
open scoped BigOperators

axiom bound {ι κ : Type} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hN : Fintype.card κ = 2 * n)
    (supports : Finset (Finset ι)) (c : Finset ι → ℝ) (l : ℕ)
    (f : ι → κ) (y : ι) (δ : ℝ) (hδ : 0 < δ) (hl : l < Fintype.card κ)
    (hsupport : ∀ S ∈ supports, y ∈ S ∧ S.card ≤ l ∧ ∀ i ∈ S, i ≠ y → f i ≠ f y)
    (hlarge : ∀ S ∈ supports, δ ≤ |c S|) (henergy : ∑ S ∈ supports, c S ^ 2 ≤ 1) :
  |normalizedSum supports c n f| ≤ (l : ℝ) / ((Fintype.card κ : ℝ) - l) / δ

end Lax253009.LargeCoefficientSoundness
