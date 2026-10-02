import Lax323828.ExponentialBounds

/-!
---
title: Lower concentration of the fibers of a uniform random map
type: theorem
---
For a uniformly random map from an $N$-element set to an $M$-element set,
with $N,M>0$, the probability that some fiber has fewer than $N/(2M)$
elements is at most $M e^{-N/(8M^2)}$.

This is a sufficient version of the concentration estimate in Lemma 4.3.
For $N=2^w$ and $M=2^s$, it tends to zero exponentially in $2^w$ for each
fixed $s$. The paper uses a sharper Chernoff bound; the threshold for $w$
in the soundness theorem can absorb the difference.
-/

namespace Lax323828.RandomFibers

open FiniteProbability

def fiber {ι κ : Type} [Fintype ι] [DecidableEq κ] (f : ι → κ) (z : κ) : Finset ι :=
  Finset.univ.filter fun i ↦ f i = z

axiom small_fiber {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] (hN : 0 < Fintype.card ι) (z : κ) :
  probability (fun f : ι → κ ↦ (fiber f z).card <
      (Fintype.card ι : ℝ) / (2 * Fintype.card κ)) ≤
    Real.exp (-(Fintype.card ι : ℝ) / (8 * (Fintype.card κ : ℝ) ^ 2))

axiom any_small_fiber {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] (hN : 0 < Fintype.card ι) :
  probability (fun f : ι → κ ↦ ∃ z, (fiber f z).card <
      (Fintype.card ι : ℝ) / (2 * Fintype.card κ)) ≤
    (Fintype.card κ : ℝ) *
      Real.exp (-(Fintype.card ι : ℝ) / (8 * (Fintype.card κ : ℝ) ^ 2))

end Lax323828.RandomFibers
