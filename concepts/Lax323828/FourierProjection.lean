import Lax323828.BooleanFourier

/-!
---
title: Averaging outside a set of coordinates
type: theorem
---
For $U\subseteq I$, average a function $F$ over the coordinates outside
$U$, retaining the input on $U$. The resulting function has Fourier
coefficient $\widehat F(S)$ when $S\subseteq U$, and zero otherwise.
This is Lemma 4.18 of Håstad's paper: take $I$ to be the set of possible
encoded words, and $U$ to be the words satisfying the side condition.

The definition averages over a full independent cube; the unused coordinates
give equal multiplicities, hence the same uniform average as over just the
coordinates outside $U$. Averaging preserves the bound $|F|\leq1$. At an
input whose entire averaging fiber has one value, that value is preserved.
-/

namespace Lax323828.FourierProjection

open BooleanFourier

def splice {ι : Type} [DecidableEq ι] (U : Finset ι) (x y : Cube ι) : Cube ι :=
  fun i ↦ if i ∈ U then x i else y i

noncomputable def project {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (U : Finset ι) (x : Cube ι) : ℝ :=
  average fun y ↦ F (splice U x y)

axiom coefficient_project {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (U S : Finset ι) :
  coefficient (project F U) S = if S ⊆ U then coefficient F S else 0

axiom bounded_project {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (hF : ∀ x, |F x| ≤ 1) (U : Finset ι) (x : Cube ι) :
  |project F U x| ≤ 1

axiom constant_fiber {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (U : Finset ι) (x : Cube ι)
    (hF : ∀ y, (∀ i ∈ U, y i = x i) → F y = F x) :
  project F U x = F x

end Lax323828.FourierProjection
