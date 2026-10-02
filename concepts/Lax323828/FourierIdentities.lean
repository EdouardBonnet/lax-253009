import Lax323828.BooleanFourier
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Algebra.Ring.Parity

/-!
---
title: Fourier shifts, odd tables and disagreement indicators
type: theorem
---
Multiplication by the character of $T$ shifts Fourier indices by symmetric
difference with $T$. If $F(-x)=-F(x)$, all coefficients on even supports
vanish, as observed after equation (1) of Håstad's paper.

For a Boolean table $A$ and a coordinate $y$, the indicator that $A(x)$
disagrees with the point evaluation $x_y$ is
$I_y(x)=(1-\operatorname{sign}(A(x))\operatorname{sign}(x_y))/2$.
Its coefficient on $S$ is
$\tfrac12\mathbf1_{S=\varnothing}-\tfrac12\widehat A(S\mathbin\triangle\{y\})$.
This combines equations (4) and (5) in Section 4.1.
-/

namespace Lax323828.FourierIdentities

open BooleanFourier
open scoped symmDiff

def bitFlip {ι : Type} (x : Cube ι) : Cube ι := fun i ↦ !(x i)

noncomputable def disagreement {ι : Type} (A : Cube ι → Bool) (y : ι)
    (x : Cube ι) : ℝ :=
  (1 - sign (A x) * sign (x y)) / 2

axiom character_shift {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (S T : Finset ι) :
  coefficient (fun x ↦ F x * character T x) S = coefficient F (S ∆ T)

axiom odd_even_vanish {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (hF : ∀ x, F (bitFlip x) = -F x)
    (S : Finset ι) (hS : Even S.card) : coefficient F S = 0

axiom disagreement_indicator {ι : Type} (A : Cube ι → Bool) (y : ι) (x : Cube ι) :
  disagreement A y x = if A x = x y then 0 else 1

axiom disagreement_coefficient {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Cube ι → Bool) (y : ι) (S : Finset ι) :
  coefficient (disagreement A y) S =
    ((if S = ∅ then 1 else 0) - coefficient (fun x ↦ sign (A x)) (S ∆ {y})) / 2

end Lax323828.FourierIdentities
