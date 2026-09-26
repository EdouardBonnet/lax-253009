import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
---
title: Fourier analysis on a finite Boolean cube
type: theorem
---
Write a Boolean value as a sign, with true represented by $-1$ and false
by $1$. For a subset $S$ of a finite coordinate set $I$, the character
$\chi_S(x)$ is the product of the signs of $x_i$ over $i\in S$.
For a real function $F$ on the cube, set
$\widehat F(S)=2^{-|I|}\sum_x F(x)\chi_S(x)$.

The characters are orthonormal for the uniform average. Fourier inversion
recovers $F(x)=\sum_S\widehat F(S)\chi_S(x)$, and Parseval's identity gives
$\sum_S\widehat F(S)^2=\mathbb E_x F(x)^2$. In particular, a sign-valued
function has total squared Fourier mass one. These are the Fourier
identities used at the start of Section 4 of Håstad's paper.
-/

namespace Lax253009.BooleanFourier

abbrev Cube (ι : Type) := ι → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

noncomputable def character {ι : Type} (S : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ S, sign (x i)

noncomputable def average {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ) : ℝ :=
  (∑ x, F x) / (2 : ℝ) ^ Fintype.card ι

noncomputable def coefficient {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ)
    (S : Finset ι) : ℝ :=
  average fun x ↦ F x * character S x

axiom orthogonality {ι : Type} [Fintype ι] [DecidableEq ι] (S T : Finset ι) :
  average (fun x ↦ character S x * character T x) = if S = T then 1 else 0

axiom inversion {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ) (x : Cube ι) :
  F x = ∑ S, coefficient F S * character S x

axiom parseval {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ) :
  ∑ S, coefficient F S ^ 2 = average (fun x ↦ F x ^ 2)

axiom boolean_energy {ι : Type} [Fintype ι] [DecidableEq ι] (A : Cube ι → Bool) :
  ∑ S, coefficient (fun x ↦ sign (A x)) S ^ 2 = 1

axiom bounded_energy {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (hF : ∀ x, |F x| ≤ 1) :
  ∑ S, coefficient F S ^ 2 ≤ 1

end Lax253009.BooleanFourier
