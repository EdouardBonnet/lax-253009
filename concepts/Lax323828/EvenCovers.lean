import Lax323828.BooleanFourier
import Lax323828.HigherMoments

/-!
---
title: Even-cover expansion of a Boolean polynomial moment
type: theorem
---
A family of supports is an even cover if every coordinate occurs an even
number of times. The uniform mean of the product of its Boolean characters
is one for an even cover and zero otherwise. Consequently the $m$th moment
of a Boolean polynomial is the sum of the coefficient products over its
even-cover tuples.

This is the moment identity in the proof of Lemma 4.13, before application
of the hypercontractive inequality. The coefficients may be arbitrary real
numbers; choosing absolute Fourier coefficients gives the nonnegative
weighted sum used in the paper. Every even cover is a double cover of its
union.
-/

namespace Lax323828.EvenCovers

open BooleanFourier HigherMoments
open scoped BigOperators

def EvenCover {ι : Type} [DecidableEq ι] {m : ℕ} (S : Fin m → Finset ι) : Prop :=
  ∀ i, Even (Finset.univ.filter fun j ↦ i ∈ S j).card

instance decidableEvenCover {ι : Type} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (S : Fin m → Finset ι) : Decidable (EvenCover S) :=
  inferInstanceAs (Decidable (∀ i, Even (Finset.univ.filter fun j ↦ i ∈ S j).card))

axiom character_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (S : Fin m → Finset ι) :
  (𝔼 x : Cube ι, ∏ j, character (S j) x) =
    if EvenCover S then 1 else 0

axiom polynomial_moment {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] (S : α → Finset ι) (c : α → ℝ) (m : ℕ) :
  (𝔼 x : Cube ι, (∑ a, c a * character (S a) x) ^ m) =
    ∑ a : Fin m → α, if EvenCover (fun j ↦ S (a j)) then ∏ j, c (a j) else 0

axiom even_implies_double {ι : Type} [DecidableEq ι] {m : ℕ}
    (S : Fin m → Finset ι) (hS : EvenCover S) : DoubleCover S

end Lax323828.EvenCovers
