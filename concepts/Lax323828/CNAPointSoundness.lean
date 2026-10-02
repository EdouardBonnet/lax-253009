import Lax323828.FourierDecoding
import Lax323828.HighDegreeSoundness
import Lax323828.SmallCoefficientSoundness
import Lax323828.LargeCoefficientSoundness

/-!
---
title: Quantitative soundness at a fixed evaluation point
type: theorem
---
The three Fourier estimates apply to the actual event that every balanced
query agrees with evaluation at a fixed point while its label is absent
from the small decoding set. This is the fixed-point step in Section 4.1.
The table may be real valued and bounded by one, so the same statement
applies after averaging over a side condition.
-/

namespace Lax323828.CNAPointSoundness

open BooleanFourier BalancedPredicates FiniteProbability

noncomputable def decoding {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (l : ℕ) (τ : ℝ) : Finset ι :=
  SmallSupport.decodingSet (coefficient F) l (τ ^ 2 / l)

def Matches {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (F : Cube ι → ℝ) (n : ℕ) (f : ι → κ) (y : ι) : Prop :=
  ∀ B : predicates κ n, F (fun i ↦ B.val (f i)) = sign (B.val (f y))

def Avoids {ι κ : Type} (D : Finset ι) (f : ι → κ) (y : ι) : Prop :=
  ∀ x ∈ D, f x ≠ f y

noncomputable def pointBound (l m r N : ℕ) (τ q : ℝ) : ℝ :=
  9 * (q ^ l + 2 * (N + 1 : ℝ) * Real.exp (-(N : ℝ) * q ^ 2 / 2)) +
    (3 : ℝ) ^ m * SmallCoefficientSoundness.boundValue l m r N τ q

axiom decoding_card {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (hF : ∀ x, |F x| ≤ 1)
    (l : ℕ) (hl : 0 < l) (τ : ℝ) (hτ : 0 < τ) :
  ((decoding F l τ).card : ℝ) ≤ (l : ℝ) / τ ^ 2

axiom point_soundness {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (F : Cube ι → ℝ) (hF : ∀ x, |F x| ≤ 1)
    (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (l m r : ℕ) (hl : 0 < l) (hlN : l < Fintype.card κ)
    (τ q : ℝ) (hτ : 0 < τ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hr : 2 * r ≤ m) (hm : Even m)
    (hlarge : (l : ℝ) / ((Fintype.card κ : ℝ) - l) / τ ≤ 1 / 3)
    (y : ι) :
  probability (fun f : ι → κ ↦ Matches F n f y ∧ Avoids (decoding F l τ) f y) ≤
    pointBound l m r (Fintype.card κ) τ q

end Lax323828.CNAPointSoundness
