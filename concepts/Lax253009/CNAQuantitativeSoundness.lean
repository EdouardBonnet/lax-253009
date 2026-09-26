import Lax253009.CNAPointSoundness
import Lax253009.CNASoundness
import Lax253009.RandomFibers

/-!
---
title: Finite quantitative soundness of the CNA test with side conditions
type: theorem
---
Combine soundness at each evaluation point with concentration of random
label fibers. Every accepted run agrees with an entire fiber. Unless a
fiber is unusually small, averaging over the possible evaluation points
costs only a factor twice the number of labels, independently of the
number of words. Projection makes the decoding set independent of the
side condition.
-/

namespace Lax253009.CNAQuantitativeSoundness

open LongCode BooleanFourier CNAPointSoundness CNASoundness FiniteProbability

noncomputable def totalBound (l m r s w : ℕ) (τ q : ℝ) : ℝ :=
  (2 : ℝ) ^ s * Real.exp (-((2 : ℝ) ^ w) / (8 * ((2 : ℝ) ^ s) ^ 2)) +
    2 * (2 : ℝ) ^ s * pointBound l m r (2 ^ s) τ q

axiom quantitative_soundness (w s l m r : ℕ) (hs : 0 < s)
    (hl : 0 < l) (hlN : l < 2 ^ s)
    (τ q : ℝ) (hτ : 0 < τ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hr : 2 * r ≤ m) (hm : Even m)
    (hlarge : (l : ℝ) / ((2 : ℝ) ^ s - l) / τ ≤ 1 / 3)
    (A : Table w) (h : Coordinate w) :
  probability (BadWithCondition (s := s) A (decoding (fun g ↦ sign (A g)) l τ) h) ≤
    totalBound l m r s w τ q

end Lax253009.CNAQuantitativeSoundness
