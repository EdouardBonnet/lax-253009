import Lax253009.SmallSupport
import Lax253009.FourierProjection
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: A small Fourier decoding set independent of side conditions
type: theorem
---
For a sign-valued table $F$, take the union of supports $S$ with
$|S|\leq\ell$ and $\widehat F(S)^2\geq\ell2^{-t}$. This decoding set
has size at most $2^t$ by Parseval and the counting bound.
Taking $t=\varepsilon s$ gives the set in equation (2).

After averaging outside any set $U$, the decoding set can only shrink,
and every surviving point lies in $U$. Consequently the decoding set for
the original table serves every side condition; it need not be chosen
anew after the condition is known. This is the inclusion used immediately
after equation (18) in the proof of Theorem 4.17.
-/

namespace Lax253009.FourierDecoding

open BooleanFourier FourierProjection SmallSupport

axiom boolean_decoding_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Cube ι → Bool) (l : ℕ) (t : ℝ) :
  ((decodingSet (coefficient (fun x ↦ sign (A x))) l (Real.rpow 2 (-t))).card : ℝ) ≤
    Real.rpow 2 t

axiom projected_decoding_subset {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (U : Finset ι) (l : ℕ) (δ : ℝ) (hδ : 0 < δ) :
  decodingSet (coefficient (project F U)) l δ ⊆ decodingSet (coefficient F) l δ ∩ U

end Lax253009.FourierDecoding
