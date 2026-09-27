import Lax253009.IndependentSetGap
import Lax434930.NondeterministicPolynomialTime
import Lax666725.RandomizedPolynomialTime

/-!
---
title: Randomized promise-gap hardness of Max Independent Set
type: theorem
---
For every integer $q\geq3$, a bounded-error randomized polynomial-time
algorithm distinguishing $\alpha(G)\leq n^{1/q}$ from
$\alpha(G)\geq n^{1-1/q}$ on all sufficiently large $n$-vertex graphs
would imply $\mathrm{NP}\subseteq\mathrm{BPP}$.

This randomized promise-gap form of Håstad's hardness result is assumed
without proof. It is separate from the proved deterministic
clique-approximation statements. NP and BPP are the registered binary-language
classes from lax-434930 and lax-666725.
-/

namespace Lax253009.IndependentSetGapHardness

open Lax434930.NondeterministicPolynomialTime
open Lax666725.RandomizedPolynomialTime

/-- Håstad's randomized promise-gap hardness, assumed without proof. -/
axiom gapSolver_implies_np_subset_bpp (q : ℕ) (hq : 3 ≤ q) :
  IndependentSetGap.Solver q → NP ⊆ BPP

end Lax253009.IndependentSetGapHardness
