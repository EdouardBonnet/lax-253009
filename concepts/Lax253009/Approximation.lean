import Lax253009.Graphs
import Lax434930.PolynomialTime
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Polynomial-time approximation of the clique number
type: definition
---
A polynomial-time $n^{1-\varepsilon}$-approximation of Max-Clique is a
single deterministic polynomial-time algorithm returning an integer $a(G)$
such that
$a(G)\leq\omega(G)\leq n^{1-\varepsilon}a(G)$ on every nonempty
$n$-vertex graph. The algorithm estimates the optimum; it is not required
to return a clique. This is the convention in the introduction of
Håstad's paper.

The input uses the binary graph encoding and the output uses mathlib's
binary encoding of natural numbers. Polynomial time is certified by a
fixed finite stack machine. The exponent $\varepsilon$ is fixed before
choosing the algorithm.
-/

namespace Lax253009.Approximation

open Graphs
open Lax434930.PolynomialTime

def Approximable (ε : ℝ) : Prop :=
  ∃ estimate : Word → ℕ,
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate) ∧
    ∀ (n : ℕ), 0 < n → ∀ G : Graph n,
      estimate G.encode ≤ G.cliqueNumber ∧
      (G.cliqueNumber : ℝ) ≤ Real.rpow (n : ℝ) (1 - ε) * (estimate G.encode : ℝ)

end Lax253009.Approximation
