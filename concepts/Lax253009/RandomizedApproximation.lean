import Lax253009.Approximation
import Lax253009.FiniteProbability
import Lax434930.Certificates

/-!
---
title: Bounded-error randomized approximation of the clique number
type: definition
---
A randomized polynomial-time approximation has a polynomial-length tape of
independent fair bits and a deterministic polynomial-time evaluator in the
registered stack-machine model. On every nonempty graph it returns an
integer satisfying both approximation inequalities with probability at least
$2/3$. Its answer on the remaining tapes is unrestricted.

The input to the evaluator is the registered pairing of the graph encoding
and the random tape. Both the machine and the polynomial are uniform and
chosen before the input graph. The tape has polynomial length in the graph
encoding, so the total runtime is polynomial in that encoding. Integer
outputs are binary words on the output stack and need not have bounded size.
-/

namespace Lax253009.RandomizedApproximation

open Graphs FiniteProbability Lax434930.PolynomialTime

def Good {n : ℕ} (ε : ℝ) (G : Graph n) (a : ℕ) : Prop :=
  a ≤ G.cliqueNumber ∧
    (G.cliqueNumber : ℝ) ≤ Real.rpow (n : ℝ) (1 - ε) * (a : ℝ)

def Approximable (ε : ℝ) : Prop :=
  ∃ (coins : Polynomial ℕ) (estimate : Word → ℕ),
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate) ∧
    ∀ (n : ℕ), 0 < n → ∀ G : Graph n,
      (2 / 3 : ℝ) ≤ probability (fun r : Fin (coins.eval G.encode.length) → Bool ↦
        Good ε G (estimate (Lax434930.Certificates.pair G.encode (List.ofFn r))))

end Lax253009.RandomizedApproximation
