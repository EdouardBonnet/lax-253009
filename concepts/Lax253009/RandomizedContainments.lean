import Lax434930.NondeterministicPolynomialTime
import Lax666725.OneSidedError
import Lax666725.ZeroError

/-!
---
title: Randomized computations as NP certificates
type: lemma
---
A successful random tape is a polynomial-length NP certificate for an RP
algorithm. A deterministic verifier simulates every coin-selected tape
transition and checks the resulting answer. The simulation includes a
polynomial running-time bound in the registered machine models.

Replacing a zero-error algorithm's failure answer by rejection also gives
an RP algorithm. Consequently both RP and ZPP are contained in the
registered NP class.
-/

namespace Lax253009.RandomizedContainments

axiom RP_subset_NP :
    Lax666725.OneSidedError.RP ⊆ Lax434930.NondeterministicPolynomialTime.NP

axiom ZPP_subset_NP :
    Lax666725.ZeroError.ZPP ⊆ Lax434930.NondeterministicPolynomialTime.NP

end Lax253009.RandomizedContainments
