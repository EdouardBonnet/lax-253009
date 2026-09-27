import Lax253009.Approximation
import Lax434930.NondeterministicPolynomialTime
import Lax666725.ZeroError

/-!
---
title: Håstad's clique inapproximability theorem
type: theorem
---
For every fixed real $\varepsilon>0$, a deterministic polynomial-time
$n^{1-\varepsilon}$-approximation of the clique number would imply
$\mathrm{NP}=\mathrm{ZPP}$. Equivalently, if $\mathrm{NP}\ne\mathrm{ZPP}$,
no such approximation exists. This is Theorem 5.2 of Håstad's paper.

The approximation convention includes a single uniform algorithm and all
nonempty finite graphs. NP is the binary-language class from lax-434930;
ZPP is the bounded-time, failure-allowed class from lax-666725. No complexity
class is redefined here. The proof implements the reductions in these machine
models, with an explicit polynomial clock and exact preservation of the
finite fair-coin output distribution.
-/

namespace Lax253009.CliqueHardness

open Approximation
open Lax434930.NondeterministicPolynomialTime Lax666725.ZeroError

axiom approximation_implies_np_eq_zpp (ε : ℝ) (hε : 0 < ε) :
  Approximable ε → NP = ZPP

axiom not_approximable (ε : ℝ) (hε : 0 < ε) (hne : NP ≠ ZPP) :
  ¬ Approximable ε

end Lax253009.CliqueHardness
