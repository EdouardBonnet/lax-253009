import Lax253009.RandomizedApproximation
import Lax434930.NondeterministicPolynomialTime
import Lax666725.RandomizedPolynomialTime

/-!
---
title: Håstad inapproximability for bounded-error randomized algorithms
type: theorem
---
For every fixed $\varepsilon>0$, a polynomial-time randomized
$n^{1-\varepsilon}$ approximation of the clique number, successful with
probability at least $2/3$ on every nonempty graph, implies
$\mathrm{NP}\subseteq\mathrm{BPP}$. Thus $\mathrm{NP}\nsubseteq\mathrm{BPP}$
rules out such randomized algorithms. The estimator may err in either
direction on unsuccessful runs. NP and BPP are the registered Lax classes.
-/

namespace Lax253009.RandomizedCliqueHardness

open RandomizedApproximation Lax434930.NondeterministicPolynomialTime
open Lax666725.RandomizedPolynomialTime

axiom approximation_implies_np_subset_bpp (ε : ℝ) (hε : 0 < ε) :
  Approximable ε → NP ⊆ BPP

axiom not_approximable (ε : ℝ) (hε : 0 < ε) (hnot : ¬ NP ⊆ BPP) :
  ¬ Approximable ε

end Lax253009.RandomizedCliqueHardness
