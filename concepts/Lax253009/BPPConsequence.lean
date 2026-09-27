import Lax253009.CliqueHardness
import Lax666725.RandomizedPolynomialTime
import Lax666725.ZPPSubsetBPP

/-!
---
title: Clique inapproximability under NP not contained in BPP
type: theorem
---
For every fixed $\varepsilon>0$, a polynomial-time
$n^{1-\varepsilon}$-approximation of the clique number would imply
$\mathrm{NP}\subseteq\mathrm{BPP}$. Consequently, the assumption
$\mathrm{NP}\nsubseteq\mathrm{BPP}$ rules out such an approximation.

The proof uses Håstad's NP = ZPP implication and the ZPP ⊆ BPP inclusion
from lax-666725. Both dependencies have proofs, so the archive dependency
closure also proves this consequence.
-/

namespace Lax253009.BPPConsequence

open Approximation
open Lax434930.NondeterministicPolynomialTime
open Lax666725.RandomizedPolynomialTime

axiom approximation_implies_np_subset_bpp (ε : ℝ) (hε : 0 < ε) :
  Approximable ε → NP ⊆ BPP

axiom not_approximable (ε : ℝ) (hε : 0 < ε) (hnot : ¬ NP ⊆ BPP) :
  ¬ Approximable ε

end Lax253009.BPPConsequence
