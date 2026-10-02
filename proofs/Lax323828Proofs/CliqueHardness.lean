import Lax323828.CliqueHardness
import Lax323828.RandomizedContainments
import Lax323828Proofs.RegisteredBridge.FairTestCompiler

set_option backward.isDefEq.respectTransparency false

namespace Lax323828Proofs

open Lax323828.Approximation
open Lax434930.NondeterministicPolynomialTime Lax666725.ZeroError
open PCPFoundation.Complexity (algBase one_lt_algBase_deg)
open RegisteredBridge

/--
---
conclusion: Lax323828.CliqueHardness.approximation_implies_np_eq_zpp
---
The uniform PCP and clique reduction give a polynomial-time fair-tape test
for every registered NP language. Rejection tapes certify its complement,
so complementary tests combine into a zero-error finite-tape algorithm.
The probability-preserving compiler implements it in the registered
probabilistic machine model with a worst-case polynomial clock. The reverse
inclusion is the proved registered containment ZPP ⊆ NP.
-/
theorem clique_approximation_implies_np_eq_zpp (ε : ℝ) (hε : 0 < ε)
    (happrox : Approximable ε) : NP = ZPP := by
  apply Set.Subset.antisymm
  · intro L hL
    obtain ⟨A⟩ := approximation_zero_test algBase one_lt_algBase_deg ε hε happrox L hL
    exact FairTestCompiler.zeroTest_in_ZPP A
  · exact Lax323828.RandomizedContainments.ZPP_subset_NP

end Lax323828Proofs
