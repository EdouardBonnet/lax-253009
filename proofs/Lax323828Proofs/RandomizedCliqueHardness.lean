import Lax323828.RandomizedCliqueHardness
import Lax323828Proofs.RegisteredBridge.RandomizedApproximationTest

namespace Lax323828Proofs

open Lax323828.RandomizedApproximation
open Lax434930.NondeterministicPolynomialTime
open Lax666725.RandomizedPolynomialTime
open PCPFoundation.Complexity (algBase one_lt_algBase_deg)
open RegisteredBridge

/--
---
conclusion: Lax323828.RandomizedCliqueHardness.approximation_implies_np_subset_bpp
---
Reuse the uniform PCP-to-clique gap reduction. Amplify the randomized
estimator's comparison, combine independent reduction and estimator tapes,
and accept only if two independent combined trials accept. The finite-tape
compiler realizes the resulting bounded-error test in the registered BPP model.
-/
theorem randomized_clique_approximation_implies_np_subset_bpp
    (ε : ℝ) (hε : 0 < ε) (h : Approximable ε) : NP ⊆ BPP := by
  let θ := min ε 1
  have hθ : 0 < θ := lt_min hε zero_lt_one
  have hθ1 : θ ≤ 1 := min_le_right _ _
  have ha := RandomizedApproximationTest.weaken (min_le_left ε 1) h
  intro L hL
  obtain ⟨R⟩ := clique_gap_reduction algBase one_lt_algBase_deg θ hθ hθ1 L hL
  exact RandomizedApproximationTest.randomized_approximation_in_BPP ha L R

/--
---
conclusion: Lax323828.RandomizedCliqueHardness.not_approximable
---
Contrapose the randomized implication through its concept statement so the
archive records the dependency in the proof network.
-/
theorem randomized_clique_not_approximable_of_np_not_subset_bpp
    (ε : ℝ) (hε : 0 < ε) (hnot : ¬ NP ⊆ BPP) : ¬ Approximable ε := by
  intro h
  exact hnot (Lax323828.RandomizedCliqueHardness.approximation_implies_np_subset_bpp ε hε h)

end Lax323828Proofs
