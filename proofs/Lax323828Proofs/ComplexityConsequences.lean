import Lax323828.BPPConsequence

namespace Lax323828Proofs

open Lax323828.Approximation
open Lax434930.NondeterministicPolynomialTime
open Lax666725.ZeroError Lax666725.RandomizedPolynomialTime

/--
---
conclusion: Lax323828.CliqueHardness.not_approximable
---
Contraposition of the main clique-hardness implication. This proof retains
that implication as an explicit archive assumption.
-/
theorem clique_not_approximable_of_np_ne_zpp
    (ε : ℝ) (hε : 0 < ε) (hne : NP ≠ ZPP) : ¬ Approximable ε := by
  intro h
  exact hne (Lax323828.CliqueHardness.approximation_implies_np_eq_zpp ε hε h)

/--
---
conclusion: Lax323828.BPPConsequence.approximation_implies_np_subset_bpp
---
Combine the main clique-hardness implication with the imported inclusion
ZPP ⊆ BPP. Both statement dependencies are recorded by the archive.
-/
theorem clique_approximation_implies_np_subset_bpp
    (ε : ℝ) (hε : 0 < ε) (h : Approximable ε) : NP ⊆ BPP := by
  rw [Lax323828.CliqueHardness.approximation_implies_np_eq_zpp ε hε h]
  exact Lax666725.ZPPSubsetBPP.ZPP_subset_BPP

/--
---
conclusion: Lax323828.BPPConsequence.not_approximable
---
Contrapose the BPP consequence; the imported classes have the same binary
language type, so no change of input encoding is involved.
-/
theorem clique_not_approximable_of_np_not_subset_bpp
    (ε : ℝ) (hε : 0 < ε) (hnot : ¬ NP ⊆ BPP) : ¬ Approximable ε := by
  intro h
  exact hnot (Lax323828.BPPConsequence.approximation_implies_np_subset_bpp ε hε h)

end Lax323828Proofs
