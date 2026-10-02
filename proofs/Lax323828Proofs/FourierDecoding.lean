import Lax323828.FourierDecoding
import Lax323828Proofs.SmallSupport
import Lax323828Proofs.FourierProjection

namespace Lax323828Proofs

open Lax323828.BooleanFourier Lax323828.FourierProjection Lax323828.SmallSupport

/--
---
conclusion: Lax323828.FourierDecoding.boolean_decoding_bound
---
The counting bound applies because Parseval gives total squared mass one.
-/
theorem fourier_decoding_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Cube ι → Bool) (l : ℕ) (t : ℝ) :
    ((decodingSet (coefficient (fun x ↦ sign (A x))) l (Real.rpow 2 (-t))).card : ℝ) ≤
      Real.rpow 2 t := by
  have h := Lax323828.SmallSupport.decodingSet_bound (coefficient (fun x ↦ sign (A x))) l (Real.rpow 2 (-t))
    (Real.rpow_pos_of_pos (by norm_num) _) (Lax323828.BooleanFourier.boolean_energy A).le
  simpa [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), one_div] using h

/--
---
conclusion: Lax323828.FourierDecoding.projected_decoding_subset
---
A support meeting the positive threshold and containing a point is nonempty,
so its projected coefficient cannot vanish. The projection formula forces
the support to lie in U and identifies its coefficient with the original one.
-/
theorem fourier_decoding_projection {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (U : Finset ι) (l : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    decodingSet (coefficient (project F U)) l δ ⊆ decodingSet (coefficient F) l δ ∩ U := by
  classical
  intro i hi
  obtain ⟨S, hS, hiS⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨hcard, hlarge⟩ := (Finset.mem_filter.mp hS).2
  have hpos : 0 < l := (Finset.card_pos.mpr ⟨i, hiS⟩).trans_le hcard
  have hsub : S ⊆ U := by
    by_contra hn
    rw [Lax323828.FourierProjection.coefficient_project, if_neg hn] at hlarge
    have hmass : (0 : ℝ) < (l : ℝ) * δ := mul_pos (by exact_mod_cast hpos) hδ
    norm_num at hlarge
    linarith
  refine Finset.mem_inter.mpr ⟨?_, hsub hiS⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨S, ?_, hiS⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hcard, ?_⟩
  simpa [Lax323828.FourierProjection.coefficient_project, hsub] using hlarge

end Lax323828Proofs
