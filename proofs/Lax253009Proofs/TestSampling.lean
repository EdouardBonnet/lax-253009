import Lax253009.TestSampling
import Lax253009Proofs.BernoulliSampling
import Lax253009Proofs.EncodedReduction

namespace Lax253009Proofs

open Lax253009.LocalTests Lax253009.TestSampling Lax253009.FiniteProbability
open Lax253009.ConsistencyGraph Lax253009.EncodedReduction Lax253009.BernoulliSampling
open scoped Classical

theorem local_test_optimum_attained {r m : ℕ} (C : System r m) :
    ∃ π : Oracle m, C.optimum = (C.acceptedSeeds π).card := by
  obtain ⟨π, _, hπ⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun π : Oracle m ↦ (C.acceptedSeeds π).card)
  exact ⟨π, hπ⟩

theorem local_test_optimum_le {r m : ℕ} (C : System r m) : C.optimum ≤ r := by
  exact Finset.sup_le fun π _ ↦ (C.acceptedSeeds π).card_le_univ.trans_eq (Fintype.card_fin r)

theorem sampled_count {r m N : ℕ} (C : System r m) (π : Oracle m) (z : Fin N → Fin r) :
    ((sampled C z).acceptedSeeds π).card = count N (Passes C π) z := by
  unfold System.acceptedSeeds count
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/--
---
conclusion: Lax253009.TestSampling.vertex_bound
---
Each sample retains the base accepting-view bound.
-/
theorem sampled_vertex_bound {r m N : ℕ} (C : System r m) (z : Fin N → Fin r)
    (A : ℕ) (hA : ∀ seed, (C.accepting seed).card ≤ A) :
    Fintype.card (Vertex (sampled C z)) ≤ N * A :=
  consistency_vertex_bound (sampled C z) A (fun i ↦ hA (z i))

/--
---
conclusion: Lax253009.TestSampling.perfect_completeness
---
A globally accepting proof accepts every sample, including repeated seeds.
-/
theorem sampled_perfect_completeness {r m N : ℕ} (C : System r m) (hC : Complete C)
    (z : Fin N → Fin r) : (output (sampled C z)).cliqueNumber = N := by
  rw [reduction_cliqueNumber]
  obtain ⟨π, hπ⟩ := hC
  apply le_antisymm (local_test_optimum_le _)
  have hfull : (sampled C z).acceptedSeeds π = Finset.univ := by
    ext i
    simp only [System.acceptedSeeds, Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_of_true (hπ (z i)) trivial
  have h := Finset.le_sup (f := fun π : Oracle m ↦ ((sampled C z).acceptedSeeds π).card)
    (Finset.mem_univ π)
  simpa only [hfull, Finset.card_univ, Fintype.card_fin, System.optimum] using h

/--
---
conclusion: Lax253009.TestSampling.soundness
---
The sampled clique number is attained by one of the 2^m global proofs.
Apply the multiplicative tail bound simultaneously to all of them.
-/
theorem sampled_soundness {r m N : ℕ} (hr : 0 < r) (C : System r m) (p : ℝ) (hp : 0 ≤ p)
    (hC : Sound C p) (hN : (m : ℝ) + 2 ≤ N * p) :
    probability (fun z : Fin N → Fin r ↦
      4 * N * p ≤ ((output (sampled C z)).cliqueNumber : ℝ)) ≤ 1 / 4 := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  apply le_trans (finite_probability_mono _
    (fun z : Fin N → Fin r ↦ ∃ π : Oracle m, 4 * N * p ≤ (count N (Passes C π) z : ℝ)) ?_)
    (bernoulli_sampling_uniform N m (Passes C) p hp (by simp [Oracle]) hC hN)
  intro z hz
  rw [reduction_cliqueNumber] at hz
  obtain ⟨π, hπ⟩ := local_test_optimum_attained (sampled C z)
  exact ⟨π, by simpa only [hπ, sampled_count] using hz⟩

end Lax253009Proofs
