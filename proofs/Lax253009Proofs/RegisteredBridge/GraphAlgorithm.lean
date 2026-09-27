import Lax253009.Graphs
import Lax253009Proofs.RegisteredBridge.EstimatorSimulation
import Lax253009Proofs.PCPFoundation.Classes.P.Range

namespace Lax253009Proofs.RegisteredBridge

open PCPFoundation.Complexity Lax253009.Graphs

/-- Convert a numerical range enumeration to the corresponding finite-index enumeration. -/
theorem flatMap_range_finRange {A : Type} (n : ℕ) (f : ℕ → List A) (g : Fin n → List A)
    (h : ∀ i (hi : i < n), f i = g ⟨i, hi⟩) :
    (List.range n).flatMap f = (List.finRange n).flatMap g := by
  have hm : (List.range n).map f = (List.finRange n).map g := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
      apply h
  simpa only [List.flatMap_def] using congrArg List.flatten hm

/-- A graph with polynomial-time vertex count and adjacency can be written in the
submission's exact unary-header, row-major adjacency-matrix encoding. -/
theorem graph_encode_mem_FP {n : List Bool → ℕ} (G : ∀ z, Graph (n z))
    (hn : UnaryFn n) {edge : List Bool → List Bool} (hedge : edge ∈ FP)
    (hspec : ∀ z (u v : Fin (n z)),
      edge (pair (pair z (List.replicate u.val true)) (List.replicate v.val true)) =
        [(G z).adjacent u v]) :
    (fun z ↦ (G z).encode) ∈ FP := by
  let row : List Bool → List Bool := fun z ↦
    (List.range (n (pairFst z))).flatMap fun j ↦ edge (pair z (List.replicate j true))
  have hrow : row ∈ FP := by
    convert flatMap_range_mem_FP hedge (hn.comp pairFst_mem_FP).mem_FP using 1
    simp only [List.length_replicate]
    rfl
  let matrix : List Bool → List Bool := fun z ↦
    (List.range (n z)).flatMap fun i ↦ row (pair z (List.replicate i true))
  have hmatrix : matrix ∈ FP := by
    convert flatMap_range_mem_FP hrow hn.mem_FP using 1
    simp only [List.length_replicate]
    rfl
  have h := Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP hn.mem_FP (constFn_mem_FP [false])) hmatrix
  apply mem_FP_of_eq h
  intro z
  unfold Graph.encode
  congr 1
  dsimp only [matrix]
  apply flatMap_range_finRange
  intro i hi
  dsimp only [row]
  rw [pairFst_pair]
  calc
    _ = (List.finRange (n z)).flatMap (fun j ↦ [(G z).adjacent ⟨i, hi⟩ j]) := by
      apply flatMap_range_finRange
      intro j hj
      exact hspec z ⟨i, hi⟩ ⟨j, hj⟩
    _ = _ := List.map_eq_flatMap.symm

/-- Apply the registered clique estimator to a polynomial-time graph family. -/
theorem estimate_graph_comparison {estimate : List Bool → ℕ}
    (M : Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate)
    {n : List Bool → ℕ} (G : ∀ z, Graph (n z)) (hn : UnaryFn n)
    {edge : List Bool → List Bool} (hedge : edge ∈ FP)
    (hspec : ∀ z (u v : Fin (n z)),
      edge (pair (pair z (List.replicate u.val true)) (List.replicate v.val true)) =
        [(G z).adjacent u v])
    {threshold : List Bool → ℕ} (hthreshold : UnaryFn threshold) :
    FPPred fun z ↦ threshold z < estimate (G z).encode := by
  have hG := graph_encode_mem_FP G hn hedge hspec
  have henc := mem_FP_comp hG (encoded_mem_FP M)
  have hval := UnaryFn.fromBitsLE_min henc (hthreshold.add (UnaryFn.const 1))
  apply (FPPred.lt hthreshold hval).of_iff
  intro z
  simp only [Function.comp_apply, from_bits_encode_nat, lt_min_iff, Nat.lt_succ_self, and_true]

end Lax253009Proofs.RegisteredBridge
