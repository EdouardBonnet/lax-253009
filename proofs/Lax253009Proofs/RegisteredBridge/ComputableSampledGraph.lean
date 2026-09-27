import Lax253009Proofs.RegisteredBridge.ComputableSampling
import Lax253009Proofs.RegisteredBridge.Reparameterize
import Lax253009Proofs.RegisteredBridge.RepeatedSlotAlgorithms

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax253009Proofs.RegisteredBridge.ComputableSampledGraph

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding ComputableNumbering
open Lax253009 LocalTests SamplingParameters FreshBitSampling
open scoped Classical

variable {r m : Word → ℕ} {C : ∀ x, LocalTests.System (r x) (m x)} {f : ℕ}

def size (f t c m : ℕ) : ℕ := sampleCount t (repetitions c m) m * (2 ^ f) ^ repetitions c m

noncomputable def graph (E : ∀ x, SlotGraph.Enumeration (C x) (2 ^ f)) (hr : ∀ x, 0 < r x)
    (t c : ℕ) (x coins : Word) : Graphs.Graph (size f t c (m x)) :=
  SlotGraph.output (RepeatedSlotViews.repeatedEnumeration (E x) (repetitions c (m x))
    (sampleCount t (repetitions c (m x)) (m x))
    (fun i j ↦ ⟨SamplingAlgorithms.draw
      (sampleCount t (repetitions c (m x)) (m x) * repetitions c (m x))
      (r x) coins (i.val * repetitions c (m x) + j.val), Nat.mod_lt _ (hr x)⟩))

theorem size_eq (f t c m : ℕ) : size f t c m = vertexBound f t (repetitions c m) m := by
  simp only [size, sampleCount, vertexBound, ← pow_mul, mul_assoc, ← pow_add]
  congr 2
  ring

theorem size_pos (f t c m : ℕ) : 0 < size f t c m := by
  unfold size sampleCount
  positivity

/-- The entire sampled adjacency matrix is polynomial-time in the input word
and the supplied random tape. The verifier parameters are fixed constants. -/
theorem encode_mem_FP (E : ∀ x, SlotGraph.Enumeration (C x) (2 ^ f))
    (hr : ∀ x, 0 < r x) (hE : SlotGraphAlgorithms.Algorithms E)
    (hrpoly : UnaryFn r) (hmpoly : UnaryFn m) (t c : ℕ) :
    (fun z ↦ (graph E hr t c (pairFst z) (pairSnd z)).encode) ∈ FP := by
  let k := fun z ↦ repetitions c (m (pairFst z))
  let N := fun z ↦ sampleCount t (k z) (m (pairFst z))
  let R := fun z ↦ r (pairFst z)
  let M := fun z ↦ m (pairFst z)
  have hk : UnaryFn k := (SamplingAlgorithms.repetitions_poly hmpoly c).comp pairFst_mem_FP
  have hN : UnaryFn N := (SamplingAlgorithms.sampleCount_poly hmpoly c t).comp pairFst_mem_FP
  have hR : UnaryFn R := hrpoly.comp pairFst_mem_FP
  have hM : UnaryFn M := hmpoly.comp pairFst_mem_FP
  let S := ComputableSampling.seed N k R (fun z ↦ hr (pairFst z)) pairSnd
  have hS := ComputableSampling.seed_realizes (coins := pairSnd) (fun z ↦ hr (pairFst z))
    hN hk hR pairSnd_mem_FP
  have hbase := hE.reparameterize pairFst_mem_FP
  have hrepeated := RepeatedSlotAlgorithms.algorithms
    (fun z ↦ E (pairFst z)) hbase S hS hM hk (UnaryFn.const (2 ^ f))
  have hA : UnaryFn (fun z ↦ (2 ^ f) ^ k z) := by
    simpa only [pow_mul] using (SamplingAlgorithms.repetition_power_poly hmpoly c f).comp pairFst_mem_FP
  exact SlotGraphAlgorithms.encode_mem_FP _ hrepeated hN hM hA

theorem graph_of_coins (E : ∀ x, SlotGraph.Enumeration (C x) (2 ^ f))
    (hr : ∀ x, 0 < r x) (t c : ℕ) (x : Word)
    (coins : Fin (sampleCount t (repetitions c (m x)) (m x) * repetitions c (m x) *
      bitsPerDraw (sampleCount t (repetitions c (m x)) (m x) * repetitions c (m x)) (r x)) → Bool) :
    graph E hr t c x (List.ofFn coins) =
      SlotGraph.output (RepeatedSlotViews.repeatedEnumeration (E x) (repetitions c (m x))
        (sampleCount t (repetitions c (m x)) (m x)) (MatrixSampling.sample (hr x) coins)) := by
  let k := repetitions c (m x)
  let N := sampleCount t k (m x)
  have hs : (fun (i : Fin N) (j : Fin k) ↦
      (⟨SamplingAlgorithms.draw (N * k) (r x) (List.ofFn coins) (i.val * k + j.val),
        Nat.mod_lt _ (hr x)⟩ : Fin (r x))) = MatrixSampling.sample (hr x) coins := by
    funext i j
    apply Fin.ext
    exact ComputableSampling.draw_matrix (hr x) coins i j
  exact congrArg (fun seed ↦ SlotGraph.output
    (RepeatedSlotViews.repeatedEnumeration (E x) k N seed)) hs

end Lax253009Proofs.RegisteredBridge.ComputableSampledGraph
