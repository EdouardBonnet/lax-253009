import Lax323828Proofs.RegisteredBridge.SamplingAlgorithms
import Lax323828Proofs.MatrixSampling

set_option backward.isDefEq.respectTransparency false

namespace Lax323828Proofs.RegisteredBridge.ComputableSampling

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding ComputableNumbering
open Lax323828 FreshBitSampling

def seed (N k r : Word → ℕ) (hr : ∀ z, 0 < r z) (coins : Word → Word) :
    ∀ z, Fin (N z) → Fin (k z) → Fin (r z) :=
  fun z i j ↦ ⟨SamplingAlgorithms.draw (N z * k z) (r z) (coins z) (i.val * k z + j.val),
    Nat.mod_lt _ (hr z)⟩

theorem seed_realizes {N k r : Word → ℕ} (hr : ∀ z, 0 < r z)
    {coins : Word → Word} (hN : UnaryFn N) (hk : UnaryFn k) (hrpoly : UnaryFn r)
    (hcoins : coins ∈ FP) :
    Realizes (prod (unary N) (unary k)) (unary r) (fun z v ↦ seed N k r hr coins z v.1 v.2) := by
  have hi := UnaryFn.length (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hj := UnaryFn.length (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have hindex := (hi.mul (hk.comp pairFst_mem_FP)).add hj
  have hdraw := SamplingAlgorithms.draw_poly ((hN.mul hk).comp pairFst_mem_FP)
    (hrpoly.comp pairFst_mem_FP) hindex (mem_FP_comp pairFst_mem_FP hcoins)
  refine ⟨_, hdraw.mem_FP, ?_⟩
  intro z v
  simp only [prod, unary, Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]
  rfl

theorem draw_matrix {N k r : ℕ} (hr : 0 < r)
    (coins : Fin (N * k * bitsPerDraw (N * k) r) → Bool) (i : Fin N) (j : Fin k) :
    SamplingAlgorithms.draw (N * k) r (List.ofFn coins) (i.val * k + j.val) =
      (MatrixSampling.sample hr coins i j).val := by
  have he : i.val * k + j.val = (finProdFinEquiv (i, j)).val := by
    change i.val * k + j.val = j.val + k * i.val
    ring
  rw [he, SamplingAlgorithms.draw_eq_sample]
  rfl

end Lax323828Proofs.RegisteredBridge.ComputableSampling
