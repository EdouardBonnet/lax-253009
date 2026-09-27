import Lax253009Proofs.RegisteredBridge.TM2InputOutput
import Lax253009Proofs.PCPFoundation.Classes.P.Range

namespace Lax253009Proofs.RegisteredBridge.FiniteEncoding

open PCPFoundation.Complexity

theorem variable_drop_mem_FP {n : List Bool → ℕ} {f : List Bool → List Bool}
    (hn : UnaryFn n) (hf : f ∈ FP) : (fun z ↦ (f z).drop (n z)) ∈ FP := by
  have h := Cobham.dropFn (FP_subset_CobhamFP hn) (FP_subset_CobhamFP hf)
  apply CobhamFP_subset_FP
  change Cobham (fun v : Fin 1 → List Bool ↦ (f (v 0)).drop (n (v 0)))
  simpa only [List.length_replicate] using h

variable {A : Type} [Fintype A]

noncomputable def unpack (g : A → Bool) (z : List Bool) : List Bool :=
  (List.range (z.length / (Fintype.card A + 1))).map fun i ↦
    ((readHead ((z.drop ((Fintype.card A + 1) * i)).take (Fintype.card A + 1))).map g).getD false

theorem unpack_mem_FP (g : A → Bool) : unpack g ∈ FP := by
  have hn : UnaryFn (fun z : List Bool ↦ z.length / (Fintype.card A + 1)) :=
    (UnaryFn.length (CobhamFP_subset_FP (Cobham.proj (0 : Fin 1)))).div
      (UnaryFn.const _)
  have hdrop : (fun z : List Bool ↦ (pairFst z).drop
      ((Fintype.card A + 1) * (pairSnd z).length)) ∈ FP :=
    variable_drop_mem_FP ((UnaryFn.const _).mul (UnaryFn.length pairSnd_mem_FP)) pairFst_mem_FP
  have hread := bounded_read_mem_FP hdrop (Fintype.card A + 1)
    (fun key ↦ [((readHead key).map g).getD false])
  apply bitwise_mem_FP hn hread
  intro z i
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]

theorem drop_packets_n (i : ℕ) (l : List A) :
    (packets l).drop ((Fintype.card A + 1) * i) = packets (l.drop i) := by
  induction i generalizing l with
  | zero => simp
  | succ i ih =>
    cases l with
    | nil => simp
    | cons a l =>
      rw [Nat.mul_succ, Nat.add_comm, ← List.drop_drop]
      rw [drop_packets]
      exact ih l

theorem unpack_packets (g : A → Bool) (l : List A) : unpack g (packets l) = l.map g := by
  unfold unpack
  rw [packets_length, Nat.mul_div_cancel_left _ (by omega : 0 < Fintype.card A + 1)]
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_range, drop_packets_n, read_head_packets,
      List.head?_drop]
    have hil : i < l.length := by simpa only [List.length_map] using hi'
    rw [List.getElem?_eq_getElem hil]
    rfl

end Lax253009Proofs.RegisteredBridge.FiniteEncoding
