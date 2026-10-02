import Lax323828Proofs.RegisteredBridge.PacketDecoding
import Lax323828Proofs.RegisteredBridge.FiniteAlphabet

set_option backward.isDefEq.respectTransparency false

namespace Lax323828Proofs.RegisteredBridge

open PCPFoundation.Complexity Turing FiniteEncoding StackEncoding

/-- The finite-stack simulation preserves arbitrary binary-encoded outputs. -/
theorem encoded_mem_FP_of_finite_stack {B : Type} {enc : B → List Bool} {f : List Bool → B}
    (M : TM2ComputableInPolyTime id enc f)
    (hfinite : ∀ k, Finite (M.tm.Γ k)) : (fun z ↦ enc (f z)) ∈ FP := by
  classical
  letI : Fintype M.tm.K := M.tm.kFin
  letI : Fintype M.tm.Λ := M.tm.ΛFin
  letI : Fintype M.tm.σ := M.tm.σFin
  letI (k : M.tm.K) : Fintype (M.tm.Γ k) := Fintype.ofFinite (M.tm.Γ k)
  obtain ⟨ruler, hruler, hrlen⟩ := Cobham.exists_ruler M.time
  have hrun := compile_run M.tm.m
    (fun z ↦ initList M.tm (z.map M.inputAlphabet.symm)) ruler
    (init_encode_mem_FP M.tm M.inputAlphabet.symm) hruler
    (init_stack_length M.tm M.inputAlphabet.symm)
  have hread := mem_FP_comp (stack_mem_FP M.tm.k₁) (unpack_mem_FP M.outputAlphabet)
  have hout := mem_FP_comp hrun hread
  apply mem_FP_of_eq hout
  intro z
  have h := M.outputsFun z
  have hs : (totalStep M.tm.m)^[(ruler z).length]
      (initList M.tm (z.map M.inputAlphabet.symm)) =
      haltList M.tm ((enc (f z)).map M.outputAlphabet.symm) :=
    total_run_after_halt M.tm.m h.evals_in_steps rfl (h.steps_le_m.trans (hrlen z))
  dsimp only [Function.comp_apply]
  rw [hs, stack_encode, unpack_packets]
  simp [haltList, List.map_map]

/-- Every function computed by the registered polynomial-time stack model has an `FP` encoding. -/
theorem encoded_mem_FP {B : Type} {enc : B → List Bool} {f : List Bool → B}
    (M : TM2ComputableInPolyTime id enc f) : (fun z ↦ enc (f z)) ∈ FP := by
  obtain ⟨N, _, hN⟩ := FiniteAlphabet.binary_computer M
  exact encoded_mem_FP_of_finite_stack N hN

end Lax323828Proofs.RegisteredBridge
