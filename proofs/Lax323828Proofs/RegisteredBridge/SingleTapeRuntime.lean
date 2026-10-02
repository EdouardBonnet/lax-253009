import Lax323828Proofs.RegisteredBridge.Time
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax323828Proofs.RegisteredBridge.SingleTapeRuntime

open Turing Time

variable {Γ Λ σ : Type} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]

/-- Elementary transitions needed by a straight-line TM1 block, including
the last jump or halt transition. The bound is independent of tape data. -/
def blockCost : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q | .write _ q => blockCost q + 1
  | .load _ q => blockCost q
  | .branch _ p q => max (blockCost p) (blockCost q)
  | .goto _ | .halt => 1

theorem block (M : Λ → TM1.Stmt Γ Λ σ) (q : TM1.Stmt Γ Λ σ)
    (v : σ) (T : Tape Γ) :
    ∃ n, 0 < n ∧ n ≤ blockCost q ∧
      Run (TM0.step (TM1to0.tr M)) n ⟨(some q, v), T⟩
        (TM1to0.trCfg M (TM1.stepAux q v T)) := by
  induction q generalizing v T with
  | move d q ih =>
    obtain ⟨n, hn, hbound, hr⟩ := ih v (T.move d)
    exact ⟨n + 1, by omega, by simpa [blockCost] using Nat.add_le_add_right hbound 1,
      .cons rfl hr⟩
  | write a q ih =>
    obtain ⟨n, hn, hbound, hr⟩ := ih v (T.write (a T.head v))
    exact ⟨n + 1, by omega, by simpa [blockCost] using Nat.add_le_add_right hbound 1,
      .cons rfl hr⟩
  | load a q ih =>
    obtain ⟨n, hn, hbound, hr⟩ := ih (a T.head v) T
    exact ⟨n, hn, hbound, hr.of_step_eq hn rfl⟩
  | branch p q₁ q₂ ih₁ ih₂ =>
    cases hp : p T.head v
    · obtain ⟨n, hn, hbound, hr⟩ := ih₂ v T
      refine ⟨n, hn, hbound.trans (Nat.le_max_right _ _), ?_⟩
      simp only [TM1.stepAux, hp, Bool.cond_false]
      exact hr.of_step_eq hn (by simp [TM0.step, TM1to0.tr, TM1to0.trAux, hp])
    · obtain ⟨n, hn, hbound, hr⟩ := ih₁ v T
      refine ⟨n, hn, hbound.trans (Nat.le_max_left _ _), ?_⟩
      simp only [TM1.stepAux, hp, Bool.cond_true]
      exact hr.of_step_eq hn (by simp [TM0.step, TM1to0.tr, TM1to0.trAux, hp])
  | goto l =>
    refine ⟨1, by decide, le_rfl, .one ?_⟩
    simp [TM0.step, TM1to0.tr, TM1to0.trAux, TM1to0.trCfg, TM1.stepAux,
      Tape.write_self]
  | halt =>
    refine ⟨1, by decide, le_rfl, .one ?_⟩
    simp [TM0.step, TM1to0.tr, TM1to0.trAux, TM1to0.trCfg, TM1.stepAux,
      Tape.write_self]

open scoped BigOperators

noncomputable def machineCost (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) : ℕ :=
  ∑ l ∈ S, blockCost (M l)

theorem run (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hS : TM1.Supports M S)
    {n : ℕ} {a b : TM1.Cfg Γ Λ σ} (h : Run (TM1.step M) n a b)
    (ha : a.l ∈ Finset.insertNone S) :
    Within (TM0.step (TM1to0.tr M)) (n * machineCost M S)
      (TM1to0.trCfg M a) (TM1to0.trCfg M b) := by
  classical
  induction h with
  | zero => exact (Within.refl _).mono (by simp)
  | @cons n a b c hs h ih =>
    have hb := TM1.step_supports M hS hs ha
    have hane : a.l ≠ none := by
      intro hn
      cases a
      simp_all [TM1.step]
    obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.mp hane
    have hls : l ∈ S := Finset.some_mem_insertNone.mp (hl ▸ ha)
    have he : b = TM1.stepAux (M l) a.var a.Tape := by
      cases a; simp_all [TM1.step]
    obtain ⟨t, ht, hbound, hr⟩ := block M (M l) a.var a.Tape
    have hc : blockCost (M l) ≤ machineCost M S := by
      exact Finset.single_le_sum (f := fun j ↦ blockCost (M j))
        (fun _ _ ↦ Nat.zero_le _) hls
    have hh : Within (TM0.step (TM1to0.tr M)) (machineCost M S)
        (TM1to0.trCfg M a) (TM1to0.trCfg M b) := by
      refine ⟨t, hbound.trans hc, ?_⟩
      simpa only [he, TM1to0.trCfg, hl, Option.map_some] using hr
    exact (hh.trans (ih hb)).mono (by simp [Nat.add_mul, Nat.add_comm])

end Lax323828Proofs.RegisteredBridge.SingleTapeRuntime
