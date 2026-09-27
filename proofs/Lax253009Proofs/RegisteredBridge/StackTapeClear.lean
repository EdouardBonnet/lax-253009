import Lax253009Proofs.RegisteredBridge.StackTapeMachine

set_option backward.isDefEq.respectTransparency false

namespace Lax253009Proofs.RegisteredBridge.StackTapeMachine

open PCPFoundation.Complexity Turing

variable {I S Λ : Type} [DecidableEq I]

def thin (t : StackTape) : StackTape := ⟨t.left.tail, t.current, t.right.tail⟩

def dirty (t : StackTape) : Bool := t.left.head?.isSome || t.right.head?.isSome

def clearPair (i : I) (q : Stmt S I Λ) : Stmt S I Λ :=
  .pop (.inr (i, false)) (fun v a ↦ (v.1, v.2.1, v.2.2 || a.isSome))
    (.pop (.inr (i, true)) (fun v a ↦ (v.1, v.2.1, v.2.2 || a.isSome)) q)

theorem clear_pair_step (io : Bool → List Bool) (s : S) (t : I → StackTape) (b : Bool)
    (i : I) (q : Stmt S I Λ) :
    TM2.stepAux (clearPair i q) (registers s t b) (tapeStacks io t) =
      TM2.stepAux q (registers s (Function.update t i (thin (t i))) (b || dirty (t i)))
        (tapeStacks io (Function.update t i (thin (t i)))) := by
  simp only [clearPair, TM2.stepAux, registers, tapeStacks, Function.update_of_ne
    (show (Sum.inr (i, true) : StackIndex I) ≠ .inr (i, false) by simp)]
  rw [stacks_update]
  simp only [registers, heads_update, thin, dirty, Bool.or_assoc]
  rw [Function.update_eq_self]

def clearSweep (indices : List I) (q : Stmt S I Λ) : Stmt S I Λ :=
  indices.foldr clearPair q

theorem dirty_update_ne (t : I → StackTape) (i j : I) (h : j ≠ i) :
    dirty (Function.update t i (thin (t i)) j) = dirty (t j) := by
  rw [Function.update_of_ne h]

theorem clear_sweep_step (io : Bool → List Bool) (s : S) (t : I → StackTape) (b : Bool)
    (indices : List I) (hi : indices.Nodup) (q : Stmt S I Λ) :
    TM2.stepAux (clearSweep indices q) (registers s t b) (tapeStacks io t) =
      TM2.stepAux q
        (registers s (sweepTapes (fun _ ↦ thin) indices t)
          (b || indices.any (fun i ↦ dirty (t i))))
        (tapeStacks io (sweepTapes (fun _ ↦ thin) indices t)) := by
  induction indices generalizing t b with
  | nil => simp [clearSweep, sweepTapes]
  | cons i indices ih =>
    obtain ⟨hne, hnd⟩ := List.nodup_cons.mp hi
    rw [clearSweep, List.foldr_cons, clear_pair_step]
    change TM2.stepAux (clearSweep indices q) _ _ = _
    rw [ih _ _ hnd]
    have he : indices.any (fun j ↦ dirty (Function.update t i (thin (t i)) j)) =
        indices.any (fun j ↦ dirty (t j)) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨j, hj, h⟩
        exact ⟨j, hj, (dirty_update_ne t i j (fun h ↦ hne (h ▸ hj))) ▸ h⟩
      · rintro ⟨j, hj, h⟩
        exact ⟨j, hj, (dirty_update_ne t i j (fun h ↦ hne (h ▸ hj))).symm ▸ h⟩
    simp only [he, List.any_cons, Bool.or_assoc, sweepTapes, List.foldl_cons]

noncomputable def allDirty [Fintype I] (t : I → StackTape) : Bool :=
  Finset.univ.toList.any (fun i ↦ dirty (t i))

theorem all_dirty_eq_false [Fintype I] (t : I → StackTape) :
    allDirty t = false ↔ ∀ i, (t i).left = [] ∧ (t i).right = [] := by
  simp [allDirty, List.any_eq_false, dirty, Bool.or_eq_false_iff]

theorem clear_all_step [Fintype I] (io : Bool → List Bool) (s : S) (t : I → StackTape)
    (b : Bool) (q : Stmt S I Λ) :
    TM2.stepAux (clearSweep Finset.univ.toList q) (registers s t b) (tapeStacks io t) =
      TM2.stepAux q (registers s (fun i ↦ thin (t i)) (b || allDirty t))
        (tapeStacks io (fun i ↦ thin (t i))) := by
  have he : sweepTapes (fun _ ↦ thin) Finset.univ.toList t = (fun i ↦ thin (t i)) := by
    funext i
    simp [sweep_tapes_apply _ _ (Finset.nodup_toList _)]
  simpa only [he, allDirty] using clear_sweep_step io s t b Finset.univ.toList
    (Finset.nodup_toList _) q

end Lax253009Proofs.RegisteredBridge.StackTapeMachine
