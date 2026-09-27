import Lax253009Proofs.RegisteredBridge.StackTape
import Mathlib.Computability.TuringMachine.Computable

set_option backward.isDefEq.respectTransparency false

namespace Lax253009Proofs.RegisteredBridge.StackTapeMachine

open PCPFoundation.Complexity Turing

variable {I S Λ : Type} [DecidableEq I]

abbrev StackIndex (I : Type) := Bool ⊕ (I × Bool)

@[reducible] def Alphabet : StackIndex I → Type
  | .inl _ => Bool
  | .inr _ => Γ

abbrev Register (S I : Type) := S × (I → Γ) × Bool

def registers (s : S) (t : I → StackTape) (b : Bool) : Register S I :=
  (s, fun i ↦ (t i).current, b)

def tapeStacks (io : Bool → List Bool) (t : I → StackTape) : (k : StackIndex I) → List (Alphabet k)
  | .inl b => io b
  | .inr (i, false) => (t i).left
  | .inr (i, true) => (t i).right

theorem heads_update (t : I → StackTape) (i : I) (u : StackTape) :
    (fun j ↦ (Function.update t i u j).current) =
      Function.update (fun j ↦ (t j).current) i u.current := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [Function.update_of_ne h]

theorem stacks_update (io : Bool → List Bool) (t : I → StackTape) (i : I) (u : StackTape) :
    tapeStacks io (Function.update t i u) =
      Function.update (Function.update (tapeStacks io t) (.inr (i, false)) u.left)
        (.inr (i, true)) u.right := by
  funext k
  cases k with
  | inl b => simp [tapeStacks, Function.update]
  | inr p =>
    obtain ⟨j, b⟩ := p
    by_cases h : j = i
    · subst j; cases b <;> simp [tapeStacks, Function.update]
    · cases b <;> simp [tapeStacks, Function.update, h]

theorem stacks_update_rev (io : Bool → List Bool) (t : I → StackTape) (i : I) (u : StackTape) :
    tapeStacks io (Function.update t i u) =
      Function.update (Function.update (tapeStacks io t) (.inr (i, true)) u.right)
        (.inr (i, false)) u.left := by
  rw [stacks_update, Function.update_comm (by simp)]

abbrev Stmt (S I Λ : Type) := TM2.Stmt (Alphabet (I := I)) Λ (Register S I)

def right (i : I) (q : Stmt S I Λ) : Stmt S I Λ :=
  .push (.inr (i, false)) (fun v ↦ v.2.1 i)
    (.pop (.inr (i, true)) (fun v a ↦ (v.1, Function.update v.2.1 i (a.getD Γ.blank), v.2.2)) q)

def left (i : I) (q : Stmt S I Λ) : Stmt S I Λ :=
  .peek (.inr (i, false)) (fun v a ↦ (v.1, v.2.1, a.isSome))
    (.branch (fun v ↦ v.2.2)
      (.push (.inr (i, true)) (fun v ↦ v.2.1 i)
        (.pop (.inr (i, false)) (fun v a ↦ (v.1, Function.update v.2.1 i (a.getD Γ.blank), v.2.2)) q)) q)

def write (i : I) (a : S → Γ) (q : Stmt S I Λ) : Stmt S I Λ :=
  .peek (.inr (i, false)) (fun v o ↦ (v.1, v.2.1, o.isSome))
    (.branch (fun v ↦ v.2.2)
      (.load (fun v ↦ (v.1, Function.update v.2.1 i (a v.1), v.2.2)) q) q)

theorem right_step (io : Bool → List Bool) (s : S) (t : I → StackTape) (b : Bool)
    (i : I) (q : Stmt S I Λ) :
    TM2.stepAux (right i q) (registers s t b) (tapeStacks io t) =
      TM2.stepAux q (registers s (Function.update t i (t i).moveRight) b)
        (tapeStacks io (Function.update t i (t i).moveRight)) := by
  simp only [right, TM2.stepAux, registers, tapeStacks, Function.update_of_ne
    (show (Sum.inr (i, true) : StackIndex I) ≠ .inr (i, false) by simp)]
  rw [stacks_update]
  simp only [StackTape.moveRight, registers, heads_update]

theorem left_step (io : Bool → List Bool) (s : S) (t : I → StackTape) (b : Bool)
    (i : I) (q : Stmt S I Λ) :
    TM2.stepAux (left i q) (registers s t b) (tapeStacks io t) =
      TM2.stepAux q (registers s (Function.update t i (t i).moveLeft) (t i).left.head?.isSome)
        (tapeStacks io (Function.update t i (t i).moveLeft)) := by
  cases hl : (t i).left with
  | nil =>
    have ht : (t i).moveLeft = t i := by simp [StackTape.moveLeft, hl]
    simp [left, TM2.stepAux, registers, tapeStacks, ht, hl, Function.update_eq_self]
  | cons a l =>
    simp only [left, TM2.stepAux, registers, tapeStacks, hl, List.head?_cons, Option.isSome_some,
      Bool.cond_true, Function.update_of_ne
        (show (Sum.inr (i, false) : StackIndex I) ≠ .inr (i, true) by simp),
      List.tail_cons, Option.getD_some]
    rw [stacks_update_rev]
    simp only [registers, heads_update, StackTape.moveLeft, hl]

theorem write_step (io : Bool → List Bool) (s : S) (t : I → StackTape) (b : Bool)
    (i : I) (a : S → Γ) (q : Stmt S I Λ) :
    TM2.stepAux (write i a q) (registers s t b) (tapeStacks io t) =
      TM2.stepAux q (registers s (Function.update t i ((t i).write (a s))) (t i).left.head?.isSome)
        (tapeStacks io (Function.update t i ((t i).write (a s)))) := by
  cases hl : (t i).left with
  | nil =>
    have ht : (t i).write (a s) = t i := by simp [StackTape.write, hl]
    simp [write, TM2.stepAux, registers, tapeStacks, ht, hl, Function.update_eq_self]
  | cons c l =>
    simp only [write, TM2.stepAux, registers, tapeStacks, hl, List.head?_cons, Option.isSome_some,
      Bool.cond_true]
    rw [stacks_update]
    simp only [registers, heads_update, StackTape.write, hl, List.cons_ne_nil, if_false]
    congr 1
    funext k
    cases k with
    | inl b => simp [tapeStacks, Function.update]
    | inr p =>
      obtain ⟨j, b⟩ := p
      by_cases h : j = i
      · subst j; cases b <;> simp [tapeStacks, Function.update, hl]
      · cases b <;> simp [tapeStacks, Function.update, h]

def move (i : I) (d : S → Dir3) (q : Stmt S I Λ) : Stmt S I Λ :=
  .branch (fun v ↦ decide (d v.1 = .left)) (left i q)
    (.branch (fun v ↦ decide (d v.1 = .right)) (right i q) q)

theorem move_step (io : Bool → List Bool) (s : S) (t : I → StackTape) (b : Bool)
    (i : I) (d : S → Dir3) (q : Stmt S I Λ) :
    ∃ b' : Bool, TM2.stepAux (move i d q) (registers s t b) (tapeStacks io t) =
      TM2.stepAux q (registers s (Function.update t i ((t i).move (d s))) b')
        (tapeStacks io (Function.update t i ((t i).move (d s)))) := by
  cases hd : d s with
  | left =>
    refine ⟨(t i).left.head?.isSome, ?_⟩
    simpa only [move, TM2.stepAux, registers, hd, decide_true, Bool.cond_true,
      StackTape.move] using left_step io s t b i q
  | right =>
    refine ⟨b, ?_⟩
    simpa only [move, TM2.stepAux, registers, hd, reduceCtorEq,
      decide_false, decide_true, Bool.cond_false, Bool.cond_true, StackTape.move] using
      right_step io s t b i q
  | stay =>
    refine ⟨b, ?_⟩
    simp [move, TM2.stepAux, registers, hd, StackTape.move, Function.update_eq_self]

def writeMove (i : I) (a : S → Γ) (d : S → Dir3) (q : Stmt S I Λ) : Stmt S I Λ :=
  write i a (move i d q)

theorem write_move_step (io : Bool → List Bool) (s : S) (t : I → StackTape) (b : Bool)
    (i : I) (a : S → Γ) (d : S → Dir3) (q : Stmt S I Λ) :
    ∃ b' : Bool, TM2.stepAux (writeMove i a d q) (registers s t b) (tapeStacks io t) =
      TM2.stepAux q (registers s (Function.update t i (((t i).write (a s)).move (d s))) b')
        (tapeStacks io (Function.update t i (((t i).write (a s)).move (d s)))) := by
  rw [writeMove, write_step]
  obtain ⟨b', h⟩ := move_step io s (Function.update t i ((t i).write (a s)))
    (t i).left.head?.isSome i d q
  exact ⟨b', by simpa only [Function.update_self, Function.update_idem] using h⟩

def tapeEffect (w : I → Bool) (a : S → I → Γ) (d : S → I → Dir3)
    (s : S) (i : I) (t : StackTape) : StackTape :=
  (if w i then t.write (a s i) else t).move (d s i)

def act (w : I → Bool) (a : S → I → Γ) (d : S → I → Dir3)
    (i : I) (q : Stmt S I Λ) : Stmt S I Λ :=
  if w i then writeMove i (fun s ↦ a s i) (fun s ↦ d s i) q else move i (fun s ↦ d s i) q

theorem act_step (w : I → Bool) (a : S → I → Γ) (d : S → I → Dir3)
    (io : Bool → List Bool) (s : S) (t : I → StackTape) (b : Bool)
    (i : I) (q : Stmt S I Λ) :
    ∃ b' : Bool, TM2.stepAux (act w a d i q) (registers s t b) (tapeStacks io t) =
      TM2.stepAux q (registers s (Function.update t i (tapeEffect w a d s i (t i))) b')
        (tapeStacks io (Function.update t i (tapeEffect w a d s i (t i)))) := by
  cases hw : w i
  · simpa only [act, tapeEffect, hw, Bool.false_eq_true, if_false] using
      move_step io s t b i (fun s ↦ d s i) q
  · simpa only [act, tapeEffect, hw, if_true] using
      write_move_step io s t b i (fun s ↦ a s i) (fun s ↦ d s i) q

def sweep (w : I → Bool) (a : S → I → Γ) (d : S → I → Dir3)
    (indices : List I) (q : Stmt S I Λ) : Stmt S I Λ :=
  indices.foldr (act w a d) q

def sweepTapes (f : I → StackTape → StackTape) (indices : List I) (t : I → StackTape) :
    I → StackTape := indices.foldl (fun ts i ↦ Function.update ts i (f i (ts i))) t

theorem sweep_step (w : I → Bool) (a : S → I → Γ) (d : S → I → Dir3)
    (io : Bool → List Bool) (s : S) (t : I → StackTape) (b : Bool)
    (indices : List I) (q : Stmt S I Λ) :
    ∃ b' : Bool, TM2.stepAux (sweep w a d indices q) (registers s t b) (tapeStacks io t) =
      TM2.stepAux q (registers s (sweepTapes (tapeEffect w a d s) indices t) b')
        (tapeStacks io (sweepTapes (tapeEffect w a d s) indices t)) := by
  induction indices generalizing t b with
  | nil => exact ⟨b, rfl⟩
  | cons i indices ih =>
    obtain ⟨c, hc⟩ := act_step w a d io s t b i (sweep w a d indices q)
    obtain ⟨b', hb⟩ := ih (Function.update t i (tapeEffect w a d s i (t i))) c
    exact ⟨b', hc.trans hb⟩

theorem sweep_tapes_apply (f : I → StackTape → StackTape) (indices : List I)
    (h : indices.Nodup) (t : I → StackTape) (j : I) :
    sweepTapes f indices t j = if j ∈ indices then f j (t j) else t j := by
  induction indices generalizing t with
  | nil => simp [sweepTapes]
  | cons i indices ih =>
    obtain ⟨hi, htail⟩ := List.nodup_cons.mp h
    change sweepTapes f indices (Function.update t i (f i (t i))) j = _
    rw [ih htail]
    by_cases hj : j = i
    · subst j
      simp [hi]
    · simp [hj, Function.update_of_ne hj]

theorem sweep_all_step [Fintype I] (w : I → Bool) (a : S → I → Γ) (d : S → I → Dir3)
    (io : Bool → List Bool) (s : S) (t : I → StackTape) (b : Bool) (q : Stmt S I Λ) :
    ∃ b' : Bool, TM2.stepAux (sweep w a d Finset.univ.toList q) (registers s t b) (tapeStacks io t) =
      TM2.stepAux q (registers s (fun i ↦ tapeEffect w a d s i (t i)) b')
        (tapeStacks io (fun i ↦ tapeEffect w a d s i (t i))) := by
  obtain ⟨b', hb⟩ := sweep_step w a d io s t b Finset.univ.toList q
  have he : sweepTapes (tapeEffect w a d s) Finset.univ.toList t =
      (fun i ↦ tapeEffect w a d s i (t i)) := by
    funext i
    simp [sweep_tapes_apply _ _ (Finset.nodup_toList _)]
  exact ⟨b', by simpa only [he] using hb⟩

end Lax253009Proofs.RegisteredBridge.StackTapeMachine
