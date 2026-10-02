import Lax323828Proofs.RegisteredBridge.MultitapeCore
import Lax323828Proofs.RegisteredBridge.StackTapeClear
import Lax323828Proofs.PCPFoundation.Classes.P.Defs
import Lax323828Proofs.PCPFoundation.Asymptotics.PolyBound

set_option backward.isDefEq.respectTransparency false

namespace Lax323828Proofs.RegisteredBridge.MultitapeTransducer

open PCPFoundation.Complexity Turing StackTapeMachine MultitapeCore Time


theorem cfg_ext {K Λ σ : Type} {A : K → Type} {c d : TM2.Cfg A Λ σ}
    (hl : c.l = d.l) (hv : c.var = d.var) (hs : c.stk = d.stk) : c = d := by
  cases c
  cases d
  cases hl
  cases hv
  cases hs
  rfl

inductive Label | readInput | reverseInput | simulate | rewindOutput | copyOutput | reverseOutput | clear
  deriving DecidableEq, Fintype

variable {n : ℕ}

abbrev input : Index n := .inl false
abbrev output : Index n := .inl true

def initial (M : TM n) : Register (Cache M.Q n) (Index n) :=
  (initialCache M, fun _ ↦ Γ.start, false)

noncomputable def program (M : TM n) : Label → Stmt (Cache M.Q n) (Index n) Label
  | .readInput =>
    .pop (.inl false) (fun v a ↦
      (v.1, Function.update v.2.1 input (Γ.ofBool (a.getD false)), a.isSome))
      (.branch (fun v ↦ v.2.2)
        (.push (.inr (input, false)) (fun v ↦ v.2.1 input) (.goto fun _ ↦ .readInput))
        (.goto fun _ ↦ .reverseInput))
  | .reverseInput =>
    .pop (.inr (input, false)) (fun v a ↦
      (v.1, Function.update v.2.1 input (a.getD Γ.blank), a.isSome))
      (.branch (fun v ↦ v.2.2)
        (.push (.inr (input, true)) (fun v ↦ v.2.1 input) (.goto fun _ ↦ .reverseInput))
        (.load (fun _ ↦ initial M) (.goto fun _ ↦ .simulate)))
  | .simulate => body M .simulate (.goto fun _ ↦ .rewindOutput)
  | .rewindOutput =>
    .peek (.inr (output, false)) (fun v a ↦ (v.1, v.2.1, a.isSome))
      (.branch (fun v ↦ v.2.2)
        (left output (.goto fun _ ↦ .rewindOutput)) (.goto fun _ ↦ .copyOutput))
  | .copyOutput =>
    .pop (.inr (output, true)) (fun v a ↦
      (v.1, Function.update v.2.1 output (a.getD Γ.blank), v.2.2))
      (.branch (fun v ↦ decide (v.2.1 output = Γ.zero ∨ v.2.1 output = Γ.one))
        (.push (.inl false) (fun v ↦ decide (v.2.1 output = Γ.one))
          (.goto fun _ ↦ .copyOutput)) (.goto fun _ ↦ .reverseOutput))
  | .reverseOutput =>
    .pop (.inl false) (fun v a ↦ ({v.1 with verdict := a.getD false}, v.2.1, a.isSome))
      (.branch (fun v ↦ v.2.2)
        (.push (.inl true) (fun v ↦ v.1.verdict) (.goto fun _ ↦ .reverseOutput))
        (.goto fun _ ↦ .clear))
  | .clear =>
    .load (fun v ↦ (v.1, v.2.1, false))
      (clearSweep Finset.univ.toList
        (.branch (fun v ↦ v.2.2) (.goto fun _ ↦ .clear)
          (.load (fun _ ↦ initial M) .halt)))

noncomputable def machine (M : TM n) : FinTM2 where
  K := StackIndex (Index n)
  k₀ := .inl false
  k₁ := .inl true
  Γ := Alphabet
  Λ := Label
  main := .readInput
  σ := Register (Cache M.Q n) (Index n)
  initialState := initial M
  m := program M

def bufferHeads (a : Γ) : Index n → Γ
  | .inl false => a
  | _ => Γ.start

def bufferStacks (w : List Bool) (l r : List Γ) :
    (k : StackIndex (Index n)) → List (Alphabet k)
  | .inl false => w
  | .inl true => []
  | .inr (.inl false, false) => l
  | .inr (.inl false, true) => r
  | _ => []

def buffer (M : TM n) (label : Label) (a : Γ) (b : Bool)
    (w : List Bool) (l r : List Γ) : (machine M).Cfg :=
  ⟨some label, (initialCache M, bufferHeads a, b), bufferStacks w l r⟩

theorem buffer_heads_update (a c : Γ) :
    Function.update (bufferHeads (n := n) a) input c = bufferHeads c := by
  funext i
  cases i with
  | inl b => cases b <;> simp [bufferHeads, Function.update, input]
  | inr i => simp [bufferHeads, Function.update, input]

theorem read_cons (M : TM n) (a : Γ) (b x : Bool) (w : List Bool) (l r : List Γ) :
    (machine M).step (buffer M .readInput a b (x :: w) l r) =
      some (buffer M .readInput (Γ.ofBool x) true w (Γ.ofBool x :: l) r) := by
  simp only [FinTM2.step, machine, program, buffer, TM2.step, TM2.stepAux,
    bufferStacks, List.head?_cons, Option.getD_some, Option.isSome_some,
    Bool.cond_true, buffer_heads_update, bufferHeads, List.tail_cons]
  congr 2
  funext k
  cases k with
  | inl b => cases b <;> rfl
  | inr p => obtain ⟨i, b⟩ := p; cases i with
    | inl c => cases c <;> cases b <;> rfl
    | inr i => cases b <;> rfl

theorem read_nil (M : TM n) (a : Γ) (b : Bool) (l r : List Γ) :
    (machine M).step (buffer M .readInput a b [] l r) =
      some (buffer M .reverseInput (Γ.ofBool false) false [] l r) := by
  simp [FinTM2.step, machine, program, buffer, TM2.step, TM2.stepAux,
    bufferStacks, buffer_heads_update]

theorem read_run (M : TM n) (a : Γ) (b : Bool) (w : List Bool) (l r : List Γ) :
    Run (machine M).step (w.length + 1) (buffer M .readInput a b w l r)
      (buffer M .reverseInput (Γ.ofBool false) false []
        (w.reverse.map Γ.ofBool ++ l) r) := by
  induction w generalizing a b l with
  | nil => exact .one (read_nil M a b l r)
  | cons x w ih =>
    simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append] using!
      Run.cons (read_cons M a b x w l r) (ih (Γ.ofBool x) true (Γ.ofBool x :: l))

theorem reverse_cons (M : TM n) (a x : Γ) (b : Bool) (l r : List Γ) :
    (machine M).step (buffer M .reverseInput a b [] (x :: l) r) =
      some (buffer M .reverseInput x true [] l (x :: r)) := by
  simp only [FinTM2.step, machine, program, buffer, TM2.step, TM2.stepAux,
    bufferStacks, List.head?_cons, Option.getD_some, Option.isSome_some,
    Bool.cond_true, buffer_heads_update, bufferHeads, List.tail_cons]
  congr 2
  funext k
  cases k with
  | inl b => cases b <;> rfl
  | inr p => obtain ⟨i, b⟩ := p; cases i with
    | inl c => cases c <;> cases b <;> rfl
    | inr i => cases b <;> rfl

def initialTapes (w : List Bool) : Index n → StackTape
  | .inl false => StackTape.init (w.map Γ.ofBool)
  | _ => StackTape.init []

theorem initial_cfg (M : TM n) (w : List Bool) :
    toCfg (initialCache M) (initialTapes w) = M.initCfg w := by
  apply Cfg.ext
  · rfl
  · exact StackTape.toTape_init _
  · funext i; exact StackTape.toTape_init _
  · exact StackTape.toTape_init _

theorem reverse_nil (M : TM n) (a : Γ) (b : Bool) (r : List Γ) :
    (machine M).step (buffer M .reverseInput a b [] [] r) =
      some (buffer M .simulate Γ.start false [] [] r) := by
  simp [FinTM2.step, machine, program, buffer, TM2.step, TM2.stepAux,
    bufferStacks, initial]
  congr 2
  funext i
  cases i with
  | inl b => cases b <;> rfl
  | inr i => rfl

theorem reverse_run (M : TM n) (a : Γ) (b : Bool) (l r : List Γ) :
    Run (machine M).step (l.length + 1) (buffer M .reverseInput a b [] l r)
      (buffer M .simulate Γ.start false [] [] (l.reverse ++ r)) := by
  induction l generalizing a b r with
  | nil => exact .one (reverse_nil M a b r)
  | cons x l ih =>
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using!
      Run.cons (reverse_cons M a x b l r) (ih x true (x :: r))

theorem init_buffer (M : TM n) (w : List Bool) :
    initList (machine M) w = buffer M .readInput Γ.start false w [] [] := by
  apply cfg_ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i; cases i with
        | inl b => cases b <;> rfl
        | inr i => rfl
      · rfl
  · funext k
    cases k with
    | inl b => cases b <;> simp [initList, machine, buffer, bufferStacks]
    | inr p => obtain ⟨i, b⟩ := p; cases i with
      | inl c => cases c <;> cases b <;> simp [initList, machine, buffer, bufferStacks]
      | inr i => cases b <;> simp [initList, machine, buffer, bufferStacks]

theorem buffer_initial_tapes (M : TM n) (w : List Bool) :
    buffer M .simulate Γ.start false [] [] (w.map Γ.ofBool) =
      config (some Label.simulate) (initialCache M) (fun _ ↦ []) (initialTapes w) false := by
  apply cfg_ext
  · rfl
  · change (initialCache M, bufferHeads Γ.start, false) =
      (initialCache M, (fun i ↦ (initialTapes w i).current), false)
    apply congrArg (fun heads : Index n → Γ ↦ (initialCache M, heads, false))
    funext i
    cases i with
    | inl b => cases b <;> rfl
    | inr i => rfl
  · funext k
    cases k with
    | inl b => cases b <;> rfl
    | inr p => obtain ⟨i, b⟩ := p; cases i with
      | inl c => cases c <;> cases b <;> rfl
      | inr i => cases b <;> rfl

theorem init_run (M : TM n) (w : List Bool) :
    Run (machine M).step (2 * w.length + 2) (initList (machine M) w)
      (config (some Label.simulate) (initialCache M) (fun _ ↦ []) (initialTapes w) false) := by
  have h := (read_run M Γ.start false w [] []).trans
    (reverse_run M (Γ.ofBool false) false (w.reverse.map Γ.ofBool ++ []) [])
  rw [init_buffer]
  simpa only [List.append_nil, List.length_map, List.length_reverse, List.map_reverse,
    List.reverse_reverse, buffer_initial_tapes, show w.length + 1 + (w.length + 1) =
      2 * w.length + 2 by omega] using h

theorem simulate_halted (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape) (b : Bool)
    (h : s.state = M.qhalt) :
    (machine M).step (config (some Label.simulate) s (fun _ ↦ []) t b) =
      some (config (some Label.rewindOutput) s (fun _ ↦ []) t b) := by
  change some (TM2.stepAux (body M Label.simulate (.goto fun _ ↦ Label.rewindOutput))
    (registers s t b) (tapeStacks (fun _ ↦ []) t)) = _
  rw [body_halted M _ _ _ _ _ _ h]
  rfl

theorem rewind_nil (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape) (b : Bool)
    (h : (t output).left = []) :
    (machine M).step (config (some Label.rewindOutput) s (fun _ ↦ []) t b) =
      some (config (some Label.copyOutput) s (fun _ ↦ []) t false) := by
  simp [FinTM2.step, machine, program, config, TM2.step, TM2.stepAux,
    registers, tapeStacks, h]

theorem rewind_cons (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape) (b : Bool)
    (h : (t output).left ≠ []) :
    (machine M).step (config (some Label.rewindOutput) s (fun _ ↦ []) t b) =
      some (config (some Label.rewindOutput) s (fun _ ↦ [])
        (Function.update t output (t output).moveLeft) true) := by
  have hd : (t output).left.head?.isSome = true := by simpa using h
  change some (TM2.stepAux (program M .rewindOutput) (registers s t b)
    (tapeStacks (fun _ ↦ []) t)) = _
  simp only [program, TM2.stepAux, registers, tapeStacks, hd, Bool.cond_true]
  erw [left_step (fun _ ↦ []) s t true output (.goto fun _ ↦ Label.rewindOutput)]
  simp only [hd, TM2.stepAux, config]

theorem move_left_size (u : StackTape) :
    u.moveLeft.left.length + u.moveLeft.right.length = u.left.length + u.right.length := by
  cases u with
  | mk l c r => cases l <;> simp [StackTape.moveLeft] <;> omega

theorem rewind_run (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape) (b : Bool) :
    ∃ u, (u output).left = [] ∧ (u output).toTape.cells = (t output).toTape.cells ∧
      (∀ i, (u i).left.length + (u i).right.length =
        (t i).left.length + (t i).right.length) ∧
      Run (machine M).step ((t output).left.length + 1)
        (config (some Label.rewindOutput) s (fun _ ↦ []) t b)
        (config (some Label.copyOutput) s (fun _ ↦ []) u false) := by
  suffices ∀ m (t : Index n → StackTape) (b : Bool), (t output).left.length = m →
      ∃ u, (u output).left = [] ∧ (u output).toTape.cells = (t output).toTape.cells ∧
        (∀ i, (u i).left.length + (u i).right.length =
          (t i).left.length + (t i).right.length) ∧
        Run (machine M).step (m + 1)
          (config (some Label.rewindOutput) s (fun _ ↦ []) t b)
          (config (some Label.copyOutput) s (fun _ ↦ []) u false) from
    this _ t b rfl
  intro m
  induction m with
  | zero =>
    intro t b h
    have he : (t output).left = [] := List.length_eq_zero_iff.mp h
    exact ⟨t, he, rfl, fun _ ↦ rfl, .one (rewind_nil M s t b he)⟩
  | succ m ih =>
    intro t b h
    have hn : (t output).left ≠ [] := by intro he; simp [he] at h
    let t' := Function.update t output (t output).moveLeft
    have hlen : (t' output).left.length = m := by
      simp only [t', Function.update_self]
      cases he : (t output).left with
      | nil => exact False.elim (hn he)
      | cons a l => simp [StackTape.moveLeft, he] at h ⊢; omega
    obtain ⟨u, hu, hc, hs, hr⟩ := ih t' true hlen
    refine ⟨u, hu, ?_, ?_, .cons (rewind_cons M s t b hn) hr⟩
    · rw [hc]
      change (t output).moveLeft.toTape.cells = (t output).toTape.cells
      rw [StackTape.toTape_move_left]
      rfl
    · intro i
      rw [hs]
      by_cases hi : i = output
      · subst i; simp only [t', Function.update_self, move_left_size]
      · simp only [t', Function.update_of_ne hi]


def copyTapes (t : Index n → StackTape) : Index n → StackTape :=
  Function.update t output ⟨(t output).left, (t output).right.head?.getD Γ.blank,
    (t output).right.tail⟩

def inputBuffer (w : List Bool) : Bool → List Bool := fun b ↦ if b then [] else w
def outputBuffer (w : List Bool) : Bool → List Bool := fun b ↦ if b then w else []

theorem copy_size (t : Index n → StackTape) (i : Index n) :
    (copyTapes t i).left.length + (copyTapes t i).right.length ≤
      (t i).left.length + (t i).right.length := by
  by_cases hi : i = output
  · subst i; simp [copyTapes]
  · simp [copyTapes, Function.update_of_ne hi]

theorem copy_bit (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape)
    (b a : Bool) (w : List Bool) (ha : (t output).right.head?.getD Γ.blank = Γ.ofBool a) :
    (machine M).step (config (some Label.copyOutput) s (inputBuffer w) t b) =
      some (config (some Label.copyOutput) s (inputBuffer (a :: w)) (copyTapes t) b) := by
  change some (TM2.stepAux (program M .copyOutput) (registers s t b)
    (tapeStacks (inputBuffer w) t)) = _
  simp only [program, TM2.stepAux, registers, tapeStacks, ha, Function.update_self]
  have hab : (decide (Γ.ofBool a = Γ.zero ∨ Γ.ofBool a = Γ.one)) = true := by cases a <;> decide
  have hae : (decide (Γ.ofBool a = Γ.one)) = a := by cases a <;> rfl
  simp only [hab, Bool.cond_true, hae]
  congr 1
  apply cfg_ext
  · rfl
  · simp only [config, registers, copyTapes, heads_update, ha]
  · funext k
    cases k with
    | inl c => cases c <;> simp [config, tapeStacks, inputBuffer, copyTapes]
    | inr p =>
      obtain ⟨i, c⟩ := p
      by_cases hi : i = output
      · subst i; cases c <;> simp [config, tapeStacks, copyTapes]
      · cases c <;> simp [config, tapeStacks, copyTapes, Function.update_of_ne hi,
          Function.update, hi]

theorem copy_blank (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape)
    (b : Bool) (w : List Bool) (ha : (t output).right.head?.getD Γ.blank = Γ.blank) :
    (machine M).step (config (some Label.copyOutput) s (inputBuffer w) t b) =
      some (config (some Label.reverseOutput) s (inputBuffer w) (copyTapes t) b) := by
  change some (TM2.stepAux (program M .copyOutput) (registers s t b)
    (tapeStacks (inputBuffer w) t)) = _
  simp only [program, TM2.stepAux, registers, tapeStacks, ha, Function.update_self]
  simp only [reduceCtorEq, or_self, decide_false, Bool.cond_false]
  congr 1
  apply cfg_ext
  · rfl
  · simp only [config, registers, copyTapes, heads_update, ha]
  · funext k
    cases k with
    | inl c => simp [config, tapeStacks]
    | inr p =>
      obtain ⟨i, c⟩ := p
      by_cases hi : i = output
      · subst i; cases c <;> simp [config, tapeStacks, copyTapes]
      · cases c <;> simp [config, tapeStacks, copyTapes, Function.update_of_ne hi,
          Function.update, hi]

inductive OutputPrefix : List Γ → List Bool → Prop
  | nil (l : List Γ) : l.head?.getD Γ.blank = Γ.blank → OutputPrefix l []
  | cons (l : List Γ) (a : Bool) (w : List Bool) :
      l.head?.getD Γ.blank = Γ.ofBool a → OutputPrefix l.tail w → OutputPrefix l (a :: w)

theorem outputPrefix_length {l : List Γ} {w : List Bool} (h : OutputPrefix l w) :
    w.length ≤ l.length := by
  induction h with
  | nil => simp
  | cons l a w hh ht ih =>
    have hl : l ≠ [] := by intro he; subst he; cases a <;> cases hh
    have hp := List.length_pos_iff.mpr hl
    simp only [List.length_tail, List.length_cons] at *
    omega

theorem outputPrefix_of_getElem (l : List Γ) (w : List Bool)
    (h : ∀ i (hi : i < w.length), (l[i]?).getD Γ.blank = Γ.ofBool (w[i]'hi))
    (hb : (l[w.length]?).getD Γ.blank = Γ.blank) : OutputPrefix l w := by
  induction w generalizing l with
  | nil => exact .nil l (by simpa only [List.length_nil, List.head?_eq_getElem?] using hb)
  | cons a w ih =>
    refine .cons l a w ?_ (ih l.tail ?_ ?_)
    · rw [List.head?_eq_getElem?]
      exact h 0 (by simp)
    · intro i hi
      rw [List.getElem?_tail]
      exact h (i + 1) (by simpa using hi)
    · simpa only [List.getElem?_tail, List.length_cons] using hb

theorem copy_run (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape)
    (b : Bool) (w y : List Bool) (hy : OutputPrefix (t output).right y) :
    ∃ u, (∀ i, (u i).left.length + (u i).right.length ≤
      (t i).left.length + (t i).right.length) ∧
      Run (machine M).step (y.length + 1)
        (config (some Label.copyOutput) s (inputBuffer w) t b)
        (config (some Label.reverseOutput) s (inputBuffer (y.reverse ++ w)) u b) := by
  induction y generalizing t w with
  | nil =>
    cases hy with
    | nil _ hh => exact ⟨copyTapes t, copy_size t, .one (copy_blank M s t b w hh)⟩
  | cons a y ih =>
    cases hy with
    | cons _ _ _ hh ht =>
      obtain ⟨u, hu, hr⟩ := ih (copyTapes t) (a :: w) (by simpa [copyTapes] using ht)
      refine ⟨u, fun i ↦ (hu i).trans (copy_size t i), ?_⟩
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
        using Run.cons (copy_bit M s t b a w hh) hr

def reverseIO (w y : List Bool) : Bool → List Bool := fun b ↦ if b then y else w

theorem reverse_output_cons (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape)
    (b a : Bool) (w y : List Bool) :
    (machine M).step (config (some Label.reverseOutput) s (reverseIO (a :: w) y) t b) =
      some (config (some Label.reverseOutput) {s with verdict := a} (reverseIO w (a :: y)) t true) := by
  simp only [FinTM2.step, machine, program, config, TM2.step, TM2.stepAux,
    registers, tapeStacks, reverseIO, Bool.false_eq_true, if_false,
    List.head?_cons, Option.getD_some, Option.isSome_some, Bool.cond_true, List.tail_cons]
  congr 2
  funext k
  cases k with
  | inl c => cases c <;> simp [tapeStacks, reverseIO]
  | inr p => obtain ⟨i, c⟩ := p; cases c <;> rfl

theorem reverse_output_nil (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape)
    (b : Bool) (y : List Bool) :
    (machine M).step (config (some Label.reverseOutput) s (reverseIO [] y) t b) =
      some (config (some Label.clear) {s with verdict := false} (outputBuffer y) t false) := by
  simp only [FinTM2.step, machine, program, config, TM2.step, TM2.stepAux,
    registers, tapeStacks, reverseIO, Bool.false_eq_true, if_false,
    List.head?_nil, Option.getD_none, Option.isSome_none, Bool.cond_false, List.tail_nil]
  congr 2
  funext k
  cases k with
  | inl c => cases c <;> simp [tapeStacks, outputBuffer, reverseIO]
  | inr p => obtain ⟨i, c⟩ := p; cases c <;> rfl

theorem reverse_output_run (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape)
    (b : Bool) (w y : List Bool) :
    Run (machine M).step (w.length + 1)
      (config (some Label.reverseOutput) s (reverseIO w y) t b)
      (config (some Label.clear) {s with verdict := false} (outputBuffer (w.reverse ++ y)) t false) := by
  induction w generalizing s b y with
  | nil => exact .one (reverse_output_nil M s t b y)
  | cons a w ih =>
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
      using Run.cons (reverse_output_cons M s t b a w y) (ih {s with verdict := a} true (a :: y))

theorem clear_live (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape) (b : Bool)
    (y : List Bool) (h : allDirty t = true) :
    (machine M).step (config (some Label.clear) s (outputBuffer y) t b) =
      some (config (some Label.clear) s (outputBuffer y) (fun i ↦ thin (t i)) true) := by
  change some (TM2.stepAux (program M .clear) (registers s t b) (tapeStacks (outputBuffer y) t)) = _
  unfold program
  simp only [TM2.stepAux, registers]
  erw [clear_all_step (outputBuffer y) s t false]
  simp [registers, h, TM2.stepAux, config]

theorem clear_done (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape) (b : Bool)
    (y : List Bool) (h : allDirty t = false) :
    (machine M).step (config (some Label.clear) s (outputBuffer y) t b) =
      some (haltList (machine M) y) := by
  have he := (all_dirty_eq_false t).mp h
  change some (TM2.stepAux (program M .clear) (registers s t b) (tapeStacks (outputBuffer y) t)) = _
  unfold program
  simp only [TM2.stepAux, registers]
  erw [clear_all_step (outputBuffer y) s t false]
  simp only [registers, h, Bool.false_or, Bool.cond_false, TM2.stepAux]
  congr 1
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl c => cases c <;> simp [haltList, machine, tapeStacks, outputBuffer]
    | inr p =>
      obtain ⟨i, c⟩ := p
      cases c <;> simp [haltList, machine, tapeStacks, thin, (he i).1, (he i).2]

theorem clear_run (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape) (b : Bool)
    (y : List Bool) (B : ℕ) (hB : ∀ i, (t i).left.length ≤ B ∧ (t i).right.length ≤ B) :
    Within (machine M).step (B + 1)
      (config (some Label.clear) s (outputBuffer y) t b) (haltList (machine M) y) := by
  induction B generalizing t b with
  | zero =>
    apply Within.one
    apply clear_done
    rw [all_dirty_eq_false]
    intro i
    simpa only [Nat.le_zero, List.length_eq_zero_iff] using hB i
  | succ B ih =>
    cases hd : allDirty t
    · exact (Within.one (clear_done M s t b y hd)).mono (by omega)
    · have hs := Within.one (clear_live M s t b y hd)
      have ht := ih (fun i ↦ thin (t i)) true (by
        intro i
        have hi := hB i
        simp only [thin, List.length_tail]
        omega)
      simpa only [Nat.add_comm 1] using hs.trans ht

theorem initial_size (x : List Bool) (i : Index n) :
    (initialTapes x i).left.length + (initialTapes x i).right.length ≤ x.length := by
  cases i with
  | inl b => cases b <;> simp [initialTapes, StackTape.init]
  | inr i => simp [initialTapes, StackTape.init]

theorem computer_run (M : TM n) {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hM : M.ComputesInTime f T) (x : List Bool) :
    Within (machine M).step (8 * (x.length + T x.length + 1))
      (initList (machine M) x) (haltList (machine M) (f x)) := by
  obtain ⟨c, m, hm, hr, hhalt, hout⟩ := hM x
  obtain ⟨s, t, b, he, hsize, hrun⟩ := MultitapeCore.run M Label.simulate
    (.goto fun _ ↦ Label.rewindOutput) (program M) rfl hr
      (initialCache M) (fun _ ↦ []) (initialTapes x) false (initial_cfg M x)
  have hb : ∀ i, (t i).left.length + (t i).right.length ≤ x.length + m := by
    intro i
    exact (hsize i).trans (Nat.add_le_add_right (initial_size x i) m)
  have hh : s.state = M.qhalt := (congrArg Cfg.state he).trans hhalt
  obtain ⟨u, hu, hc, hs, hrewind⟩ := rewind_run M s t b
  have ho : (u output).toTape.HasOutput (f x) := by
    apply (Tape.hasOutput_congr (hc.trans (congrArg (fun d ↦ d.output.cells) he)) (f x)).mpr
    exact hout
  have hp : OutputPrefix (u output).right (f x) := by
    apply outputPrefix_of_getElem
    · intro i hi
      simpa [StackTape.toTape, StackTape.contents, hu] using ho.1 i hi
    · simpa [StackTape.toTape, StackTape.contents, hu] using ho.2
  have hlen := outputPrefix_length hp
  obtain ⟨v, hv, hcopy⟩ := copy_run M s u false [] (f x) hp
  have hin : inputBuffer ([] : List Bool) = fun _ ↦ [] := by funext b; cases b <;> rfl
  simp only [hin, List.append_nil] at hcopy
  have hrev := reverse_output_run M s v false (f x).reverse []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hrev
  have hclean := clear_run M {s with verdict := false} v false (f x) (x.length + m) (by
    intro i
    have h₁ := hv i
    have h₂ := hs i
    have h₃ := hb i
    omega)
  have hprefix := ((((init_run M x).trans hrun).trans (.one (simulate_halted M s t b hh))).trans hrewind).trans hcopy
  have hwhole := (show Within (machine M).step _ _ _ from
    ⟨_, le_rfl, hprefix.trans hrev⟩).trans hclean
  apply hwhole.mono
  have h₁ := hs output
  have h₂ := hb output
  omega

theorem computer_polytime (M : TM n) {f : List Bool → List Bool} {T : ℕ → ℕ} {d : ℕ}
    (hM : M.ComputesInTime f T) (hT : T =O (· ^ d)) :
    Nonempty (TM2ComputableInPolyTime id id f) := by
  obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hT
  refine ⟨{
    tm := machine M
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.C 8 * (Polynomial.X + p + 1)
    outputsFun := ?_
  }⟩
  intro x
  have h := (computer_run M hM x).mono (show 8 * (x.length + T x.length + 1) ≤
      (Polynomial.C 8 * (Polynomial.X + p + 1)).eval x.length by
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    exact Nat.mul_le_mul_left 8 (Nat.add_le_add_right (Nat.add_le_add_left (hp _) _) _))
  simpa only [TM2OutputsInTime, Equiv.refl, List.map_id, id_eq, Option.map_some] using h.evals

end Lax323828Proofs.RegisteredBridge.MultitapeTransducer

namespace Lax323828Proofs.RegisteredBridge

open PCPFoundation.Complexity Turing

theorem FP_registered_computer {f : List Bool → List Bool} (hf : f ∈ FP) :
    Nonempty (TM2ComputableInPolyTime id id f) := by
  obtain ⟨d, n, M, T, hM, hT⟩ := hf
  exact MultitapeTransducer.computer_polytime M hM hT

end Lax323828Proofs.RegisteredBridge
