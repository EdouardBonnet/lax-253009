import Lax323828Proofs.RegisteredBridge.MultitapeCore
import Lax323828Proofs.RegisteredBridge.StackTapeClear

set_option backward.isDefEq.respectTransparency false

namespace Lax323828Proofs.RegisteredBridge.MultitapeMachine

open PCPFoundation.Complexity Turing StackTapeMachine MultitapeCore Time


theorem cfg_ext {K Λ σ : Type} {A : K → Type} {c d : TM2.Cfg A Λ σ}
    (hl : c.l = d.l) (hv : c.var = d.var) (hs : c.stk = d.stk) : c = d := by
  cases c
  cases d
  cases hl
  cases hv
  cases hs
  rfl

inductive Label | readInput | reverseInput | simulate | rewindOutput | readVerdict | clear
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
        (left output (.goto fun _ ↦ .rewindOutput)) (.goto fun _ ↦ .readVerdict))
  | .readVerdict =>
    .peek (.inr (output, true)) (fun v a ↦
      ({v.1 with verdict := decide (a.getD Γ.blank = Γ.one)}, v.2.1, v.2.2))
      (.goto fun _ ↦ .clear)
  | .clear =>
    .load (fun v ↦ (v.1, v.2.1, false))
      (clearSweep Finset.univ.toList
        (.branch (fun v ↦ v.2.2) (.goto fun _ ↦ .clear)
          (.push (.inl true) (fun v ↦ v.1.verdict) (.load (fun _ ↦ initial M) .halt))))

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

end Lax323828Proofs.RegisteredBridge.MultitapeMachine
