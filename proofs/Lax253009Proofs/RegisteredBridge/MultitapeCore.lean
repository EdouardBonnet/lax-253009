import Lax253009Proofs.RegisteredBridge.StackTapeMachine
import Lax253009Proofs.RegisteredBridge.Time
import Mathlib.Tactic.DeriveFintype

set_option backward.isDefEq.respectTransparency false

namespace Lax253009Proofs.RegisteredBridge.MultitapeCore

open PCPFoundation.Complexity Turing StackTapeMachine Time

variable {Q : Type}

abbrev Index (n : ℕ) := Bool ⊕ Fin n

structure Cache (Q : Type) (n : ℕ) where
  state : Q
  symbols : Index n → Γ
  directions : Index n → Dir3
  verdict : Bool
  deriving Fintype

def initialCache {n : ℕ} (M : TM n) : Cache M.Q n :=
  ⟨M.qstart, fun _ ↦ Γ.blank, fun _ ↦ Dir3.stay, false⟩

def toCfg {n : ℕ} (s : Cache Q n) (t : Index n → StackTape) : Cfg n Q :=
  ⟨s.state, (t (.inl false)).toTape, fun i ↦ (t (.inr i)).toTape,
    (t (.inl true)).toTape⟩

def writable {n : ℕ} : Index n → Bool
  | .inl false => false
  | _ => true

def nextCache {n : ℕ} (M : TM n) (s : Cache M.Q n) (heads : Index n → Γ) : Cache M.Q n :=
  let (q, a, o, di, dw, dout) := M.δ s.state (heads (.inl false))
    (fun i ↦ heads (.inr i)) (heads (.inl true))
  ⟨q, (fun | .inl false => Γ.blank | .inl true => o.toΓ | .inr i => (a i).toΓ),
    (fun | .inl false => di | .inl true => dout | .inr i => dw i), s.verdict⟩

def nextTapes {n : ℕ} (s : Cache Q n) (t : Index n → StackTape) : Index n → StackTape :=
  fun i ↦ tapeEffect writable Cache.symbols Cache.directions s i (t i)

theorem next_tapes_size {n : ℕ} (s : Cache Q n) (t : Index n → StackTape) (i : Index n) :
    (nextTapes s t i).left.length + (nextTapes s t i).right.length ≤
      (t i).left.length + (t i).right.length + 1 := by
  unfold nextTapes tapeEffect
  have h := StackTape.length_move_le
    (if writable i then (t i).write (s.symbols i) else t i) (s.directions i)
  have hw (u : StackTape) (a : Γ) :
      (u.write a).left = u.left ∧ (u.write a).right = u.right := by
    unfold StackTape.write
    split <;> exact ⟨rfl, rfl⟩
  cases hi : writable i <;> simpa only [hi, Bool.false_eq_true, if_false, if_true, (hw _ _).1, (hw _ _).2] using h

theorem next_cfg {n : ℕ} (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape)
    (h : s.state ≠ M.qhalt) :
    M.step (toCfg s t) = some (toCfg (nextCache M s (fun i ↦ (t i).current))
      (nextTapes (nextCache M s (fun i ↦ (t i).current)) t)) := by
  simp only [TM.step, toCfg, h, if_false, StackTape.read_toTape, nextCache]
  generalize M.δ s.state (t (.inl false)).current
    (fun i ↦ (t (.inr i)).current) (t (.inl true)).current = act
  obtain ⟨q, a, o, di, dw, dout⟩ := act
  congr 1
  apply Cfg.ext
  · rfl
  · simp [nextTapes, tapeEffect, writable, StackTape.toTape_move]
  · funext i
    simp [nextTapes, tapeEffect, writable, StackTape.toTape_move, StackTape.toTape_write]
  · simp [nextTapes, tapeEffect, writable, StackTape.toTape_move, StackTape.toTape_write]

noncomputable def body {n : ℕ} {Λ : Type} (M : TM n) (loop : Λ)
    (exit : Stmt (Cache M.Q n) (Index n) Λ) : Stmt (Cache M.Q n) (Index n) Λ :=
  .branch (fun v ↦ decide (v.1.state = M.qhalt)) exit
    (.load (fun v ↦ (nextCache M v.1 v.2.1, v.2.1, v.2.2))
      (sweep writable Cache.symbols Cache.directions Finset.univ.toList (.goto fun _ ↦ loop)))

def config {n : ℕ} {Λ : Type} (l : Option Λ) (s : Cache Q n)
    (io : Bool → List Bool) (t : Index n → StackTape) (b : Bool) :
    TM2.Cfg (Alphabet (I := Index n)) Λ (Register (Cache Q n) (Index n)) :=
  ⟨l, registers s t b, tapeStacks io t⟩

theorem body_live {n : ℕ} {Λ : Type} (M : TM n) (loop : Λ)
    (exit : Stmt (Cache M.Q n) (Index n) Λ) (s : Cache M.Q n)
    (io : Bool → List Bool) (t : Index n → StackTape) (b : Bool)
    (h : s.state ≠ M.qhalt) :
    ∃ b', TM2.stepAux (body M loop exit) (registers s t b) (tapeStacks io t) =
      config (some loop) (nextCache M s (fun i ↦ (t i).current)) io
        (nextTapes (nextCache M s (fun i ↦ (t i).current)) t) b' := by
  simp only [body, TM2.stepAux, registers, h, decide_false, Bool.cond_false]
  exact sweep_all_step writable Cache.symbols Cache.directions io
    (nextCache M s (fun i ↦ (t i).current)) t b (.goto fun _ ↦ loop)

theorem body_halted {n : ℕ} {Λ : Type} (M : TM n) (loop : Λ)
    (exit : Stmt (Cache M.Q n) (Index n) Λ) (s : Cache M.Q n)
    (io : Bool → List Bool) (t : Index n → StackTape) (b : Bool)
    (h : s.state = M.qhalt) :
    TM2.stepAux (body M loop exit) (registers s t b) (tapeStacks io t) =
      TM2.stepAux exit (registers s t b) (tapeStacks io t) := by
  simp only [body, TM2.stepAux, registers, h, decide_true, Bool.cond_true]

theorem step {n : ℕ} {Λ : Type} (M : TM n) (loop : Λ)
    (exit : Stmt (Cache M.Q n) (Index n) Λ)
    (code : Λ → Stmt (Cache M.Q n) (Index n) Λ) (hc : code loop = body M loop exit)
    (s : Cache M.Q n) (io : Bool → List Bool) (t : Index n → StackTape) (b : Bool)
    (d : Cfg n M.Q) (hd : M.step (toCfg s t) = some d) :
    ∃ s' t' b', toCfg s' t' = d ∧
      (∀ i, (t' i).left.length + (t' i).right.length ≤
        (t i).left.length + (t i).right.length + 1) ∧
      TM2.step code (config (some loop) s io t b) =
        some (config (some loop) s' io t' b') := by
  have hh : s.state ≠ M.qhalt := by
    intro h; simp [TM.step, toCfg, h] at hd
  let s' := nextCache M s (fun i ↦ (t i).current)
  let t' := nextTapes s' t
  obtain ⟨b', hb⟩ := body_live M loop exit s io t b hh
  refine ⟨s', t', b', Option.some.inj ((next_cfg M s t hh).symm.trans hd),
    next_tapes_size s' t, ?_⟩
  simpa only [config, TM2.step, hc] using congrArg some hb

theorem run {n : ℕ} {Λ : Type} (M : TM n) (loop : Λ)
    (exit : Stmt (Cache M.Q n) (Index n) Λ)
    (code : Λ → Stmt (Cache M.Q n) (Index n) Λ) (hc : code loop = body M loop exit)
    {m : ℕ} {c d : Cfg n M.Q} (h : M.reachesIn m c d)
    (s : Cache M.Q n) (io : Bool → List Bool) (t : Index n → StackTape) (b : Bool)
    (hstart : toCfg s t = c) :
    ∃ s' t' b', toCfg s' t' = d ∧
      (∀ i, (t' i).left.length + (t' i).right.length ≤
        (t i).left.length + (t i).right.length + m) ∧
      Run (TM2.step code) m (config (some loop) s io t b)
        (config (some loop) s' io t' b') := by
  induction h generalizing s t b with
  | zero => exact ⟨s, t, b, hstart, fun _ ↦ Nat.le_refl _, .zero _⟩
  | step hs ht ih =>
    rw [← hstart] at hs
    obtain ⟨s₁, t₁, b₁, he, hlen, hstep⟩ := step M loop exit code hc s io t b _ hs
    obtain ⟨s₂, t₂, b₂, he₂, hlen₂, hrun⟩ := ih s₁ t₁ b₁ he
    refine ⟨s₂, t₂, b₂, he₂, ?_, .cons hstep hrun⟩
    intro i
    have h₁ := hlen i
    have h₂ := hlen₂ i
    omega

end Lax253009Proofs.RegisteredBridge.MultitapeCore
