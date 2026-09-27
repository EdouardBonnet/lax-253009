import Lax253009Proofs.RegisteredBridge.Time
import Mathlib.Computability.TuringMachine.StackTuringMachine

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax253009Proofs.RegisteredBridge.StackSubroutine

open Turing Time Function

/-- A finite-register subroutine reads and updates one component of the
enclosing control register, preserving all other components. -/
structure Lens (S T : Type) where
  get : T → S
  put : T → S → T
  get_put : ∀ t s, get (put t s) = s
  put_get : ∀ t, put t (get t) = t
  put_put : ∀ t s u, put (put t s) u = put t u

def Lens.fst (S T : Type) : Lens S (S × T) where
  get := Prod.fst
  put t s := (s, t.2)
  get_put _ _ := rfl
  put_get _ := rfl
  put_put _ _ _ := rfl

def Lens.snd (S T : Type) : Lens T (S × T) where
  get := Prod.snd
  put t s := (t.1, s)
  get_put _ _ := rfl
  put_get _ := rfl
  put_put _ _ _ := rfl

def Lens.comp {S T U : Type} (a : Lens S T) (b : Lens T U) : Lens S U where
  get u := a.get (b.get u)
  put u s := b.put u (a.put (b.get u) s)
  get_put u s := by rw [b.get_put, a.get_put]
  put_get u := by rw [a.put_get, b.put_get]
  put_put u s t := by rw [b.get_put, b.put_put, a.put_put]

variable {K J Λ Λ' σ τ : Type} {Γ : K → Type} {Δ : J → Type}
variable [DecidableEq K] [DecidableEq J]

abbrev Alphabet (Γ : K → Type) (Δ : J → Type) : K ⊕ J → Type := Sum.elim Γ Δ

def joinedStacks (S : ∀ k, List (Γ k)) (T : ∀ j, List (Δ j)) : ∀ i, List (Alphabet Γ Δ i) :=
  Sum.rec S T

theorem update_left (S : ∀ k, List (Γ k)) (T : ∀ j, List (Δ j)) (k : K) (l : List (Γ k)) :
    update (joinedStacks S T) (.inl k) l = joinedStacks (update S k l) T := by
  funext i
  cases i with
  | inl i =>
    by_cases hi : i = k
    · subst i; simp [joinedStacks]
    · simp [joinedStacks, update_of_ne hi, update, hi]
  | inr j => simp [joinedStacks, update]

def lift (v : Lens σ τ) (label : Λ → Λ') (exit : Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt (Alphabet Γ Δ) Λ' τ
  | .push k f q => .push (.inl k) (fun t ↦ f (v.get t)) (lift v label exit q)
  | .peek k f q => .peek (.inl k) (fun t a ↦ v.put t (f (v.get t) a)) (lift v label exit q)
  | .pop k f q => .pop (.inl k) (fun t a ↦ v.put t (f (v.get t) a)) (lift v label exit q)
  | .load f q => .load (fun t ↦ v.put t (f (v.get t))) (lift v label exit q)
  | .branch f q r => .branch (fun t ↦ f (v.get t)) (lift v label exit q) (lift v label exit r)
  | .goto f => .goto (fun t ↦ label (f (v.get t)))
  | .halt => .goto (fun _ ↦ exit)

def config (v : Lens σ τ) (label : Λ → Λ') (exit : Λ') (t : τ) (T : ∀ j, List (Δ j))
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg (Alphabet Γ Δ) Λ' τ :=
  ⟨some ((c.l.map label).getD exit), v.put t c.var, joinedStacks c.stk T⟩

theorem block (v : Lens σ τ) (label : Λ → Λ') (exit : Λ')
    (q : TM2.Stmt Γ Λ σ) (t : τ) (S : ∀ k, List (Γ k)) (T : ∀ j, List (Δ j)) :
    TM2.stepAux (lift v label exit q) t (joinedStacks S T) =
      config v label exit t T (TM2.stepAux q (v.get t) S) := by
  induction q generalizing t S with
  | push k f q ih =>
    simp only [lift, TM2.stepAux, update_left]
    exact ih _ _
  | peek k f q ih =>
    simp only [lift, TM2.stepAux, joinedStacks]
    rw [ih]
    simp only [v.get_put, config, v.put_put]
  | pop k f q ih =>
    simp only [lift, TM2.stepAux]
    rw [update_left, ih]
    simp only [joinedStacks, v.get_put, config, v.put_put]
  | load f q ih =>
    simp only [lift, TM2.stepAux]
    rw [ih]
    simp only [v.get_put, config, v.put_put]
  | branch f q r ihq ihr =>
    cases hf : f (v.get t)
    · simpa only [lift, TM2.stepAux, hf, Bool.cond_false] using ihr t S
    · simpa only [lift, TM2.stepAux, hf, Bool.cond_true] using ihq t S
  | goto f => simp [lift, TM2.stepAux, config, v.put_get]
  | halt => simp [lift, TM2.stepAux, config, v.put_get]

theorem run (v : Lens σ τ) (label : Λ → Λ') (exit : Λ')
    (M : Λ → TM2.Stmt Γ Λ σ) (N : Λ' → TM2.Stmt (Alphabet Γ Δ) Λ' τ)
    (hN : ∀ l, N (label l) = lift v label exit (M l))
    (t : τ) (T : ∀ j, List (Δ j)) {n : ℕ} {a b : TM2.Cfg Γ Λ σ}
    (h : Run (TM2.step M) n a b) :
    Run (TM2.step N) n (config v label exit t T a) (config v label exit t T b) := by
  apply h.map (config v label exit t T)
  intro a b hs
  rcases a with ⟨l, s, S⟩
  cases l with
  | none => simp [TM2.step] at hs
  | some l =>
    have hb : b = TM2.stepAux (M l) s S := by simpa [TM2.step] using hs.symm
    rw [hb]
    simp only [config, Option.map_some, Option.getD_some, TM2.step, hN]
    rw [block]
    simp only [v.get_put, config, v.put_put]


theorem update_right (S : ∀ k, List (Γ k)) (T : ∀ j, List (Δ j)) (k : K) (l : List (Γ k)) :
    update (joinedStacks T S) (.inr k) l = joinedStacks T (update S k l) := by
  funext i
  cases i with
  | inl j => simp [joinedStacks, update]
  | inr i =>
    by_cases hi : i = k
    · subst i; simp [joinedStacks]
    · simp [joinedStacks, update, hi]

def liftRight (v : Lens σ τ) (label : Λ → Λ') (exit : Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt (Alphabet Δ Γ) Λ' τ
  | .push k f q => .push (.inr k) (fun t ↦ f (v.get t)) (liftRight v label exit q)
  | .peek k f q => .peek (.inr k) (fun t a ↦ v.put t (f (v.get t) a)) (liftRight v label exit q)
  | .pop k f q => .pop (.inr k) (fun t a ↦ v.put t (f (v.get t) a)) (liftRight v label exit q)
  | .load f q => .load (fun t ↦ v.put t (f (v.get t))) (liftRight v label exit q)
  | .branch f q r => .branch (fun t ↦ f (v.get t)) (liftRight v label exit q) (liftRight v label exit r)
  | .goto f => .goto (fun t ↦ label (f (v.get t)))
  | .halt => .goto (fun _ ↦ exit)

def configRight (v : Lens σ τ) (label : Λ → Λ') (exit : Λ') (t : τ) (T : ∀ j, List (Δ j))
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg (Alphabet Δ Γ) Λ' τ :=
  ⟨some ((c.l.map label).getD exit), v.put t c.var, joinedStacks T c.stk⟩

theorem blockRight (v : Lens σ τ) (label : Λ → Λ') (exit : Λ')
    (q : TM2.Stmt Γ Λ σ) (t : τ) (S : ∀ k, List (Γ k)) (T : ∀ j, List (Δ j)) :
    TM2.stepAux (liftRight v label exit q) t (joinedStacks T S) =
      configRight v label exit t T (TM2.stepAux q (v.get t) S) := by
  induction q generalizing t S with
  | push k f q ih =>
    simp only [liftRight, TM2.stepAux, update_right]
    exact ih _ _
  | peek k f q ih =>
    simp only [liftRight, TM2.stepAux, joinedStacks]
    rw [ih]
    simp only [v.get_put, configRight, v.put_put]
  | pop k f q ih =>
    simp only [liftRight, TM2.stepAux]
    rw [update_right, ih]
    simp only [joinedStacks, v.get_put, configRight, v.put_put]
  | load f q ih =>
    simp only [liftRight, TM2.stepAux]
    rw [ih]
    simp only [v.get_put, configRight, v.put_put]
  | branch f q r ihq ihr =>
    cases hf : f (v.get t)
    · simpa only [liftRight, TM2.stepAux, hf, Bool.cond_false] using ihr t S
    · simpa only [liftRight, TM2.stepAux, hf, Bool.cond_true] using ihq t S
  | goto f => simp [liftRight, TM2.stepAux, configRight, v.put_get]
  | halt => simp [liftRight, TM2.stepAux, configRight, v.put_get]

theorem runRight (v : Lens σ τ) (label : Λ → Λ') (exit : Λ')
    (M : Λ → TM2.Stmt Γ Λ σ) (N : Λ' → TM2.Stmt (Alphabet Δ Γ) Λ' τ)
    (hN : ∀ l, N (label l) = liftRight v label exit (M l))
    (t : τ) (T : ∀ j, List (Δ j)) {n : ℕ} {a b : TM2.Cfg Γ Λ σ}
    (h : Run (TM2.step M) n a b) :
    Run (TM2.step N) n (configRight v label exit t T a) (configRight v label exit t T b) := by
  apply h.map (configRight v label exit t T)
  intro a b hs
  rcases a with ⟨l, s, S⟩
  cases l with
  | none => simp [TM2.step] at hs
  | some l =>
    have hb : b = TM2.stepAux (M l) s S := by simpa [TM2.step] using hs.symm
    rw [hb]
    simp only [configRight, Option.map_some, Option.getD_some, TM2.step, hN]
    rw [blockRight]
    simp only [v.get_put, configRight, v.put_put]

end Lax253009Proofs.RegisteredBridge.StackSubroutine
