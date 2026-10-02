import Lax323828Proofs.RegisteredBridge.Time
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax323828Proofs.RegisteredBridge.StackToTapeTime

open Turing Time Function TM2to1 TM2to1.Λ'

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

/-- The greatest number of stack operations along a branch of one block. -/
def stackOps : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q | .peek _ _ q | .pop _ _ q => stackOps q + 1
  | .load _ q => stackOps q
  | .branch _ p q => max (stackOps p) (stackOps q)
  | .goto _ | .halt => 0

theorem stackOps_run {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    stackOps (stRun o q) = stackOps q + 1 := by cases o <;> rfl

theorem stWrite_length {k : K} (o : StAct K Γ σ k) (v : σ) (S : ∀ k, List (Γ k)) (j : K) :
    ((update S k (stWrite v (S k) o)) j).length ≤ (S j).length + 1 := by
  by_cases h : j = k
  · subst j; cases o <;> simp [stWrite] <;> omega
  · simp [update_of_ne h]

variable (M : Λ → TM2.Stmt Γ Λ σ)

theorem go_run {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    {S : List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse)
    (n : ℕ) (hn : n ≤ S.length) :
    Run (TM1.step (tr M)) n ⟨some (go k o q), v, Tape.mk' ∅ (addBottom L)⟩
      ⟨some (go k o q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => exact .zero _
  | succ n ih =>
    have h := ih (by omega)
    have hs : TM1.step (tr M)
        ⟨some (go k o q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ =
      some ⟨some (go k o q), v, (Tape.move Dir.right)^[n + 1] (Tape.mk' ∅ (addBottom L))⟩ := by
      rw [iterate_succ_apply']
      simp only [TM1.step, TM1.stepAux, tr, Tape.mk'_nth_nat, Tape.move_right_n_head,
        addBottom_nth_snd]
      rw [stk_nth_val _ hL, List.getElem?_eq_getElem]
      · rfl
      · simpa only [List.length_reverse] using (show n < S.length by omega)
    exact h.trans (.one hs)

theorem ret_run (q : TM2.Stmt Γ Λ σ) (v : σ)
    (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    Run (TM1.step (tr M)) n
      ⟨some (ret q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      ⟨some (ret q), v, Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => exact .zero _
  | succ n ih =>
    refine .cons ?_ ih
    simp only [TM1.step]
    rw [Option.some_inj, tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat,
      addBottom_nth_succ_fst, TM1.stepAux, iterate_succ', Function.comp_apply, Tape.move_right_left]
    rfl

theorem block (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k))
    (L : ListBlank (∀ k, Option (Γ k)))
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse)
    (B : ℕ) (hB : ∀ k, (S k).length + stackOps q ≤ B) :
    ∃ b, TrCfg (TM2.stepAux q v S) b ∧
      Within (TM1.step (tr M)) (stackOps q * (2 * B + 2))
        (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L))) b := by
  induction q using stmtStRec generalizing v S L with
  | run k o q ih =>
    simp only [stackOps_run] at hB ⊢
    let S' := update S k (stWrite v (S k) o)
    let v' := stVar v (S k) o
    obtain ⟨L', hL', hact⟩ := tr_respects_aux₂ (q := TM1.Stmt.goto fun _ _ ↦ ret q) hL o
    have hb' : ∀ j, (S' j).length + stackOps q ≤ B := by
      intro j
      have h := stWrite_length o v S j
      have hj := hB j
      dsimp only [S']
      omega
    obtain ⟨b, hcfg, htail⟩ := ih v' S' L' hL' hb'
    refine ⟨b, ?_, ?_⟩
    · simpa only [step_run, v', S'] using hcfg
    · have hgo := go_run M o q v (hL k) (S k).length le_rfl
      have hs : TM1.step (tr M)
          ⟨some (go k o q), v, (Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩ =
        some ⟨some (ret q), v', (Tape.move Dir.right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
        simp only [TM1.step, tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat,
          addBottom_nth_snd]
        rw [stk_nth_val _ (hL k), List.getElem?_eq_none (le_of_eq List.length_reverse)]
        simp only [Option.isNone, Bool.cond_true, hact, TM1.stepAux]
        rfl
      have hret := ret_run M q v' L' (S' k).length
      have hend : TM1.step (tr M) ⟨some (ret q), v', Tape.mk' ∅ (addBottom L')⟩ =
        some (TM1.stepAux (trNormal q) v' (Tape.mk' ∅ (addBottom L'))) := by
        simp [TM1.step, tr, TM1.stepAux, Tape.mk'_head, addBottom_head_fst]
      have hh := ((hgo.trans (.one hs)).trans hret).trans (.one hend)
      have hwhole := (show Within (TM1.step (tr M)) _ _ _ from ⟨_, le_rfl, hh⟩).trans htail
      simp only [trNormal_run, TM1.stepAux]
      apply hwhole.mono
      have hk := hB k
      have hk' := hb' k
      rw [Nat.add_mul]
      omega
  | load a q ih => exact ih (a v) S L hL hB
  | branch p q₁ q₂ ih₁ ih₂ =>
    simp only [stackOps] at hB ⊢
    cases hp : p v
    · obtain ⟨b, hcfg, hr⟩ := ih₂ v S L hL (fun k ↦ by have h := hB k; omega)
      refine ⟨b, ?_, ?_⟩
      · simpa only [TM2.stepAux, hp, Bool.cond_false] using hcfg
      · simpa only [trNormal, TM1.stepAux, hp, Bool.cond_false] using
          hr.mono (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))
    · obtain ⟨b, hcfg, hr⟩ := ih₁ v S L hL (fun k ↦ by have h := hB k; omega)
      refine ⟨b, ?_, ?_⟩
      · simpa only [TM2.stepAux, hp, Bool.cond_true] using hcfg
      · simpa only [trNormal, TM1.stepAux, hp, Bool.cond_true] using
          hr.mono (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
  | goto l =>
    refine ⟨_, .mk L hL, ?_⟩
    simp only [stackOps, Nat.zero_mul]
    exact Within.refl _
  | halt =>
    refine ⟨_, .mk L hL, ?_⟩
    simp only [stackOps, Nat.zero_mul]
    exact Within.refl _

theorem stepAux_length (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (j : K) :
    ((TM2.stepAux q v S).stk j).length ≤ (S j).length + stackOps q := by
  induction q using stmtStRec generalizing v S with
  | run k o q ih =>
    rw [step_run, stackOps_run]
    have h := ih (stVar v (S k) o) (update S k (stWrite v (S k) o))
    have h' := stWrite_length o v S j
    omega
  | load a q ih => exact ih _ _
  | branch p q₁ q₂ ih₁ ih₂ =>
    cases hp : p v
    · simpa only [TM2.stepAux, hp, Bool.cond_false, stackOps] using
        (ih₂ v S).trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
    · simpa only [TM2.stepAux, hp, Bool.cond_true, stackOps] using
        (ih₁ v S).trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  | goto l => simp [TM2.stepAux, stackOps]
  | halt => simp [TM2.stepAux, stackOps]

open scoped BigOperators

variable [Fintype Λ]

noncomputable def machineOps : ℕ := ∑ l, stackOps (M l)

theorem stackOps_le (l : Λ) : stackOps (M l) ≤ machineOps M :=
  Finset.single_le_sum (f := fun j ↦ stackOps (M j))
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ l)

/-- A source run, including its accumulated stack growth, admits a single-tape
run of at most quadratic length. This version reserves all required tape
space in `B`, so the same per-step cost works throughout the induction. -/
theorem run (B : ℕ) {n : ℕ} {a b : TM2.Cfg Γ Λ σ}
    (h : Run (TM2.step M) n a b) {a' : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ}
    (ha' : TrCfg a a') (hB : ∀ k, (a.stk k).length + machineOps M * n ≤ B) :
    ∃ b', TrCfg b b' ∧
      Within (TM1.step (tr M)) (n * (1 + machineOps M * (2 * B + 2))) a' b' := by
  induction h generalizing a' with
  | zero => exact ⟨a', ha', (Within.refl _).mono (by simp)⟩
  | @cons n a b c hs h ih =>
    cases ha' with
    | @mk l v S L hL =>
      cases l with
      | none => simp [TM2.step] at hs
      | some l =>
        have hb : b = TM2.stepAux (M l) v S := by simpa [TM2.step] using hs.symm
        have hslot := stackOps_le M l
        have hbound : ∀ k, (S k).length + stackOps (M l) ≤ B := by
          intro k
          have hk := hB k
          simp only [Nat.mul_succ] at hk
          omega
        obtain ⟨d, hd, hblock⟩ := block M (M l) v S L hL B hbound
        have hbound' : ∀ k, (b.stk k).length + machineOps M * n ≤ B := by
          intro k
          rw [hb]
          have hg := stepAux_length (M l) v S k
          have hk := hB k
          simp only [Nat.mul_succ] at hk
          omega
        obtain ⟨b', hb', hrest⟩ := ih (hb ▸ hd) hbound'
        refine ⟨b', hb', ?_⟩
        have hfirst : Within (TM1.step (tr M)) 1
            ⟨some (normal l), v, Tape.mk' ∅ (addBottom L)⟩
            (TM1.stepAux (trNormal (M l)) v (Tape.mk' ∅ (addBottom L))) := .one rfl
        have hprefix := (hfirst.trans hblock).mono
          (Nat.add_le_add_left (Nat.mul_le_mul_right _ hslot) 1)
        exact (hprefix.trans hrest).mono (by simp [Nat.add_mul, Nat.add_comm])

theorem run_quadratic (B : ℕ) {n : ℕ} {a b : TM2.Cfg Γ Λ σ}
    (h : Run (TM2.step M) n a b) {a' : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ}
    (ha' : TrCfg a a') (hB : ∀ k, (a.stk k).length ≤ B) :
    ∃ b', TrCfg b b' ∧
      Within (TM1.step (tr M))
        (n * (1 + machineOps M * (2 * (B + machineOps M * n) + 2))) a' b' :=
  run M _ h ha' (fun k ↦ Nat.add_le_add_right (hB k) _)

end Lax323828Proofs.RegisteredBridge.StackToTapeTime
