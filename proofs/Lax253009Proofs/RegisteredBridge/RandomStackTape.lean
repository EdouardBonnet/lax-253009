import Lax253009Proofs.RegisteredBridge.StackToTapeTime
import Lax253009Proofs.RegisteredBridge.FairExecution

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax253009Proofs.RegisteredBridge.RandomStackTape

open Turing Function TM2to1 TM2to1.Λ' FairExecution StackToTapeTime
open scoped Classical

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]
variable (M : Bool → Λ → TM2.Stmt Γ Λ σ)

def advance (c : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ) (bit : Bool) :=
  (TM1.step (tr (M bit)) c).getD c

def sourceAdvance (c : TM2.Cfg Γ Λ σ) (bit : Bool) := (TM2.step (M bit) c).getD c

/-- Scanning to a stack's top uses no random choice. -/
theorem go_run {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    {S : List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse)
    (n : ℕ) (hn : n ≤ S.length) :
    DeterministicRun (advance M) n ⟨some (go k o q), v, Tape.mk' ∅ (addBottom L)⟩
      ⟨some (go k o q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => exact .zero _
  | succ n ih =>
    have h := ih (by omega)
    refine h.trans (.one (fun bit ↦ ?_))
    unfold advance
    have hs : TM1.step (tr (M bit))
        ⟨some (go k o q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ =
      some ⟨some (go k o q), v, (Tape.move Dir.right)^[n + 1] (Tape.mk' ∅ (addBottom L))⟩ := by
      rw [iterate_succ_apply']
      simp only [TM1.step, TM1.stepAux, tr, Tape.mk'_nth_nat, Tape.move_right_n_head,
        addBottom_nth_snd]
      rw [stk_nth_val _ hL, List.getElem?_eq_getElem]
      · rfl
      · simpa only [List.length_reverse] using (show n < S.length by omega)
    simp only [hs, Option.getD_some]

theorem ret_run (q : TM2.Stmt Γ Λ σ) (v : σ)
    (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    DeterministicRun (advance M) n
      ⟨some (ret q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      ⟨some (ret q), v, Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => exact .zero _
  | succ n ih =>
    refine .cons (fun bit ↦ ?_) ih
    unfold advance
    have hs : TM1.step (tr (M bit))
        ⟨some (ret q), v, (Tape.move Dir.right)^[n + 1] (Tape.mk' ∅ (addBottom L))⟩ =
      some ⟨some (ret q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
      simp only [TM1.step]
      rw [Option.some_inj, tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat,
        addBottom_nth_succ_fst, TM1.stepAux, iterate_succ', Function.comp_apply,
        Tape.move_right_left]
      rfl
    simp only [hs, Option.getD_some]

/-- Once a source block has been selected by its coin, all stack scans
and all remaining operations in that block are deterministic. -/
theorem block (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k))
    (L : ListBlank (∀ k, Option (Γ k)))
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse)
    (B : ℕ) (hB : ∀ k, (S k).length + stackOps q ≤ B) :
    ∃ b n, TrCfg (TM2.stepAux q v S) b ∧ n ≤ stackOps q * (2 * B + 2) ∧
      DeterministicRun (advance M) n
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
    obtain ⟨b, n, hcfg, hn, htail⟩ := ih v' S' L' hL' hb'
    have hgo := go_run M o q v (hL k) (S k).length le_rfl
    have hs : ∀ bit, advance M
        ⟨some (go k o q), v, (Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩ bit =
        ⟨some (ret q), v', (Tape.move Dir.right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
      intro bit
      unfold advance
      have he : TM1.step (tr (M bit))
          ⟨some (go k o q), v, (Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩ =
          some ⟨some (ret q), v', (Tape.move Dir.right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
        simp only [TM1.step, tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat,
          addBottom_nth_snd]
        rw [stk_nth_val _ (hL k), List.getElem?_eq_none (le_of_eq List.length_reverse)]
        simp only [Option.isNone, Bool.cond_true, hact, TM1.stepAux]
        rfl
      simp only [he, Option.getD_some]
    have hret := ret_run M q v' L' (S' k).length
    have hend : ∀ bit, advance M ⟨some (ret q), v', Tape.mk' ∅ (addBottom L')⟩ bit =
        TM1.stepAux (trNormal q) v' (Tape.mk' ∅ (addBottom L')) := by
      intro bit
      simp [advance, TM1.step, tr, TM1.stepAux, Tape.mk'_head, addBottom_head_fst]
    have hr := (((hgo.trans (.one hs)).trans hret).trans (.one hend)).trans htail
    refine ⟨b, (S k).length + 1 + (S' k).length + 1 + n, ?_, ?_, ?_⟩
    · simpa only [step_run, v', S'] using hcfg
    · have hk := hB k
      have hk' := hb' k
      rw [Nat.add_mul]
      omega
    · simpa only [trNormal_run, TM1.stepAux] using hr
  | load a q ih => exact ih (a v) S L hL hB
  | branch p q₁ q₂ ih₁ ih₂ =>
    simp only [stackOps] at hB ⊢
    cases hp : p v
    · obtain ⟨b, n, hcfg, hn, hr⟩ := ih₂ v S L hL (fun k ↦ by have h := hB k; omega)
      refine ⟨b, n, ?_, hn.trans (Nat.mul_le_mul_right _ (Nat.le_max_right _ _)), ?_⟩
      · simpa only [TM2.stepAux, hp, Bool.cond_false] using hcfg
      · simpa only [trNormal, TM1.stepAux, hp, Bool.cond_false] using hr
    · obtain ⟨b, n, hcfg, hn, hr⟩ := ih₁ v S L hL (fun k ↦ by have h := hB k; omega)
      refine ⟨b, n, ?_, hn.trans (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)), ?_⟩
      · simpa only [TM2.stepAux, hp, Bool.cond_true] using hcfg
      · simpa only [trNormal, TM1.stepAux, hp, Bool.cond_true] using hr
  | goto l => exact ⟨_, 0, .mk L hL, by simp [stackOps], .zero _⟩
  | halt => exact ⟨_, 0, .mk L hL, by simp [stackOps], .zero _⟩

variable [Fintype Λ]

noncomputable def growth : ℕ := machineOps (M false) + machineOps (M true)

theorem stackOps_le (bit : Bool) (l : Λ) : stackOps (M bit l) ≤ growth M := by
  have h := StackToTapeTime.stackOps_le (M bit) l
  cases bit <;> simp only [growth] <;> omega

theorem advance_length (a : TM2.Cfg Γ Λ σ) (bit : Bool) (k : K) :
    ((sourceAdvance M a bit).stk k).length ≤ (a.stk k).length + growth M := by
  rcases a with ⟨l, v, S⟩
  cases l with
  | none => simp [sourceAdvance, TM2.step]
  | some l =>
    exact (stepAux_length (M bit l) v S k).trans
      (Nat.add_le_add_left (stackOps_le M bit l) _)

theorem fold_length (a : TM2.Cfg Γ Λ σ) (coins : List Bool) (k : K) :
    ((coins.foldl (sourceAdvance M) a).stk k).length ≤
      (a.stk k).length + growth M * coins.length := by
  induction coins generalizing a with
  | nil => simp
  | cons bit coins ih =>
    have h := ih (sourceAdvance M a bit)
    have h' := advance_length M a bit k
    simp only [List.foldl_cons, List.length_cons, Nat.mul_succ]
    omega

theorem step_simulation (B : ℕ) (a : TM2.Cfg Γ Λ σ)
    (c : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ) (hc : TrCfg a c)
    (hB : ∀ k, (a.stk k).length + growth M ≤ B) (bit : Bool) :
    ∃ d n, n < 1 + growth M * (2 * B + 2) ∧
      DeterministicRun (advance M) n (advance M c bit) d ∧ TrCfg (sourceAdvance M a bit) d := by
  cases hc with
  | @mk l v S L hL =>
    cases l with
    | none => exact ⟨_, 0, by omega, .zero _, .mk L hL⟩
    | some l =>
      obtain ⟨d, n, hd, hn, hr⟩ := block M (M bit l) v S L hL B (fun k ↦
        (Nat.add_le_add_left (stackOps_le M bit l) _).trans (hB k))
      refine ⟨d, n, ?_, hr, hd⟩
      have h := Nat.mul_le_mul_right (2 * B + 2) (stackOps_le M bit l)
      omega

theorem source_stationary (a : TM2.Cfg Γ Λ σ) (ha : a.l = none) (bit : Bool) :
    sourceAdvance M a bit = a := by
  cases a
  simp_all [sourceAdvance, TM2.step]

theorem target_stationary (c : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ)
    (hc : c.l = none) (bit : Bool) : advance M c bit = c := by
  cases c
  simp_all [advance, TM1.step]

theorem config_var {a : TM2.Cfg Γ Λ σ} {c : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ}
    (hc : TrCfg a c) : a.var = c.var := by cases hc; rfl

theorem config_halt {a : TM2.Cfg Γ Λ σ} {c : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ}
    (hc : TrCfg a c) (ha : a.l = none) : c.l = none := by
  cases hc
  simp_all

/-- Every source coin path has the same output distribution after stack
simulation. The worst-case time bound is quadratic in the source clock. -/
theorem uniform_simulation {α : Type} (out : σ → α)
    (a : TM2.Cfg Γ Λ σ) (c : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ)
    (hc : TrCfg a c) (B n k : ℕ) (hB : ∀ j, (a.stk j).length ≤ B)
    (hk : (1 + growth M * (2 * (B + growth M * (n + 1)) + 2)) * n ≤ k)
    (hn : ∀ r : Fin n → Bool, ((List.ofFn r).foldl (sourceAdvance M) a).l = none) :
    (∀ r : Fin k → Bool, ((List.ofFn r).foldl (advance M) c).l = none) ∧
    (∀ P : α → Prop,
      Lax253009.FiniteProbability.probability (fun r : Fin k → Bool ↦
        P (out ((List.ofFn r).foldl (advance M) c).var)) =
      Lax253009.FiniteProbability.probability (fun r : Fin n → Bool ↦
        P (out ((List.ofFn r).foldl (sourceAdvance M) a).var))) := by
  let R (b : TM2.Cfg Γ Λ σ) (d : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ) :=
    TrCfg b d ∧ ∃ coins : List Bool, coins.length ≤ n ∧ coins.foldl (sourceAdvance M) a = b
  apply FairExecution.uniform_simulation (sourceAdvance M) (advance M)
    (fun b ↦ out b.var) (fun d ↦ out d.var) (fun b ↦ b.l = none) (fun d ↦ d.l = none)
    R (1 + growth M * (2 * (B + growth M * (n + 1)) + 2))
    (source_stationary M) ?_ ?_ a c ⟨hc, [], by simp, rfl⟩ n k hk hn
  · intro b d hbd hb
    have hh := config_halt hbd.1 hb
    exact ⟨hh, target_stationary M d hh, congrArg out (config_var hbd.1)⟩
  · intro b d hbd bit
    by_cases hb : b.l = none
    · have hd := config_halt hbd.1 hb
      refine ⟨d, 0, by omega, ?_, ?_⟩
      · rw [target_stationary M d hd]; exact .zero _
      · simpa only [source_stationary M b hb] using hbd
    · obtain ⟨hcfg, coins, hlen, he⟩ := hbd
      have hlt : coins.length < n := by
        by_contra hlt
        have hnlen : n = coins.length := by omega
        subst n
        have hh := hn (fun i : Fin coins.length ↦ coins[i.val])
        rw [List.ofFn_getElem, he] at hh
        exact hb hh
      have hsize : ∀ j, (b.stk j).length + growth M ≤ B + growth M * (n + 1) := by
        intro j
        have hlen' := fold_length M a coins j
        rw [he] at hlen'
        have hj := hB j
        have hg := Nat.mul_le_mul_left (growth M) hlen
        rw [Nat.mul_succ]
        omega
      obtain ⟨d', t, ht, hr, hd'⟩ := step_simulation M _ b d hcfg hsize bit
      refine ⟨d', t, ht, hr, hd', coins ++ [bit], ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]; omega
      · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, he]

variable [Inhabited Λ]

theorem supportsStmt_mono {S T : Finset (Λ' K Γ Λ σ)} (h : S ⊆ T)
    (q : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ) (hq : TM1.SupportsStmt S q) :
    TM1.SupportsStmt T q := by
  induction q with
  | move d q ih | write f q ih | load f q ih => exact ih hq
  | branch p q r ihq ihr => exact ⟨ihq hq.1, ihr hq.2⟩
  | goto l => exact fun a v ↦ h (hq a v)
  | halt => trivial

theorem normal_not_subterm (q : TM2.Stmt Γ Λ σ) (l : Λ) : normal l ∉ trStmts₁ q := by
  induction q using stmtStRec with
  | run k o q ih => simp [trStmts₁_run, ih]
  | load f q ih => exact ih
  | branch p q r ihq ihr => simp [trStmts₁, ihq, ihr]
  | goto f => simp [trStmts₁]
  | halt => simp [trStmts₁]

noncomputable def support : Finset (Λ' K Γ Λ σ) :=
  trSupp (M false) Finset.univ ∪ trSupp (M true) Finset.univ

/-- Both branch tables share one finite support. Administrative labels
have exactly the same meaning in the two tables. -/
theorem supports (bit : Bool) : TM1.Supports (tr (M bit)) (support M) := by
  classical
  have hM (b : Bool) : TM2.Supports (M b) Finset.univ := by
    constructor
    · exact Finset.mem_univ _
    · intro l hl
      induction M b l with
      | push k f q ih | peek k f q ih | pop k f q ih | load f q ih => exact ih
      | branch p q r ihq ihr => exact ⟨ihq, ihr⟩
      | goto f => exact fun _ ↦ Finset.mem_univ _
      | halt => trivial
  have htr (b : Bool) := tr_supports (M b) (hM b)
  have hsub (b : Bool) : trSupp (M b) Finset.univ ⊆ support M := by
    cases b
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  constructor
  · exact hsub bit (htr bit).1
  · intro l hl
    cases l with
    | normal l =>
      have hnormal : normal l ∈ trSupp (M bit) Finset.univ :=
        Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, Finset.mem_insert_self _ _⟩
      exact supportsStmt_mono (hsub bit) _ ((htr bit).2 _ hnormal)
    | go j o q =>
      rcases Finset.mem_union.mp hl with hl | hl
      · exact supportsStmt_mono (hsub false) _ ((htr false).2 _ hl)
      · exact supportsStmt_mono (hsub true) _ ((htr true).2 _ hl)
    | ret q =>
      rcases Finset.mem_union.mp hl with hl | hl
      · exact supportsStmt_mono (hsub false) _ ((htr false).2 _ hl)
      · exact supportsStmt_mono (hsub true) _ ((htr true).2 _ hl)

end Lax253009Proofs.RegisteredBridge.RandomStackTape
