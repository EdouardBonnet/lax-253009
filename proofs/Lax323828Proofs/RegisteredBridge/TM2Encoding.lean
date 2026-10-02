import Lax323828Proofs.RegisteredBridge.FiniteWordEncoding
import Mathlib.Computability.TuringMachine.Computable

set_option backward.isDefEq.respectTransparency false

namespace Lax323828Proofs.RegisteredBridge

open PCPFoundation.Complexity FiniteEncoding
open scoped BigOperators

namespace StackEncoding

variable {K Λ σ : Type} {Γ : K → Type}
  [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [Nonempty σ]
  [∀ k, Fintype (Γ k)]

abbrev Control (Λ σ : Type) := Option Λ × σ

noncomputable def encode (c : Turing.TM2.Cfg Γ Λ σ) : List Bool :=
  pair (code (c.l, c.var)) (Cobham.encodeVec fun i : Fin (Fintype.card K) ↦
    packets (c.stk ((Fintype.equivFin K).symm i)))

def stateKey (Λ σ : Type) [Fintype Λ] [Fintype σ] (z : List Bool) : List Bool :=
  (pairFst z).take (Fintype.card (Control Λ σ))

noncomputable def readState (Λ σ : Type) [Fintype Λ] [Fintype σ] [Nonempty σ]
    (z : List Bool) : Control Λ σ :=
  (decode (stateKey Λ σ z)).getD (none, Classical.arbitrary σ)

noncomputable def stack (z : List Bool) (k : K) : List Bool :=
  entry (Fintype.equivFin K k).val (pairSnd z)

theorem read_state_encode (c : Turing.TM2.Cfg Γ Λ σ) :
    readState Λ σ (encode c) = (c.l, c.var) := by
  simp only [readState, stateKey, encode, pairFst_pair, ← code_length (c.l, c.var),
    List.take_length, decode_code, Option.getD_some]

theorem stack_encode (c : Turing.TM2.Cfg Γ Λ σ) (k : K) :
    stack (encode c) k = packets (c.stk k) := by
  simp only [stack, encode, pairSnd_pair, entry_encodeVec]
  exact congrArg (fun j : K ↦ packets (c.stk j)) ((Fintype.equivFin K).symm_apply_apply k)

theorem state_key_mem_FP : stateKey Λ σ ∈ FP := take_mem_FP pairFst_mem_FP _

theorem stack_mem_FP (k : K) : (fun z ↦ stack z k) ∈ FP :=
  mem_FP_comp pairSnd_mem_FP (entry_mem_FP _)

noncomputable def rebuild (q : List Bool) (st : K → List Bool) : List Bool :=
  pair q (Cobham.encodeVec fun i : Fin (Fintype.card K) ↦ st ((Fintype.equivFin K).symm i))

theorem rebuild_mem_FP {q : List Bool → List Bool} {st : K → List Bool → List Bool}
    (hq : q ∈ FP) (hst : ∀ k, st k ∈ FP) :
    (fun z ↦ rebuild (q z) (fun k ↦ st k z)) ∈ FP :=
  mem_FP_pair hq (encodeVec_mem_FP _ (fun _ ↦ hst _))

noncomputable def replaceState (f : Control Λ σ → Control Λ σ) (z : List Bool) : List Bool :=
  pair (code (f (readState Λ σ z))) (pairSnd z)

theorem replace_state_mem_FP (f : Control Λ σ → Control Λ σ) : replaceState f ∈ FP := by
  apply mem_FP_pair _ pairSnd_mem_FP
  exact mem_FP_of_bounded_key (state_key_mem_FP (Λ := Λ) (σ := σ))
    (fun _z ↦ List.length_take_le _ _)
    (fun key ↦ code (f ((decode key).getD (none, Classical.arbitrary σ))))

theorem replace_state_encode (f : Control Λ σ → Control Λ σ) (c : Turing.TM2.Cfg Γ Λ σ) :
    replaceState f (encode c) = encode ⟨(f (c.l, c.var)).1, (f (c.l, c.var)).2, c.stk⟩ := by
  unfold replaceState
  rw [read_state_encode]
  simp only [encode, pairSnd_pair, Prod.mk.eta]

noncomputable def replaceStack (k : K) (f : List Bool → List Bool) (z : List Bool) : List Bool :=
  rebuild (pairFst z) (fun j ↦ if j = k then f (stack z k) else stack z j)

theorem replace_stack_mem_FP (k : K) {f : List Bool → List Bool} (hf : f ∈ FP) :
    replaceStack k f ∈ FP := by
  apply rebuild_mem_FP pairFst_mem_FP
  intro j
  by_cases hj : j = k
  · subst j
    simpa only [ite_true, Function.comp_def] using mem_FP_comp (stack_mem_FP (K := K) k) hf
  · simpa only [hj, ite_false] using stack_mem_FP (K := K) j

theorem replace_stack_encode (k : K) (f : List Bool → List Bool) (g : List (Γ k) → List (Γ k))
    (h : ∀ l, f (packets l) = packets (g l)) (c : Turing.TM2.Cfg Γ Λ σ) :
    replaceStack k f (encode c) = encode ⟨c.l, c.var, Function.update c.stk k (g (c.stk k))⟩ := by
  simp only [replaceStack, rebuild, encode, pairFst_pair]
  congr 1
  congr 1
  funext i
  change (if (Fintype.equivFin K).symm i = k then f (stack (encode c) k)
    else stack (encode c) ((Fintype.equivFin K).symm i)) = _
  simp only [stack_encode, h]
  by_cases hi : (Fintype.equivFin K).symm i = k
  · rw [if_pos hi]
    have hh := congrArg (fun j : K ↦ packets ((Function.update c.stk k (g (c.stk k))) j)) hi
    simpa only [Function.update_self] using hh.symm
  · simp only [hi, ite_false, Function.update_of_ne hi]

theorem state_dispatch_mem_FP (F : Control Λ σ → List Bool → List Bool)
    (hF : ∀ q, F q ∈ FP) : (fun z ↦ F (readState Λ σ z) z) ∈ FP := by
  exact bounded_dispatch_mem_FP (state_key_mem_FP (Λ := Λ) (σ := σ))
    (fun _z ↦ List.length_take_le _ _)
    (fun key ↦ (decode key).getD (none, Classical.arbitrary σ)) F hF

noncomputable def push (k : K) (f : σ → Γ k) (z : List Bool) : List Bool :=
  replaceStack k (fun w ↦ packet (f (readState Λ σ z).2) ++ w) z

theorem push_mem_FP (k : K) (f : σ → Γ k) : push (Λ := Λ) k f ∈ FP := by
  apply state_dispatch_mem_FP (fun q z ↦ replaceStack k (fun w ↦ packet (f q.2) ++ w) z)
  intro q
  exact replace_stack_mem_FP k (Cobham.appendFn_mem_FP (constFn_mem_FP _)
    (CobhamFP_subset_FP (Cobham.proj (0 : Fin 1))))

theorem push_encode (k : K) (f : σ → Γ k) (c : Turing.TM2.Cfg Γ Λ σ) :
    push (Λ := Λ) k f (encode c) = encode ⟨c.l, c.var, Function.update c.stk k (f c.var :: c.stk k)⟩ := by
  unfold push
  rw [read_state_encode]
  exact replace_stack_encode k (fun w ↦ packet (f c.var) ++ w) (List.cons (f c.var))
    (fun _ ↦ rfl) c

noncomputable def peekKey (k : K) (z : List Bool) : List Bool :=
  pair (stateKey Λ σ z) ((stack z k).take (Fintype.card (Γ k) + 1))

theorem peek_key_mem_FP (k : K) : peekKey (Λ := Λ) (σ := σ) (Γ := Γ) k ∈ FP :=
  mem_FP_pair state_key_mem_FP (take_mem_FP (stack_mem_FP k) _)

theorem peek_key_length (k : K) (z : List Bool) :
    (peekKey (Λ := Λ) (σ := σ) (Γ := Γ) k z).length ≤
      2 * Fintype.card (Control Λ σ) + 2 + (Fintype.card (Γ k) + 1) := by
  simp only [peekKey, pair_length]
  have h₁ : (stateKey Λ σ z).length ≤ Fintype.card (Control Λ σ) := List.length_take_le _ _
  have h₂ : ((stack z k).take (Fintype.card (Γ k) + 1)).length ≤ Fintype.card (Γ k) + 1 :=
    List.length_take_le _ _
  omega

noncomputable def peek (k : K) (f : σ → Option (Γ k) → σ) (z : List Bool) : List Bool :=
  pair (code ((readState Λ σ z).1,
    f (readState Λ σ z).2 (readHead ((stack z k).take (Fintype.card (Γ k) + 1))))) (pairSnd z)

theorem peek_mem_FP (k : K) (f : σ → Option (Γ k) → σ) : peek (Λ := Λ) k f ∈ FP := by
  apply mem_FP_pair _ pairSnd_mem_FP
  have h := mem_FP_of_bounded_key (peek_key_mem_FP (Γ := Γ) (Λ := Λ) (σ := σ) k)
    (peek_key_length k)
    (fun key ↦
      let q : Control Λ σ := (decode (pairFst key)).getD (none, Classical.arbitrary σ)
      code (q.1, f q.2 (readHead (pairSnd key))))
  simpa only [peekKey, pairFst_pair, pairSnd_pair, readState] using h

theorem peek_encode (k : K) (f : σ → Option (Γ k) → σ) (c : Turing.TM2.Cfg Γ Λ σ) :
    peek (Λ := Λ) k f (encode c) = encode ⟨c.l, f c.var (c.stk k).head?, c.stk⟩ := by
  unfold peek
  rw [read_state_encode, stack_encode, read_head_packets]
  simp only [encode, pairSnd_pair]

theorem drop_stack_mem_FP (k : K) :
    replaceStack k (fun w ↦ w.drop (Fintype.card (Γ k) + 1)) ∈ FP :=
  replace_stack_mem_FP k (drop_mem_FP (CobhamFP_subset_FP (Cobham.proj (0 : Fin 1))) _)

theorem drop_stack_encode (k : K) (c : Turing.TM2.Cfg Γ Λ σ) :
    replaceStack k (fun w ↦ w.drop (Fintype.card (Γ k) + 1)) (encode c) =
      encode ⟨c.l, c.var, Function.update c.stk k (c.stk k).tail⟩ :=
  replace_stack_encode k _ List.tail drop_packets c

theorem branch_mem_FP (p : σ → Bool) {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    (fun z ↦ if p (readState Λ σ z).2 then f z else g z) ∈ FP := by
  apply state_dispatch_mem_FP (fun q z ↦ if p q.2 then f z else g z)
  intro q
  cases h : p q.2
  · simpa only [h, Bool.false_eq_true, if_false] using hg
  · simpa only [h, if_true] using hf

theorem compile_statement (q : Turing.TM2.Stmt Γ Λ σ) :
    ∃ f : List Bool → List Bool, f ∈ FP ∧
      ∀ c : Turing.TM2.Cfg Γ Λ σ, f (encode c) = encode (Turing.TM2.stepAux q c.var c.stk) := by
  induction q with
  | push k f q ih =>
    obtain ⟨g, hg, hsim⟩ := ih
    refine ⟨g ∘ push (Λ := Λ) k f, mem_FP_comp (push_mem_FP k f) hg, ?_⟩
    intro c
    rw [Function.comp_apply, push_encode, hsim]
    rfl
  | peek k f q ih =>
    obtain ⟨g, hg, hsim⟩ := ih
    refine ⟨g ∘ peek (Λ := Λ) k f, mem_FP_comp (peek_mem_FP k f) hg, ?_⟩
    intro c
    rw [Function.comp_apply, peek_encode, hsim]
    rfl
  | pop k f q ih =>
    obtain ⟨g, hg, hsim⟩ := ih
    let drop := replaceStack k (fun w ↦ w.drop (Fintype.card (Γ k) + 1))
    refine ⟨g ∘ drop ∘ peek (Λ := Λ) k f,
      mem_FP_comp (mem_FP_comp (peek_mem_FP k f) (drop_stack_mem_FP k)) hg, ?_⟩
    intro c
    dsimp only [Function.comp_apply, drop]
    rw [peek_encode, drop_stack_encode, hsim]
    rfl
  | load f q ih =>
    obtain ⟨g, hg, hsim⟩ := ih
    refine ⟨g ∘ replaceState (fun q : Control Λ σ ↦ (q.1, f q.2)),
      mem_FP_comp (replace_state_mem_FP _) hg, ?_⟩
    intro c
    rw [Function.comp_apply, replace_state_encode, hsim]
    rfl
  | branch p q r ihq ihr =>
    obtain ⟨f, hf, hsimf⟩ := ihq
    obtain ⟨g, hg, hsimg⟩ := ihr
    refine ⟨fun z ↦ if p (readState Λ σ z).2 then f z else g z, branch_mem_FP p hf hg, ?_⟩
    intro c
    dsimp only
    rw [read_state_encode]
    cases hp : p c.var <;> simp only [hp, Bool.false_eq_true, if_false, if_true,
      Turing.TM2.stepAux, Bool.cond_false, Bool.cond_true, hsimf, hsimg]
  | goto f =>
    refine ⟨replaceState (fun q : Control Λ σ ↦ (some (f q.2), q.2)), replace_state_mem_FP _, ?_⟩
    intro c
    rw [replace_state_encode]
    rfl
  | halt =>
    refine ⟨replaceState (fun q : Control Λ σ ↦ (none, q.2)), replace_state_mem_FP _, ?_⟩
    intro c
    rw [replace_state_encode]
    rfl

end StackEncoding
end Lax323828Proofs.RegisteredBridge
