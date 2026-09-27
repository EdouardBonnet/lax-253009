import Lax253009Proofs.RegisteredBridge.TM2InputOutput
import Lax666725.ProbabilisticMachines
import Mathlib.Tactic.DeriveFintype

set_option backward.isDefEq.respectTransparency false

namespace Lax253009Proofs.RegisteredBridge.RandomTapeSimulation

open PCPFoundation.Complexity Turing FiniteEncoding StackEncoding
open Lax666725.ProbabilisticMachines

inductive Slot | coins | left | right deriving DecidableEq, Fintype

@[reducible] def alphabet (M : Machine) : Slot → Type
  | .coins => Bool
  | .left | .right => M.Γ

instance alphabetFintype (M : Machine) (k : Slot) : Fintype (alphabet M k) := by
  cases k <;> infer_instance

abbrev Store (M : Machine) := M.Q × M.Γ × Bool

def next (M : Machine) (v : Store M) : M.Q × TM0.Stmt M.Γ :=
  (M.transition v.2.2 v.1 v.2.1).getD (v.1, .write v.2.1)

def program (M : Machine) (_ : Unit) : TM2.Stmt (alphabet M) Unit (Store M) :=
  .pop .coins (fun v a ↦ (v.1, v.2.1, a.getD false))
    (.branch (fun v ↦ (M.transition v.2.2 v.1 v.2.1).isNone) (.goto fun _ ↦ ())
      (.branch (fun v ↦ match (next M v).2 with | .move .left => true | _ => false)
        (.push .right (fun v ↦ v.2.1)
          (.load (fun v ↦ ((next M v).1, v.2.1, v.2.2))
            (.pop .left (fun v a ↦ (v.1, a.getD default, v.2.2)) (.goto fun _ ↦ ()))))
        (.branch (fun v ↦ match (next M v).2 with | .move .right => true | _ => false)
          (.push .left (fun v ↦ v.2.1)
            (.load (fun v ↦ ((next M v).1, v.2.1, v.2.2))
              (.pop .right (fun v a ↦ (v.1, a.getD default, v.2.2)) (.goto fun _ ↦ ()))))
          (.load (fun v ↦ ((next M v).1,
            (match (next M v).2 with | .write a => a | _ => v.2.1), v.2.2))
            (.goto fun _ ↦ ())))))

def tapeStacks (M : Machine) (r : List Bool) (l u : List M.Γ) : (k : Slot) → List (alphabet M k)
  | .coins => r
  | .left => l
  | .right => u

def cfg (M : Machine) (q : M.Q) (a : M.Γ) (b : Bool)
    (r : List Bool) (l u : List M.Γ) : TM2.Cfg (alphabet M) Unit (Store M) :=
  ⟨some (), (q, a, b), tapeStacks M r l u⟩

def tapeCfg (M : Machine) (q : M.Q) (a : M.Γ) (l u : List M.Γ) : TM0.Cfg M.Γ M.Q :=
  ⟨q, ⟨a, ListBlank.mk l, ListBlank.mk u⟩⟩

theorem pop_coins (M : Machine) (r : List Bool) (l u : List M.Γ) :
    Function.update (tapeStacks M r l u) .coins r.tail = tapeStacks M r.tail l u := by
  funext k; cases k <;> rfl

theorem tape_stacks_left (M : Machine) (r : List Bool) (l l' u : List M.Γ) :
    Function.update (tapeStacks M r l u) .left l' = tapeStacks M r l' u := by
  funext k; cases k <;> rfl

theorem tape_stacks_right (M : Machine) (r : List Bool) (l u u' : List M.Γ) :
    Function.update (tapeStacks M r l u) .right u' = tapeStacks M r l u' := by
  funext k; cases k <;> rfl

theorem step_none (M : Machine) (q : M.Q) (a : M.Γ) (b c : Bool)
    (r : List Bool) (l u : List M.Γ) (h : M.transition c q a = none) :
    totalStep (program M) (cfg M q a b (c :: r) l u) = cfg M q a c r l u := by
  simp [totalStep, program, cfg, TM2.stepAux, tapeStacks, h]
  congr 1
  funext k; cases k <;> rfl

theorem step_left (M : Machine) (q q' : M.Q) (a : M.Γ) (b c : Bool)
    (r : List Bool) (l u : List M.Γ) (h : M.transition c q a = some (q', .move .left)) :
    totalStep (program M) (cfg M q a b (c :: r) l u) =
      cfg M q' (l.head?.getD default) c r l.tail (a :: u) := by
  simp [totalStep, program, cfg, TM2.stepAux, tapeStacks, next, h]
  congr 1
  funext k; cases k <;> rfl

theorem step_right (M : Machine) (q q' : M.Q) (a : M.Γ) (b c : Bool)
    (r : List Bool) (l u : List M.Γ) (h : M.transition c q a = some (q', .move .right)) :
    totalStep (program M) (cfg M q a b (c :: r) l u) =
      cfg M q' (u.head?.getD default) c r (a :: l) u.tail := by
  simp [totalStep, program, cfg, TM2.stepAux, tapeStacks, next, h]
  congr 1
  funext k; cases k <;> rfl

theorem step_write (M : Machine) (q q' : M.Q) (a a' : M.Γ) (b c : Bool)
    (r : List Bool) (l u : List M.Γ) (h : M.transition c q a = some (q', .write a')) :
    totalStep (program M) (cfg M q a b (c :: r) l u) = cfg M q' a' c r l u := by
  simp [totalStep, program, cfg, TM2.stepAux, tapeStacks, next, h]
  congr 1
  funext k; cases k <;> rfl

theorem step (M : Machine) (q : M.Q) (a : M.Γ) (b c : Bool)
    (r : List Bool) (l u : List M.Γ) :
    ∃ q' a' l' u', M.advance (tapeCfg M q a l u) c = tapeCfg M q' a' l' u' ∧
      totalStep (program M) (cfg M q a b (c :: r) l u) = cfg M q' a' c r l' u' := by
  cases h : M.transition c q a with
  | none =>
    exact ⟨q, a, l, u, by simp [Machine.advance, TM0.step, tapeCfg, h],
      step_none M q a b c r l u h⟩
  | some p =>
    obtain ⟨q', action⟩ := p
    cases action with
    | move d =>
      cases d with
      | left =>
        refine ⟨q', l.head?.getD default, l.tail, a :: u, ?_, step_left M q q' a b c r l u h⟩
        simp only [Machine.advance, TM0.step, tapeCfg, h, Option.map_some, Option.getD_some]
        cases l <;> rfl
      | right =>
        refine ⟨q', u.head?.getD default, a :: l, u.tail, ?_, step_right M q q' a b c r l u h⟩
        simp only [Machine.advance, TM0.step, tapeCfg, h, Option.map_some, Option.getD_some]
        cases u <;> rfl
    | write a' =>
      exact ⟨q', a', l, u, by simp [Machine.advance, TM0.step, tapeCfg, h],
        step_write M q q' a a' b c r l u h⟩

theorem run (M : Machine) (q : M.Q) (a : M.Γ) (b : Bool) (r : List Bool) (l u : List M.Γ) :
    ∃ q' a' b' l' u', r.foldl M.advance (tapeCfg M q a l u) = tapeCfg M q' a' l' u' ∧
      (totalStep (program M))^[r.length] (cfg M q a b r l u) = cfg M q' a' b' [] l' u' := by
  induction r generalizing q a b l u with
  | nil => exact ⟨q, a, b, l, u, rfl, rfl⟩
  | cons c r ih =>
    obtain ⟨q₁, a₁, l₁, u₁, he, hs⟩ := step M q a b c r l u
    obtain ⟨q₂, a₂, b₂, l₂, u₂, he₂, hs₂⟩ := ih q₁ a₁ c l₁ u₁
    refine ⟨q₂, a₂, b₂, l₂, u₂, ?_, ?_⟩
    · simpa only [List.foldl_cons, he] using he₂
    · simpa only [List.length_cons, Function.iterate_succ_apply, hs] using hs₂

def start (M : Machine) (z : List Bool) : TM2.Cfg (alphabet M) Unit (Store M) :=
  cfg M default (((pairFst z).map M.input).head?.getD default) false
    (pairSnd z) [] ((pairFst z).map M.input).tail

theorem start_tape (M : Machine) (x : List Bool) :
    tapeCfg M default ((x.map M.input).head?.getD default) [] (x.map M.input).tail =
      TM0.init (x.map M.input) := by
  cases x <;> rfl

theorem start_encode_mem_FP (M : Machine) : (fun z ↦ encode (start M z)) ∈ FP := by
  classical
  have hv : (fun z ↦ code ((start M z).l, (start M z).var)) ∈ FP := by
    have h := bounded_read_mem_FP pairFst_mem_FP 1
      (fun l ↦ code ((some () : Option Unit),
        ((default : M.Q), ((l.map M.input).head?.getD default), false)))
    apply mem_FP_of_eq h
    intro z
    simp only [start, cfg]
    cases pairFst z <;> rfl
  have hs : ∀ k : Slot, (fun z ↦ packets ((start M z).stk k)) ∈ FP := by
    intro k
    cases k with
    | coins =>
      simpa only [start, cfg, tapeStacks, List.map_id, Function.comp_def] using
        mem_FP_comp pairSnd_mem_FP (packets_map_mem_FP (id : Bool → Bool))
    | left => exact constFn_mem_FP []
    | right =>
      simpa only [start, cfg, tapeStacks, List.map_tail, List.drop_one, Function.comp_def] using
        mem_FP_comp (drop_mem_FP pairFst_mem_FP 1) (packets_map_mem_FP M.input)
  exact mem_FP_pair hv (encodeVec_mem_FP
    (fun i z ↦ packets ((start M z).stk ((Fintype.equivFin Slot).symm i)))
    (fun i ↦ hs _))

theorem start_size (M : Machine) (z : List Bool) (k : Slot) :
    ((start M z).stk k).length ≤ z.length := by
  cases k with
  | coins => exact pairSnd_length_le z
  | left => exact Nat.zero_le _
  | right =>
    simp only [start, cfg, tapeStacks, List.length_tail, List.length_map]
    have h := pairFst_length_le z
    omega

noncomputable def flag (M : Machine) (out : M.Q → Bool) (z : List Bool) : List Bool :=
  [out (readState Unit (Store M) z).2.1]

theorem flag_mem_FP (M : Machine) (out : M.Q → Bool) : flag M out ∈ FP :=
  state_dispatch_mem_FP (Λ := Unit) (σ := Store M) (fun c _ ↦ [out c.2.1]) (fun _ ↦ constFn_mem_FP _)

theorem finite_coin_evaluation_mem_FP (M : Machine) (out : M.Q → Bool) :
    (fun z ↦ [out (M.run (pairFst z) (pairSnd z)).q]) ∈ FP := by
  have hr := compile_run (program M) (start M) pairSnd
    (start_encode_mem_FP M) pairSnd_mem_FP (start_size M)
  have hf := mem_FP_comp hr (flag_mem_FP M out)
  apply mem_FP_of_eq hf
  intro z
  obtain ⟨q, a, b, l, u, he, hs⟩ := run M default
    (((pairFst z).map M.input).head?.getD default) false (pairSnd z) []
      ((pairFst z).map M.input).tail
  change flag M out (encode ((totalStep (program M))^[(pairSnd z).length] (start M z))) = _
  unfold start
  rw [hs]
  simp only [flag, read_state_encode, cfg]
  have hr' : M.run (pairFst z) (pairSnd z) = tapeCfg M q a l u := by
    simpa only [Machine.run, start_tape] using he
  rw [hr']
  rfl

end Lax253009Proofs.RegisteredBridge.RandomTapeSimulation
