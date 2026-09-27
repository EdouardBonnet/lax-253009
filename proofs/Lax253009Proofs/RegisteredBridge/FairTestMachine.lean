import Lax253009Proofs.RegisteredBridge.MultitapeTransducer
import Lax253009Proofs.RegisteredBridge.StackSubroutineRandom
import Lax253009Proofs.RegisteredBridge.FixedStackRead
import Lax253009Proofs.RegisteredBridge.FairTests

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Lax253009Proofs.RegisteredBridge.FairTestMachine

open Turing PCPFoundation.Complexity StackSubroutine FairExecution Function
open scoped Classical

noncomputable section

variable {m n : ℕ} (A : TM m) (B : TM n)

abbrev Stack (m n : ℕ) := StackTapeMachine.StackIndex (MultitapeCore.Index m) ⊕
  StackTapeMachine.StackIndex (MultitapeCore.Index n)

abbrev Alphabet : Stack m n → Type :=
  StackSubroutine.Alphabet StackTapeMachine.Alphabet StackTapeMachine.Alphabet

instance alphabetFintype (k : Stack m n) : Fintype (Alphabet k) := by
  cases k with
  | inl k =>
    cases k with
    | inl bit => exact inferInstanceAs (Fintype Bool)
    | inr i => exact inferInstanceAs (Fintype Γ)
  | inr k =>
    cases k with
    | inl bit => exact inferInstanceAs (Fintype Bool)
    | inr i => exact inferInstanceAs (Fintype Γ)

noncomputable instance transducerRegisterFintype (C : TM m) :
    Fintype (MultitapeTransducer.machine C).σ := (MultitapeTransducer.machine C).σFin

inductive Label
  | prepare : MultitapeTransducer.Label → Label
  | check : MultitapeTransducer.Label → Label
  | sample | copyRest | reverseCoins | readAnswer
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.prepare .readInput⟩

structure Register where
  prep : (MultitapeTransducer.machine A).σ
  check : (MultitapeTransducer.machine B).σ
  bit : Bool
  more : Bool
  answer : Fin (Fintype.card (Option Bool)) → Bool
  deriving Fintype

noncomputable instance : Inhabited (Register A B) :=
  ⟨⟨MultitapeTransducer.initial A, MultitapeTransducer.initial B, false, false, fun _ ↦ false⟩⟩

def prepLens : Lens (MultitapeTransducer.machine A).σ (Register A B) where
  get := Register.prep
  put s a := {s with prep := a}
  get_put _ _ := rfl
  put_get _ := rfl
  put_put _ _ _ := rfl

def checkLens : Lens (MultitapeTransducer.machine B).σ (Register A B) where
  get := Register.check
  put s a := {s with check := a}
  get_put _ _ := rfl
  put_get _ := rfl
  put_put _ _ _ := rfl

def answerLens : Lens (Fin (Fintype.card (Option Bool)) → Bool) (Register A B) where
  get := Register.answer
  put s a := {s with answer := a}
  get_put _ _ := rfl
  put_get _ := rfl
  put_put _ _ _ := rfl

abbrev buffer : Stack m n := .inl (.inl false)
abbrev source : Stack m n := .inl (.inl true)
abbrev checkInput : Stack m n := .inr (.inl false)
abbrev checkOutput : Stack m n := .inr (.inl true)

noncomputable def program (coin : Bool) : Label → TM2.Stmt (Alphabet (m := m) (n := n)) Label (Register A B)
  | .prepare l => lift (prepLens A B) Label.prepare .sample (MultitapeTransducer.program A l)
  | .check l => liftRight (checkLens A B) Label.check .readAnswer (MultitapeTransducer.program B l)
  | .sample =>
    .pop source (fun v _ ↦ v)
      (.pop source (fun v a ↦ {v with bit := a.getD false})
        (.branch (fun v ↦ v.bit)
          (.push buffer (fun _ ↦ false) (.push buffer (fun _ ↦ true) (.goto fun _ ↦ .copyRest)))
          (.push buffer (fun _ ↦ coin) (.push buffer (fun _ ↦ coin) (.goto fun _ ↦ .sample)))))
  | .copyRest =>
    .pop source (fun v a ↦ {v with bit := a.getD false, more := a.isSome})
      (.branch (fun v ↦ v.more)
        (.push buffer (fun v ↦ v.bit) (.goto fun _ ↦ .copyRest))
        (.goto fun _ ↦ .reverseCoins))
  | .reverseCoins =>
    .pop buffer (fun v a ↦ {v with bit := a.getD false, more := a.isSome})
      (.branch (fun v ↦ v.more)
        (.push checkInput (fun v ↦ v.bit) (.goto fun _ ↦ .reverseCoins))
        (.load (fun v ↦ {v with check := MultitapeTransducer.initial B})
          (.goto fun _ ↦ .check .readInput)))
  | .readAnswer =>
    FixedStackRead.program checkOutput id (answerLens A B) .halt
      (List.finRange (Fintype.card (Option Bool)))

noncomputable def advance (c : TM2.Cfg (Alphabet (m := m) (n := n)) Label (Register A B)) (bit : Bool) :=
  (TM2.step (program A B bit) c).getD c

noncomputable def output (v : Register A B) : Option Bool :=
  (FiniteEncoding.decode (List.ofFn v.answer)).getD none

def io {r : ℕ} (input output : List Bool) :
    (k : StackTapeMachine.StackIndex (MultitapeCore.Index r)) → List (StackTapeMachine.Alphabet k)
  | .inl false => input
  | .inl true => output
  | .inr _ => []

def memory (buf src cin cout : List Bool) : ∀ k : Stack m n, List (Alphabet k) :=
  joinedStacks (io buf src) (io cin cout)

theorem memory_buffer (buf src cin cout : List Bool) :
    memory (m := m) (n := n) buf src cin cout buffer = buf := rfl

theorem memory_source (buf src cin cout : List Bool) :
    memory (m := m) (n := n) buf src cin cout source = src := rfl

theorem memory_checkInput (buf src cin cout : List Bool) :
    memory (m := m) (n := n) buf src cin cout checkInput = cin := rfl

theorem memory_checkOutput (buf src cin cout : List Bool) :
    memory (m := m) (n := n) buf src cin cout checkOutput = cout := rfl

def config (l : Option Label) (v : Register A B) (buf src cin cout : List Bool) :
    TM2.Cfg (Alphabet (m := m) (n := n)) Label (Register A B) :=
  ⟨l, v, memory buf src cin cout⟩

theorem update_buffer (buf src cin cout w : List Bool) :
    update (memory (m := m) (n := n) buf src cin cout) buffer w = memory w src cin cout := by
  funext k
  cases k with
  | inl k =>
    cases k with
    | inl bit => cases bit <;> simp [memory, joinedStacks, io, buffer, update]
    | inr k => simp [memory, joinedStacks, io, buffer, update]
  | inr k => simp [memory, joinedStacks, buffer, update]

theorem update_source (buf src cin cout w : List Bool) :
    update (memory (m := m) (n := n) buf src cin cout) source w = memory buf w cin cout := by
  funext k
  cases k with
  | inl k =>
    cases k with
    | inl bit => cases bit <;> simp [memory, joinedStacks, io, source, update]
    | inr k => simp [memory, joinedStacks, io, source, update]
  | inr k => simp [memory, joinedStacks, source, update]

theorem update_checkInput (buf src cin cout w : List Bool) :
    update (memory (m := m) (n := n) buf src cin cout) checkInput w = memory buf src w cout := by
  funext k
  cases k with
  | inl k => simp [memory, joinedStacks, checkInput, update]
  | inr k =>
    cases k with
    | inl bit => cases bit <;> simp [memory, joinedStacks, io, checkInput, update]
    | inr k => simp [memory, joinedStacks, io, checkInput, update]

theorem update_checkOutput (buf src cin cout w : List Bool) :
    update (memory (m := m) (n := n) buf src cin cout) checkOutput w = memory buf src cin w := by
  funext k
  cases k with
  | inl k => simp [memory, joinedStacks, checkOutput, update]
  | inr k =>
    cases k with
    | inl bit => cases bit <;> simp [memory, joinedStacks, io, checkOutput, update]
    | inr k => simp [memory, joinedStacks, io, checkOutput, update]

theorem sample_step (v : Register A B) (buf x : List Bool) (k : ℕ) (coin : Bool) :
    advance A B (config A B (some .sample) v buf (pair (List.replicate (k + 1) false) x) [] []) coin =
      config A B (some .sample) {v with bit := false} (coin :: coin :: buf)
        (pair (List.replicate k false) x) [] [] := by
  simp only [advance, config, TM2.step, program, List.replicate_succ, pair_cons_eq,
    TM2.stepAux, memory_source, memory_buffer, List.head?_cons, Option.getD_some,
    List.tail_cons, update_source, Bool.cond_false, update_buffer]
  all_goals rfl

theorem sample_done (v : Register A B) (buf x : List Bool) (coin : Bool) :
    advance A B (config A B (some .sample) v buf (pair [] x) [] []) coin =
      config A B (some .copyRest) {v with bit := true} (true :: false :: buf) x [] [] := by
  simp only [advance, config, TM2.step, program, pair, delimit, List.flatMap_nil,
    List.nil_append, List.cons_append, TM2.stepAux, memory_source, memory_buffer,
    List.head?_cons, Option.getD_some, List.tail_cons, update_source,
    Bool.cond_true, update_buffer]
  all_goals rfl

theorem copy_cons (v : Register A B) (buf x : List Bool) (b coin : Bool) :
    advance A B (config A B (some .copyRest) v buf (b :: x) [] []) coin =
      config A B (some .copyRest) {v with bit := b, more := true} (b :: buf) x [] [] := by
  simp only [advance, config, TM2.step, program, TM2.stepAux, memory_source, memory_buffer, List.head?_cons, Option.getD_some, Option.isSome_some, Bool.cond_true,
    List.tail_cons, update_source, update_buffer]
  all_goals rfl

theorem copy_nil (v : Register A B) (buf : List Bool) (coin : Bool) :
    advance A B (config A B (some .copyRest) v buf [] [] []) coin =
      config A B (some .reverseCoins) {v with bit := false, more := false} buf [] [] [] := by
  simp only [advance, config, TM2.step, program, TM2.stepAux, memory_source, memory_buffer, List.head?_nil, Option.getD_none, Option.isSome_none, Bool.cond_false,
    List.tail_nil, update_source]
  all_goals rfl

theorem copy_run (v : Register A B) (buf x : List Bool) :
    DeterministicRun (advance A B) (x.length + 1)
      (config A B (some .copyRest) v buf x [] [])
      (config A B (some .reverseCoins) {v with bit := false, more := false}
        (x.reverse ++ buf) [] [] []) := by
  induction x generalizing v buf with
  | nil => exact .one (copy_nil A B v buf)
  | cons b x ih =>
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append] using
      DeterministicRun.cons (copy_cons A B v buf x b) (ih {v with bit := b, more := true} (b :: buf))

theorem reverse_cons (v : Register A B) (buf cin : List Bool) (b coin : Bool) :
    advance A B (config A B (some .reverseCoins) v (b :: buf) [] cin []) coin =
      config A B (some .reverseCoins) {v with bit := b, more := true} buf [] (b :: cin) [] := by
  simp only [advance, config, TM2.step, program, TM2.stepAux, memory_buffer, memory_checkInput, List.head?_cons, Option.getD_some, Option.isSome_some, Bool.cond_true,
    List.tail_cons, update_buffer, update_checkInput]
  all_goals rfl

theorem reverse_nil (v : Register A B) (cin : List Bool) (coin : Bool) :
    advance A B (config A B (some .reverseCoins) v [] [] cin []) coin =
      config A B (some (.check .readInput))
        {v with bit := false, more := false, check := MultitapeTransducer.initial B} [] [] cin [] := by
  simp only [advance, config, TM2.step, program, TM2.stepAux, memory_buffer, memory_checkInput, List.head?_nil, Option.getD_none, Option.isSome_none, Bool.cond_false,
    List.tail_nil, update_buffer]
  all_goals rfl

theorem reverse_run (v : Register A B) (buf cin : List Bool) :
    DeterministicRun (advance A B) (buf.length + 1)
      (config A B (some .reverseCoins) v buf [] cin [])
      (config A B (some (.check .readInput))
        {v with bit := false, more := false, check := MultitapeTransducer.initial B}
        [] [] (buf.reverse ++ cin) []) := by
  induction buf generalizing v cin with
  | nil => exact .one (reverse_nil A B v cin)
  | cons b buf ih =>
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append] using
      DeterministicRun.cons (reverse_cons A B v buf cin b)
        (ih {v with bit := b, more := true} (b :: cin))


def answerBits (a : Option Bool) : Fin (Fintype.card (Option Bool)) → Bool :=
  fun i ↦ decide (Fintype.equivFin (Option Bool) a = i)

theorem answer_code (a : Option Bool) : List.ofFn (answerBits a) = FiniteEncoding.code a := rfl

def finalConfig (v : Register A B) (a : Option Bool) :
    TM2.Cfg (Alphabet (m := m) (n := n)) Label (Register A B) :=
  config A B none {v with answer := answerBits a} [] [] [] []

theorem final_output (v : Register A B) (a : Option Bool) :
    output A B (finalConfig A B v a).var = a := by
  change (FiniteEncoding.decode (List.ofFn (answerBits a))).getD none = a
  rw [answer_code, FiniteEncoding.decode_code]
  rfl

theorem read_answer (v : Register A B) (a : Option Bool) (coin : Bool) :
    advance A B (config A B (some .readAnswer) v [] [] [] (FiniteEncoding.code a)) coin =
      finalConfig A B v a := by
  have h := FixedStackRead.all checkOutput id id (fun b ↦ rfl) (answerLens A B)
    (.halt : TM2.Stmt (Alphabet (m := m) (n := n)) Label (Register A B))
    (answerBits a) v (memory [] [] [] []) []
  simp only [List.map_id, List.append_nil, update_checkOutput, answer_code] at h
  unfold advance
  simp only [config, TM2.step, program, h, Option.getD_some]
  rfl

theorem final_halt (v : Register A B) (a : Option Bool) :
    (finalConfig A B v a).l = none := rfl

theorem final_stationary (v : Register A B) (a : Option Bool) (coin : Bool) :
    advance A B (finalConfig A B v a) coin = finalConfig A B v a := rfl

theorem initial_io (C : TM m) (x : List Bool) :
    (initList (MultitapeTransducer.machine C) x).stk = io x [] := by
  funext k
  cases k with
  | inl bit => cases bit <;> simp [initList, MultitapeTransducer.machine, io]
  | inr i => simp [initList, MultitapeTransducer.machine, io]

theorem halted_io (C : TM m) (x : List Bool) :
    (haltList (MultitapeTransducer.machine C) x).stk = io [] x := by
  funext k
  cases k with
  | inl bit => cases bit <;> simp [haltList, MultitapeTransducer.machine, io]
  | inr i => simp [haltList, MultitapeTransducer.machine, io]

theorem prepare_initial (v : Register A B) (x : List Bool) :
    StackSubroutine.config (prepLens A B) Label.prepare .sample v (io [] [])
      (initList (MultitapeTransducer.machine A) x) =
    config A B (some (.prepare .readInput)) {v with prep := MultitapeTransducer.initial A}
      x [] [] [] := by
  apply MultitapeTransducer.cfg_ext <;> try rfl
  exact congrArg (fun S ↦ joinedStacks S (io (r := n) [] [])) (initial_io A x)

theorem prepare_final (v : Register A B) (x : List Bool) :
    StackSubroutine.config (prepLens A B) Label.prepare .sample v (io [] [])
      (haltList (MultitapeTransducer.machine A) x) =
    config A B (some .sample) {v with prep := MultitapeTransducer.initial A}
      [] x [] [] := by
  apply MultitapeTransducer.cfg_ext <;> try rfl
  exact congrArg (fun S ↦ joinedStacks S (io (r := n) [] [])) (halted_io A x)

theorem check_initial (v : Register A B) (x : List Bool) :
    configRight (checkLens A B) Label.check .readAnswer v (io [] [])
      (initList (MultitapeTransducer.machine B) x) =
    config A B (some (.check .readInput)) {v with check := MultitapeTransducer.initial B}
      [] [] x [] := by
  apply MultitapeTransducer.cfg_ext <;> try rfl
  exact congrArg (fun S ↦ joinedStacks (io (r := m) [] []) S) (initial_io B x)

theorem check_final (v : Register A B) (x : List Bool) :
    configRight (checkLens A B) Label.check .readAnswer v (io [] [])
      (haltList (MultitapeTransducer.machine B) x) =
    config A B (some .readAnswer) {v with check := MultitapeTransducer.initial B}
      [] [] [] x := by
  apply MultitapeTransducer.cfg_ext <;> try rfl
  exact congrArg (fun S ↦ joinedStacks (io (r := m) [] []) S) (halted_io B x)

theorem prepare_run {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hA : A.ComputesInTime f T) (v : Register A B) (x : List Bool) :
    ∃ t, t ≤ 8 * (x.length + T x.length + 1) ∧
      DeterministicRun (advance A B) t
        (config A B (some (.prepare .readInput)) {v with prep := MultitapeTransducer.initial A}
          x [] [] [])
        (config A B (some .sample) {v with prep := MultitapeTransducer.initial A}
          [] (f x) [] []) := by
  obtain ⟨t, ht, hr⟩ := MultitapeTransducer.computer_run A hA x
  have h := deterministic_run (prepLens A B) Label.prepare .sample
    (MultitapeTransducer.program A) (program A B) (fun _ _ ↦ rfl) v (io [] []) hr
  refine ⟨t, ht, ?_⟩
  convert h using 1
  · rfl
  · exact (prepare_initial A B v x).symm
  · exact (prepare_final A B v (f x)).symm

theorem check_run {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hB : B.ComputesInTime f T) (v : Register A B) (x : List Bool) :
    ∃ t, t ≤ 8 * (x.length + T x.length + 1) ∧
      DeterministicRun (advance A B) t
        (config A B (some (.check .readInput)) {v with check := MultitapeTransducer.initial B}
          [] [] x [])
        (config A B (some .readAnswer) {v with check := MultitapeTransducer.initial B}
          [] [] [] (f x)) := by
  obtain ⟨t, ht, hr⟩ := MultitapeTransducer.computer_run B hB x
  have h := deterministic_run_right (checkLens A B) Label.check .readAnswer
    (MultitapeTransducer.program B) (program A B) (fun _ _ ↦ rfl) v (io [] []) hr
  refine ⟨t, ht, ?_⟩
  convert h using 1
  · rfl
  · exact (check_initial A B v x).symm
  · exact (check_final A B v (f x)).symm


end

end Lax253009Proofs.RegisteredBridge.FairTestMachine
