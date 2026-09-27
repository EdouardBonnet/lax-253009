import Lax253009Proofs.RegisteredBridge.FairTestMachine
import Lax253009Proofs.RegisteredBridge.CoinTree

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Lax253009Proofs.RegisteredBridge.FairTestMachine

open Turing PCPFoundation.Complexity FairExecution
open scoped Classical

variable {m n : ℕ} (A : TM m) (B : TM n)

def doubleBits (x : List Bool) : List Bool := x.flatMap fun b ↦ [b, b]

theorem doubleBits_length (x : List Bool) : (doubleBits x).length = 2 * x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [doubleBits, List.flatMap_cons] at *; omega

theorem pair_double (x y : List Bool) : pair x y = doubleBits x ++ false :: true :: y := by
  simp [pair, delimit, doubleBits, List.append_assoc]

theorem doubleBits_snoc (x : List Bool) (b : Bool) :
    (doubleBits (x ++ [b])).reverse = b :: b :: (doubleBits x).reverse := by
  simp [doubleBits, List.flatMap_append]

theorem cleanup {result : List Bool → Option Bool} {T : ℕ → ℕ}
    (hB : B.ComputesInTime (fun z ↦ FiniteEncoding.code (result z)) T)
    (v : Register A B) (prior x : List Bool) :
    ∃ t v', t ≤ 2 * x.length + 2 * prior.length + 6 +
        8 * ((pair prior x).length + T (pair prior x).length + 1) ∧
      DeterministicRun (advance A B) t
        (config A B (some .sample) v (doubleBits prior).reverse (pair [] x) [] [])
        (finalConfig A B v' (result (pair prior x))) := by
  let v₀ := {v with bit := false, more := false}
  let v₁ := {v₀ with check := MultitapeTransducer.initial B}
  have h₀ := DeterministicRun.one (sample_done A B v (doubleBits prior).reverse x)
  have h₁ := copy_run A B {v with bit := true} (true :: false :: (doubleBits prior).reverse) x
  have h₂ := reverse_run A B v₀ (x.reverse ++ true :: false :: (doubleBits prior).reverse) []
  have hw : (x.reverse ++ true :: false :: (doubleBits prior).reverse).reverse ++ [] =
      pair prior x := by
    rw [pair_double]
    simp
  rw [hw] at h₂
  obtain ⟨t, ht, h₃⟩ := check_run A B hB v₀ (pair prior x)
  have h₄ := DeterministicRun.one (read_answer A B v₁ (result (pair prior x)))
  refine ⟨1 + (x.length + 1) + ((x.reverse ++ true :: false :: (doubleBits prior).reverse).length + 1) + t + 1,
    v₁, ?_, (((h₀.trans h₁).trans h₂).trans h₃).trans h₄⟩
  simp only [List.length_append, List.length_reverse, List.length_cons, doubleBits_length]
  omega

def sampleBound (T : ℕ → ℕ) (x : List Bool) (total remaining : ℕ) : ℕ :=
  remaining + 2 * x.length + 2 * total + 6 +
    8 * (2 * total + 2 + x.length + T (2 * total + 2 + x.length) + 1)

/-- An execution tree is exactly the tree of the requested independent
fair bits. All preparation, copying, checking and answer decoding occurs
as deterministic stretches around those choices. -/
theorem sample_execution {result : List Bool → Option Bool} {T : ℕ → ℕ}
    (hB : B.ComputesInTime (fun z ↦ FiniteEncoding.code (result z)) T)
    (x : List Bool) (total : ℕ) :
    ∀ remaining (prior : List Bool) (v : Register A B), remaining + prior.length = total →
    ∃ t, t ≤ sampleBound T x total remaining ∧
      Executes (advance A B) (fun c ↦ output A B c.var) (fun c ↦ c.l = none)
        (config A B (some .sample) v (doubleBits prior).reverse
          (pair (List.replicate remaining false) x) [] [])
        (CoinTree.sample remaining (fun r ↦ result (pair (prior ++ r) x))) t := by
  intro remaining
  induction remaining with
  | zero =>
    intro prior v hlen
    obtain ⟨t, v', ht, hr⟩ := cleanup A B hB v prior x
    have hdone := Executes.done (step := advance A B) (out := fun c ↦ output A B c.var)
      (halt := fun c ↦ c.l = none) (finalConfig A B v' (result (pair prior x)))
      (final_halt A B _ _) (final_stationary A B _ _)
    have he := hdone.prepend hr
    refine ⟨t, ?_, ?_⟩
    · simpa only [sampleBound, Nat.zero_add, ← hlen, pair_length] using ht
    · simpa only [Nat.add_zero, CoinTree.sample, List.append_nil, List.replicate_zero,
        final_output] using he
  | succ remaining ih =>
    intro prior v hlen
    have hlen' (b : Bool) : remaining + (prior ++ [b]).length = total := by
      simp only [List.length_append, List.length_singleton]
      omega
    obtain ⟨t₀, ht₀, h₀⟩ := ih (prior ++ [false]) {v with bit := false} (hlen' false)
    obtain ⟨t₁, ht₁, h₁⟩ := ih (prior ++ [true]) {v with bit := false} (hlen' true)
    have hs (b : Bool) :
        advance A B
          (config A B (some .sample) v (doubleBits prior).reverse
            (pair (List.replicate (remaining + 1) false) x) [] []) b =
        config A B (some .sample) {v with bit := false}
          (doubleBits (prior ++ [b])).reverse (pair (List.replicate remaining false) x) [] [] := by
      rw [sample_step, doubleBits_snoc]
    rw [← hs false] at h₀
    rw [← hs true] at h₁
    have he := Executes.flip
      (config A B (some .sample) v (doubleBits prior).reverse
        (pair (List.replicate (remaining + 1) false) x) [] []) h₀ h₁
    refine ⟨max t₀ t₁ + 1, ?_, ?_⟩
    · simp only [sampleBound] at ht₀ ht₁ ⊢; omega
    · simpa only [CoinTree.sample, List.append_assoc, List.singleton_append] using he


theorem input_config (x : List Bool) :
    (TM2.init buffer x : TM2.Cfg (Alphabet (m := m) (n := n)) Label (Register A B)) =
      config A B (some (.prepare .readInput)) default x [] [] [] := by
  apply MultitapeTransducer.cfg_ext <;> try rfl
  funext k
  cases k with
  | inl k =>
    cases k with
    | inl bit => cases bit <;> simp [TM2.init, config, memory, StackSubroutine.joinedStacks,
        io, buffer, Function.update]
    | inr k => simp [TM2.init, config, memory, StackSubroutine.joinedStacks, io, buffer, Function.update]
  | inr k =>
    cases k with
    | inl bit => cases bit <;> simp [TM2.init, config, memory, StackSubroutine.joinedStacks,
        io, buffer, Function.update]
    | inr k => simp [TM2.init, config, memory, StackSubroutine.joinedStacks, io, buffer, Function.update]

/-- Complete fair-tape execution, including the polynomial-time machines
that compute the tape length and evaluate the encoded test. -/
theorem execution (bits : List Bool → ℕ) (result : List Bool → Option Bool)
    {T₀ T₁ : ℕ → ℕ}
    (hA : A.ComputesInTime
      (fun z ↦ pair (List.replicate (bits z.reverse) false) z.reverse) T₀)
    (hB : B.ComputesInTime
      (fun z ↦ FiniteEncoding.code (result (pair (pairSnd z) (pairFst z)))) T₁)
    (x : List Bool) :
    ∃ t, t ≤ 8 * (x.length + T₀ x.length + 1) + sampleBound T₁ x (bits x) (bits x) ∧
      Executes (advance A B) (fun c ↦ output A B c.var) (fun c ↦ c.l = none)
        (TM2.init buffer x.reverse)
        (CoinTree.sample (bits x) (fun r ↦ result (pair x r))) t := by
  obtain ⟨p, hp, hprep⟩ := prepare_run A B hA default x.reverse
  obtain ⟨s, hs, he⟩ := sample_execution A B hB x (bits x) (bits x) [] default (by simp)
  have hstart : DeterministicRun (advance A B) p (TM2.init buffer x.reverse)
      (config A B (some .sample) default [] (pair (List.replicate (bits x) false) x) [] []) := by
    rw [input_config]
    have hv : {(default : Register A B) with prep := MultitapeTransducer.initial A} = default := rfl
    simpa only [List.reverse_reverse, hv] using hprep
  have hex := he.prepend hstart
  refine ⟨p + s, ?_, ?_⟩
  · simp only [List.length_reverse] at hp
    exact Nat.add_le_add hp hs
  · simpa only [doubleBits, List.flatMap_nil, List.reverse_nil, List.nil_append,
      pairFst_pair, pairSnd_pair] using hex


end Lax253009Proofs.RegisteredBridge.FairTestMachine
