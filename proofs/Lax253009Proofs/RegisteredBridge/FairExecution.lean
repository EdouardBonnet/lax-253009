import Lax253009Proofs.FiniteProbability
import Mathlib.Data.List.OfFn

set_option backward.isDefEq.respectTransparency false

namespace Lax253009Proofs.RegisteredBridge.FairExecution

open Lax253009.FiniteProbability
open scoped BigOperators Classical

variable {α β γ : Type}

def splitCoins (n : ℕ) : (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun r := (r 0, Fin.tail r)
  invFun p := Fin.cons p.1 p.2
  left_inv r := by funext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
  right_inv p := by cases p; rfl

/-- Exact expectation after a fixed number of independent fair choices. -/
noncomputable def average (step : α → Bool → α) (value : α → ℝ) : ℕ → α → ℝ
  | 0, a => value a
  | n + 1, a => (average step value n (step a false) + average step value n (step a true)) / 2

theorem average_eq_expect (step : α → Bool → α) (value : α → ℝ) (n : ℕ) (a : α) :
    average step value n a = 𝔼 r : Fin n → Bool, value ((List.ofFn r).foldl step a) := by
  induction n generalizing a with
  | zero => simp [average]
  | succ n ih =>
    have he : (𝔼 r : Fin (n + 1) → Bool, value ((List.ofFn r).foldl step a)) =
        𝔼 p : Bool × (Fin n → Bool), value ((List.ofFn p.2).foldl step (step a p.1)) := by
      apply Fintype.expect_equiv (splitCoins n)
      intro r
      simp only [splitCoins, Equiv.coe_fn_mk, List.ofFn_succ, List.foldl_cons]
      rfl
    have hp : (𝔼 p : Bool × (Fin n → Bool), value ((List.ofFn p.2).foldl step (step a p.1))) =
        𝔼 b : Bool, 𝔼 r : Fin n → Bool, value ((List.ofFn r).foldl step (step a b)) := by
      rw [← Finset.expect_product', Finset.univ_product_univ]
    rw [he, hp]
    simp_rw [← ih]
    rw [Fintype.expect_eq_sum_div_card]
    simp [average, Fintype.sum_bool, add_comm]

theorem average_indicator (step : α → Bool → α) (P : α → Prop) (n : ℕ) (a : α) :
    average step (fun b ↦ if P b then 1 else 0) n a =
      probability (fun r : Fin n → Bool ↦ P ((List.ofFn r).foldl step a)) := by
  rw [average_eq_expect, finite_probability_indicator]

theorem average_stationary (step : α → Bool → α) (value : α → ℝ)
    (a : α) (ha : ∀ b, step a b = a) (n : ℕ) : average step value n a = value a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [average, ha, ih]; ring

/-- A stretch of administrative transitions that never uses its coin. -/
inductive DeterministicRun (step : α → Bool → α) : ℕ → α → α → Prop
  | zero (a : α) : DeterministicRun step 0 a a
  | cons {n : ℕ} {a b c : α} :
      (∀ bit, step a bit = b) → DeterministicRun step n b c → DeterministicRun step (n + 1) a c

theorem DeterministicRun.one {step : α → Bool → α} {a b : α}
    (h : ∀ bit, step a bit = b) : DeterministicRun step 1 a b := .cons h (.zero b)

theorem DeterministicRun.trans {step : α → Bool → α} {a b c : α} {n m : ℕ}
    (h : DeterministicRun step n a b) (h' : DeterministicRun step m b c) :
    DeterministicRun step (n + m) a c := by
  induction h with
  | zero => simpa only [Nat.zero_add] using h'
  | cons hs h ih => simpa only [Nat.add_right_comm] using DeterministicRun.cons hs (ih h')

theorem DeterministicRun.of_step_eq {step : α → Bool → α} {a a' b : α} {n : ℕ}
    (h : DeterministicRun step n a b) (hn : 0 < n)
    (he : ∀ bit, step a' bit = step a bit) : DeterministicRun step n a' b := by
  cases h with
  | zero => omega
  | cons hs ht => exact .cons (fun bit ↦ (he bit).trans (hs bit)) ht

theorem DeterministicRun.average_eq {step : α → Bool → α} {n : ℕ} {a b : α}
    (h : DeterministicRun step n a b) (value : α → ℝ) (m : ℕ) :
    average step value (n + m) a = average step value m b := by
  induction h with
  | zero => simp only [Nat.zero_add]
  | cons hs h ih =>
    rw [Nat.add_right_comm, average, hs, hs, ih]
    ring

inductive Tree (α : Type)
  | leaf : α → Tree α
  | flip : Tree α → Tree α → Tree α

noncomputable def Tree.mean (value : α → ℝ) : Tree α → ℝ
  | .leaf a => value a
  | .flip a b => (a.mean value + b.mean value) / 2

/-- A bounded execution certificate permits deterministic administrative
steps between genuine random choices. Terminal configurations are absorbing. -/
inductive Executes (step : β → Bool → β) (out : β → α) (halt : β → Prop) : β → Tree α → ℕ → Prop
  | done (b : β) (hh : halt b) (hb : ∀ bit, step b bit = b) : Executes step out halt b (.leaf (out b)) 0
  | delay {b c : β} {tree : Tree α} {n : ℕ} :
      (∀ bit, step b bit = c) → Executes step out halt c tree n → Executes step out halt b tree (n + 1)
  | flip (b : β) {left right : Tree α} {n m : ℕ} :
      Executes step out halt (step b false) left n → Executes step out halt (step b true) right m →
      Executes step out halt b (.flip left right) (max n m + 1)

theorem Executes.average_eq {step : β → Bool → β} {out : β → α} {halt : β → Prop} {b : β} {tree : Tree α} {n : ℕ}
    (h : Executes step out halt b tree n) (value : α → ℝ) (k : ℕ) (hk : n ≤ k) :
    average step (value ∘ out) k b = tree.mean value := by
  induction h generalizing k with
  | done b hh hb => exact average_stationary step (value ∘ out) b hb k
  | @delay b c tree n hs h ih =>
    cases k with
    | zero => omega
    | succ k =>
      simp only [average, hs, ih k (by omega)]
      ring
  | @flip b left right n m h₀ h₁ ih₀ ih₁ =>
    cases k with
    | zero => omega
    | succ k =>
      rw [average, ih₀ k (by omega), ih₁ k (by omega)]
      rfl

theorem Executes.prepend {step : β → Bool → β} {out : β → α} {halt : β → Prop} {a b : β}
    {tree : Tree α} {n m : ℕ} (h : DeterministicRun step n a b)
    (e : Executes step out halt b tree m) : Executes step out halt a tree (n + m) := by
  induction h with
  | zero => simpa only [Nat.zero_add] using e
  | cons hs h ih => simpa only [Nat.add_right_comm] using Executes.delay hs (ih e)

theorem fold_stationary (step : β → Bool → β) (b : β) (hb : ∀ bit, step b bit = b)
    (coins : List Bool) : coins.foldl step b = b := by
  induction coins with
  | nil => rfl
  | cons bit coins ih => simpa only [List.foldl_cons, hb] using ih

theorem Executes.halts {step : β → Bool → β} {out : β → α} {halt : β → Prop}
    {b : β} {tree : Tree α} {n : ℕ} (h : Executes step out halt b tree n)
    (k : ℕ) (hk : n ≤ k) (r : Fin k → Bool) : halt ((List.ofFn r).foldl step b) := by
  induction h generalizing k with
  | done b hh hb => simpa only [fold_stationary step b hb] using hh
  | @delay b c tree n hs h ih =>
    cases k with
    | zero => omega
    | succ k =>
      simp only [List.ofFn_succ, List.foldl_cons, hs]
      exact ih k (by omega) (Fin.tail r)
  | @flip b left right n m h₀ h₁ ih₀ ih₁ =>
    cases k with
    | zero => omega
    | succ k =>
      cases hr : r 0
      · simp only [List.ofFn_succ, List.foldl_cons, hr]
        exact ih₀ k (by omega) (Fin.tail r)
      · simp only [List.ofFn_succ, List.foldl_cons, hr]
        exact ih₁ k (by omega) (Fin.tail r)

theorem executes_of_halts (step : β → Bool → β) (out : β → α) (halt : β → Prop)
    (hstop : ∀ b, halt b → ∀ bit, step b bit = b) (n : ℕ) (b : β)
    (h : ∀ r : Fin n → Bool, halt ((List.ofFn r).foldl step b)) :
    ∃ tree, Executes step out halt b tree n := by
  induction n generalizing b with
  | zero =>
    have hb : halt b := by simpa using h (fun i ↦ Fin.elim0 i)
    exact ⟨.leaf (out b), .done b hb (hstop b hb)⟩
  | succ n ih =>
    have hc (bit : Bool) (r : Fin n → Bool) :
        halt ((List.ofFn r).foldl step (step b bit)) := by
      simpa only [List.ofFn_succ, List.foldl_cons, Fin.cons_zero, Fin.cons_succ, Fin.tail_cons]
        using h (Fin.cons bit r)
    obtain ⟨left, hl⟩ := ih (step b false) (hc false)
    obtain ⟨right, hr⟩ := ih (step b true) (hc true)
    exact ⟨.flip left right, by simpa only [max_self] using Executes.flip b hl hr⟩

/-- Replace one random source step by a target coin step followed by a
bounded deterministic computation. Equal leaf outputs give equal exact
probabilities, even when the administrative time depends on the branch. -/
theorem simulate_tree (source : β → Bool → β) (target : γ → Bool → γ)
    (sourceOut : β → α) (targetOut : γ → α) (sourceHalt : β → Prop) (targetHalt : γ → Prop)
    (R : β → γ → Prop) (C : ℕ)
    (hstop : ∀ b c, R b c → sourceHalt b →
      targetHalt c ∧ (∀ bit, target c bit = c) ∧ sourceOut b = targetOut c)
    (hstep : ∀ b c, R b c → ∀ bit, ∃ d n, n < C ∧
      DeterministicRun target n (target c bit) d ∧ R (source b bit) d)
    {b : β} {tree : Tree α} {n : ℕ} (e : Executes source sourceOut sourceHalt b tree n) :
    ∀ c, R b c → ∃ m tree', m ≤ C * n ∧ Executes target targetOut targetHalt c tree' m ∧
      ∀ value : α → ℝ, tree'.mean value = tree.mean value := by
  induction e with
  | done b hh hb =>
    intro c hc
    obtain ⟨hcHalt, hcstop, he⟩ := hstop b c hc hh
    exact ⟨0, .leaf (targetOut c), by simp, Executes.done c hcHalt hcstop, fun value ↦ by
      simp only [Tree.mean, he]⟩
  | @delay b d tree n hs h ih =>
    intro c hc
    obtain ⟨d₀, n₀, hn₀, hd₀, hr₀⟩ := hstep b c hc false
    obtain ⟨d₁, n₁, hn₁, hd₁, hr₁⟩ := hstep b c hc true
    obtain ⟨m₀, t₀, hm₀, he₀, hp₀⟩ := ih d₀ (hs false ▸ hr₀)
    obtain ⟨m₁, t₁, hm₁, he₁, hp₁⟩ := ih d₁ (hs true ▸ hr₁)
    refine ⟨max (n₀ + m₀) (n₁ + m₁) + 1, .flip t₀ t₁, ?_,
      Executes.flip c (he₀.prepend hd₀) (he₁.prepend hd₁), ?_⟩
    · rw [Nat.mul_succ]; omega
    · intro value
      simp only [Tree.mean, hp₀, hp₁]
      ring
  | @flip b left right n m h₀ h₁ ih₀ ih₁ =>
    intro c hc
    obtain ⟨d₀, n₀, hn₀, hd₀, hr₀⟩ := hstep b c hc false
    obtain ⟨d₁, n₁, hn₁, hd₁, hr₁⟩ := hstep b c hc true
    obtain ⟨m₀, t₀, hm₀, he₀, hp₀⟩ := ih₀ d₀ hr₀
    obtain ⟨m₁, t₁, hm₁, he₁, hp₁⟩ := ih₁ d₁ hr₁
    refine ⟨max (n₀ + m₀) (n₁ + m₁) + 1, .flip t₀ t₁, ?_,
      Executes.flip c (he₀.prepend hd₀) (he₁.prepend hd₁), ?_⟩
    · have hmax₀ := Nat.mul_le_mul_left C (Nat.le_max_left n m)
      have hmax₁ := Nat.mul_le_mul_left C (Nat.le_max_right n m)
      rw [Nat.mul_succ]
      omega
    · intro value
      simp only [Tree.mean, hp₀, hp₁]

/-- The simulation preserves every output-event probability and proves the
target's worst-case clock, including all branches and unused terminal bits. -/
theorem uniform_simulation (source : β → Bool → β) (target : γ → Bool → γ)
    (sourceOut : β → α) (targetOut : γ → α) (sourceHalt : β → Prop) (targetHalt : γ → Prop)
    (R : β → γ → Prop) (C : ℕ)
    (hsource : ∀ b, sourceHalt b → ∀ bit, source b bit = b)
    (hstop : ∀ b c, R b c → sourceHalt b →
      targetHalt c ∧ (∀ bit, target c bit = c) ∧ sourceOut b = targetOut c)
    (hstep : ∀ b c, R b c → ∀ bit, ∃ d n, n < C ∧
      DeterministicRun target n (target c bit) d ∧ R (source b bit) d)
    (b : β) (c : γ) (hc : R b c) (n k : ℕ) (hk : C * n ≤ k)
    (hn : ∀ r : Fin n → Bool, sourceHalt ((List.ofFn r).foldl source b)) :
    (∀ r : Fin k → Bool, targetHalt ((List.ofFn r).foldl target c)) ∧
    (∀ P : α → Prop,
      probability (fun r : Fin k → Bool ↦ P (targetOut ((List.ofFn r).foldl target c))) =
      probability (fun r : Fin n → Bool ↦ P (sourceOut ((List.ofFn r).foldl source b)))) := by
  obtain ⟨tree, ht⟩ := executes_of_halts source sourceOut sourceHalt hsource n b hn
  obtain ⟨m, tree', hm, he, hp⟩ := simulate_tree source target sourceOut targetOut sourceHalt
    targetHalt R C hstop hstep ht c hc
  refine ⟨he.halts k (hm.trans hk), fun P ↦ ?_⟩
  rw [← average_indicator target (fun d ↦ P (targetOut d)) k c,
    ← average_indicator source (fun a ↦ P (sourceOut a)) n b]
  exact (he.average_eq (fun a ↦ if P a then 1 else 0) k (hm.trans hk)).trans
    ((hp _).trans (ht.average_eq _ n le_rfl).symm)

end Lax253009Proofs.RegisteredBridge.FairExecution
