import Lax253009Proofs.RegisteredBridge.FairExecution

set_option backward.isDefEq.respectTransparency false

namespace Lax253009Proofs.RegisteredBridge.CoinTree

open FairExecution
open scoped BigOperators Classical

variable {α : Type}

def sample : ℕ → (List Bool → α) → FairExecution.Tree α
  | 0, f => .leaf (f [])
  | n + 1, f => .flip (sample n (fun r ↦ f (false :: r))) (sample n (fun r ↦ f (true :: r)))

theorem mean_eq_expect (n : ℕ) (f : List Bool → α) (value : α → ℝ) :
    (sample n f).mean value = 𝔼 r : Fin n → Bool, value (f (List.ofFn r)) := by
  induction n generalizing f with
  | zero => simp [sample, Tree.mean]
  | succ n ih =>
    have he : (𝔼 r : Fin (n + 1) → Bool, value (f (List.ofFn r))) =
        𝔼 p : Bool × (Fin n → Bool), value (f (p.1 :: List.ofFn p.2)) := by
      apply Fintype.expect_equiv (splitCoins n)
      intro r
      simp only [splitCoins, Equiv.coe_fn_mk, List.ofFn_succ]
      rfl
    have hp : (𝔼 p : Bool × (Fin n → Bool), value (f (p.1 :: List.ofFn p.2))) =
        𝔼 b : Bool, 𝔼 r : Fin n → Bool, value (f (b :: List.ofFn r)) := by
      rw [← Finset.expect_product', Finset.univ_product_univ]
    rw [he, hp]
    rw [sample, Tree.mean, ih, ih]
    simp only [Fintype.expect_eq_sum_div_card, Fintype.sum_bool, Fintype.card_bool]
    ring

theorem indicator (n : ℕ) (f : List Bool → α) (P : α → Prop) :
    (sample n f).mean (fun a ↦ if P a then 1 else 0) =
      Lax253009.FiniteProbability.probability (fun r : Fin n → Bool ↦ P (f (List.ofFn r))) := by
  rw [mean_eq_expect, finite_probability_indicator]

end Lax253009Proofs.RegisteredBridge.CoinTree
