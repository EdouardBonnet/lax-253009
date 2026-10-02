import Lax323828Proofs.RegisteredBridge.ComputableNumbering
import Mathlib.Algebra.BigOperators.Fin

set_option backward.isDefEq.respectTransparency false

namespace Lax323828Proofs.RegisteredBridge.ComputableDigits

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding ComputableNumbering

theorem div_min_power (n b i : ℕ) : n / min (b ^ i) (n + 1) = n / b ^ i := by
  rcases le_total (b ^ i) (n + 1) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, Nat.div_eq_of_lt (Nat.lt_succ_self n), Nat.div_eq_of_lt (by omega)]

/-- A base-b digit can be read without constructing the possibly enormous
power b^i. Capping the denominator above n leaves the quotient unchanged. -/
theorem digit_poly {n b i : Word → ℕ} (hn : UnaryFn n) (hb : UnaryFn b) (hi : UnaryFn i) :
    UnaryFn (fun z ↦ n z / b z ^ i z % b z) :=
  ((hn.div (hb.powMin hi (hn.add (UnaryFn.const 1)))).mod hb).of_eq
    (fun z ↦ by rw [div_min_power])

theorem digit_realizes (b k : Word → ℕ) (hb : UnaryFn b) :
    Realizes (prod (unary (fun z ↦ b z ^ k z)) (unary k)) (unary b)
      (fun z v ↦ (@finFunctionFinEquiv (b z) (k z)).symm v.1 v.2) := by
  have hn := UnaryFn.length (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hi := UnaryFn.length (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have hpoly := digit_poly hn (hb.comp pairFst_mem_FP) hi
  refine ⟨_, hpoly.mem_FP, ?_⟩
  intro z v
  simp only [prod, unary, Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]
  rfl

end Lax323828Proofs.RegisteredBridge.ComputableDigits
