import Lax253009Proofs.RegisteredBridge.CliqueGapReduction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax253009Proofs.RegisteredBridge

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding
open Lax253009 FiniteProbability
open scoped Classical

/-- A clique approximation supplies, for every registered NP language, a
uniform polynomial-time test of an input and a fair random tape. Members
pass for every tape and nonmembers pass with probability at most one third.
The remaining model conversion must implement this test by a registered
probabilistic procedure. -/
theorem approximation_random_test (F : FinBase) (hd : 1 < F.deg)
    (ε : ℝ) (hε : 0 < ε) (happrox : Approximation.Approximable ε) :
    ∀ L ∈ Lax434930.NondeterministicPolynomialTime.NP,
      ∃ b : Word → ℕ, UnaryFn b ∧ ∃ D : Word → Prop, FPPred D ∧
        (∀ x ∈ L, ∀ coins : Fin (b x) → Bool, D (pair x (List.ofFn coins))) ∧
        (∀ x ∉ L, probability (fun coins : Fin (b x) → Bool ↦ D (pair x (List.ofFn coins))) ≤ 1 / 3) := by
  let θ := min ε 1
  have hθ : 0 < θ := lt_min hε zero_lt_one
  obtain ⟨estimate, ⟨M⟩, he⟩ := approximation_weaken (min_le_left ε 1) happrox
  intro L hL
  obtain ⟨R⟩ := clique_gap_reduction F hd θ hθ (min_le_right _ _) L hL
  let D := fun z ↦ R.threshold (pairFst z) <
    estimate (R.graph (pairFst z) (pairSnd z)).encode
  have hD (x coins : Word) : D (pair x coins) ↔
      R.threshold x < estimate (R.graph x coins).encode := by
    change R.threshold (pairFst (pair x coins)) <
      estimate (R.graph (pairFst (pair x coins)) (pairSnd (pair x coins))).encode ↔ _
    rw [pairFst_pair, pairSnd_pair]
  have hpoly : FPPred D := by
    have henc := mem_FP_comp R.graph_poly (encoded_mem_FP M)
    have ht := R.threshold_poly.comp pairFst_mem_FP
    have hv := UnaryFn.fromBitsLE_min henc (ht.add (UnaryFn.const 1))
    apply (FPPred.lt ht hv).of_iff
    intro z
    simp only [D, Function.comp_apply, from_bits_encode_nat, lt_min_iff,
      Nat.lt_succ_self, and_true]
  refine ⟨R.bits, R.bits_poly, D, hpoly, ?_, ?_⟩
  · intro x hx coins
    apply (hD x (List.ofFn coins)).mpr
    have hlarge := R.complete x hx (List.ofFn coins)
    have hhi := (he _ (R.nonempty x) (R.graph x (List.ofFn coins))).2
    by_contra hn
    have hle : (estimate (R.graph x (List.ofFn coins)).encode : ℝ) ≤ R.threshold x := by
      exact_mod_cast Nat.le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_left hle
      (Real.rpow_nonneg (Nat.cast_nonneg (R.size x)) (1 - θ))
    exact (not_lt_of_ge (hhi.trans hm)) hlarge
  · intro x hx
    apply le_trans (Lax253009.FiniteProbability.monotone _ _ ?_) (R.sound x hx)
    intro coins hcoin
    exact (Nat.le_of_lt ((hD x (List.ofFn coins)).mp hcoin)).trans
      (he _ (R.nonempty x) (R.graph x (List.ofFn coins))).1

end Lax253009Proofs.RegisteredBridge
