import Lax253009.RandomizedApproximation
import Lax253009.GraphEncoding
import Lax253009Proofs.RegisteredBridge.CliqueGapReduction
import Lax253009Proofs.RegisteredBridge.BoundedErrorTests

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048

namespace Lax253009Proofs.RegisteredBridge.RandomizedApproximationTest

open PCPFoundation.Complexity FiniteEncoding
open Lax434930.PolynomialTime (Word)
open Lax253009 FiniteProbability RandomizedApproximation
open BoundedErrorTests
open scoped Classical BigOperators

theorem weaken {ε θ : ℝ} (hθ : θ ≤ ε) (h : Approximable ε) : Approximable θ := by
  obtain ⟨p, estimate, hpoly, he⟩ := h
  refine ⟨p, estimate, hpoly, fun n hn G ↦ (he n hn G).trans ?_⟩
  apply Lax253009.FiniteProbability.monotone
  intro r hg
  refine ⟨hg.1, hg.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem polynomial_length {g : Word → Word} (hg : g ∈ FP) (p : Polynomial ℕ) :
    UnaryFn (fun z ↦ p.eval (g z).length) := by
  obtain ⟨ruler, hruler, hlen⟩ := Cobham.exists_exact_ruler p
  exact (UnaryFn.length (mem_FP_comp hg hruler)).of_eq (fun z ↦ hlen _)

theorem tape_error (A : Test) (x : Word) (b : Bool) (n : ℕ) (hn : n = A.bits x) :
    probability (fun r : Fin n → Bool ↦ A.answer (pair x (List.ofFn r)) ≠ b) = A.error x b := by
  subst n
  rfl

/-- Compare the randomized integer estimate with an input threshold. Only the
one-bit comparison is repeated; integer outputs retain their binary encoding. -/
noncomputable def comparison (p : Polynomial ℕ) (estimate : Word → ℕ)
    (M : Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate) : Test where
  bits := fun y ↦ p.eval (pairFst y).length
  bits_poly := polynomial_length pairFst_mem_FP p
  answer := fun z ↦ decide ((pairSnd (pairFst z)).length <
    estimate (Lax434930.Certificates.pair (pairFst (pairFst z)) (pairSnd z)))
  answer_poly := by
    have he := mem_FP_comp (registered_pair_mem_FP
      (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP) (encoded_mem_FP M)
    have ht := UnaryFn.length (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
    have hv := UnaryFn.fromBitsLE_min he (ht.add (UnaryFn.const 1))
    apply (FPPred.lt ht hv).of_iff
    intro z
    simp only [Function.comp_apply, from_bits_encode_nat, lt_min_iff,
      Nat.lt_succ_self, and_true, decide_eq_true_eq]

theorem comparison_error (p : Polynomial ℕ) (estimate : Word → ℕ)
    (M : Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate)
    {ε : ℝ} {n : ℕ} (G : Graphs.Graph n) (k : ℕ) (b : Bool)
    (he : (2 / 3 : ℝ) ≤ probability (fun r : Fin (p.eval G.encode.length) → Bool ↦
      Good ε G (estimate (Lax434930.Certificates.pair G.encode (List.ofFn r)))))
    (hsep : ∀ a, Good ε G a → decide (k < a) = b) :
    (comparison p estimate M).error (pair G.encode (List.replicate k false)) b ≤ 1 / 3 := by
  have hm := Lax253009.FiniteProbability.monotone
    (fun r : Fin (p.eval G.encode.length) → Bool ↦
      decide (k < estimate (Lax434930.Certificates.pair G.encode (List.ofFn r))) ≠ b)
    (fun r ↦ ¬ Good ε G (estimate (Lax434930.Certificates.pair G.encode (List.ofFn r))))
    (fun r hr hg ↦ hr (hsep _ hg))
  rw [FairTests.probability_not (fun r : Fin (p.eval G.encode.length) → Bool ↦
    Good ε G (estimate (Lax434930.Certificates.pair G.encode (List.ofFn r))))] at hm
  have hb : probability (fun r : Fin (p.eval G.encode.length) → Bool ↦
      decide (k < estimate (Lax434930.Certificates.pair G.encode (List.ofFn r))) ≠ b) ≤ 1 / 3 := by
    linarith
  rw [← tape_error (comparison p estimate M) _ b (p.eval G.encode.length)
    (by simp [comparison])]
  simpa only [comparison, pairFst_pair, pairSnd_pair, List.length_replicate] using hb

noncomputable def context {ε : ℝ} {L : Language} (R : CliqueGapReduction ε L) (z : Word) : Word :=
  pair (R.graph (pairFst z) (pairSnd z)).encode
    (List.replicate (R.threshold (pairFst z)) false)

@[simp] theorem context_pair {ε : ℝ} {L : Language} (R : CliqueGapReduction ε L)
    (x coins : Word) : context R (pair x coins) =
      pair (R.graph x coins).encode (List.replicate (R.threshold x) false) := by
  unfold context
  rw [pairFst_pair, pairSnd_pair]

theorem context_poly {ε : ℝ} {L : Language} (R : CliqueGapReduction ε L) : context R ∈ FP :=
  mem_FP_pair R.graph_poly ((R.threshold_poly.comp pairFst_mem_FP).replicate_mem_FP false)

noncomputable def compose {ε : ℝ} {L : Language} (R : CliqueGapReduction ε L) (A : Test) : Test where
  bits := fun x ↦ R.bits x + A.bits (context R (pair x []))
  bits_poly := R.bits_poly.add (A.bits_poly.comp
    (mem_FP_comp (mem_FP_pair id_mem_FP (constFn_mem_FP [])) (context_poly R)))
  answer := fun z ↦ A.answer (pair (context R (left R.bits z)) (pairSnd (right R.bits z)))
  answer_poly := A.answer_poly.comp (mem_FP_pair
    (mem_FP_comp (left_poly R.bits_poly) (context_poly R))
    (mem_FP_comp (right_poly R.bits_poly) pairSnd_mem_FP))

theorem compose_error {ε : ℝ} {L : Language} (R : CliqueGapReduction ε L) (A : Test)
    (x : Word) (b : Bool) :
    (compose R A).error x b = probability
      (fun r : (Fin (R.bits x) → Bool) × (Fin (A.bits (context R (pair x []))) → Bool) ↦
        A.answer (pair (context R (pair x (List.ofFn r.1))) (List.ofFn r.2)) ≠ b) := by
  unfold Test.error
  apply finite_probability_equiv (blockEquiv _ _) _ _
  intro r
  simp only [Test.run, compose, left, right, pairFst_pair, pairSnd_pair,
    FairTests.take_block, FairTests.drop_block]
  rfl

theorem compose_in_BPP {ε : ℝ} {L : Language} (R : CliqueGapReduction ε L) (A : Test)
    (hbits : ∀ x coins, A.bits (context R (pair x [])) = A.bits (context R (pair x coins)))
    (hyes : ∀ x ∈ L, ∀ coins, A.error (context R (pair x coins)) true ≤ 1 / 12)
    (hno : ∀ x coins, ¬ R.threshold x ≤ (R.graph x coins).cliqueNumber →
      A.error (context R (pair x coins)) false ≤ 1 / 12) :
    L ∈ Lax666725.RandomizedPolynomialTime.BPP := by
  apply (compose R A).andSelf_in_BPP L
  · intro x hx
    rw [compose_error]
    apply finite_probability_product_bound
      (fun coins r ↦ A.answer (pair (context R (pair x (List.ofFn coins))) (List.ofFn r)) ≠ true)
    intro coins
    rw [tape_error A _ true _ (hbits x (List.ofFn coins))]
    exact hyes x hx _
  · intro x hx
    rw [compose_error]
    let bad := fun coins : Fin (R.bits x) → Bool ↦
      R.threshold x ≤ (R.graph x (List.ofFn coins)).cliqueNumber
    let err := fun r : (Fin (R.bits x) → Bool) × (Fin (A.bits (context R (pair x []))) → Bool) ↦
      A.answer (pair (context R (pair x (List.ofFn r.1))) (List.ofFn r.2)) ≠ false
    have hb : probability (fun r : (Fin (R.bits x) → Bool) ×
        (Fin (A.bits (context R (pair x []))) → Bool) ↦ bad r.1) ≤ 1 / 3 := by
      rw [finite_probability_product (fun a (_ : Fin (A.bits (context R (pair x []))) → Bool) ↦ bad a)]
      simp_rw [finite_probability_indicator, Fintype.expect_const]
      simpa only [finite_probability_indicator] using R.sound x hx
    have hg : probability (fun r ↦ ¬ bad r.1 ∧ err r) ≤ 1 / 12 := by
      apply finite_probability_product_bound (fun a b ↦ ¬ bad a ∧ err (a, b))
      intro coins
      by_cases hc : bad coins
      · simp [hc, finite_probability_indicator]
      · simp only [hc, not_false_eq_true, true_and]
        rw [tape_error A _ false _ (hbits x (List.ofFn coins))]
        exact hno x _ hc
    have hm := Lax253009.FiniteProbability.monotone err
      (fun r ↦ bad r.1 ∨ (¬ bad r.1 ∧ err r)) (fun r hr ↦ by tauto)
    have hu := Lax253009.FiniteProbability.union_bound
      (fun r : (Fin (R.bits x) → Bool) × (Fin (A.bits (context R (pair x []))) → Bool) ↦ bad r.1)
      (fun r ↦ ¬ bad r.1 ∧ err r)
    exact (hm.trans hu).trans (by linarith)

/-- Combine the approximation algorithm's independent coins with the reduction
coins. Successful estimates classify every complete graph and every graph
outside the reduction's exceptional soundness event. -/
theorem randomized_approximation_in_BPP {ε : ℝ}
    (h : Approximable ε) (L : Language) (R : CliqueGapReduction ε L) :
    L ∈ Lax666725.RandomizedPolynomialTime.BPP := by
  obtain ⟨p, estimate, ⟨M⟩, he⟩ := h
  let A := (comparison p estimate M).boost
  have hbits (x coins : Word) : A.bits (context R (pair x [])) = A.bits (context R (pair x coins)) := by
    simp only [A, Test.boost_bits, comparison, context, pairFst_pair, pairSnd_pair,
      Lax253009.GraphEncoding.encoding_length]
  have hyes (x : Word) (hx : x ∈ L) (coins : Word) :
      A.error (context R (pair x coins)) true ≤ 1 / 12 := by
    apply Test.boost_error
    rw [context_pair]
    apply comparison_error p estimate M (R.graph x coins) (R.threshold x) true
      (he _ (R.nonempty x) _)
    intro a ha
    apply decide_eq_true
    have hgap := R.complete x hx coins
    have hpow := Real.rpow_nonneg (Nat.cast_nonneg (R.size x)) (1 - ε)
    by_contra hn
    have hle : (a : ℝ) ≤ R.threshold x := by exact_mod_cast Nat.le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_left hle hpow
    exact (not_lt_of_ge (ha.2.trans hm)) hgap
  have hno (x coins : Word) (hg : ¬ R.threshold x ≤ (R.graph x coins).cliqueNumber) :
      A.error (context R (pair x coins)) false ≤ 1 / 12 := by
    apply Test.boost_error
    rw [context_pair]
    apply comparison_error p estimate M (R.graph x coins) (R.threshold x) false
      (he _ (R.nonempty x) _)
    intro a ha
    apply decide_eq_false
    have hsmall := Nat.lt_of_not_ge hg
    exact Nat.not_lt_of_ge (ha.1.trans hsmall.le)
  exact compose_in_BPP R A hbits hyes hno

end Lax253009Proofs.RegisteredBridge.RandomizedApproximationTest
