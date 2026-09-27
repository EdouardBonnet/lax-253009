import Lax253009Proofs.RegisteredBridge.NPApproximationTest
import Lax253009Proofs.RegisteredBridge.CertificateDecoder
import Lax253009Proofs.RegisteredBridge.MultitapeBridge
import Lax253009Proofs.PCPFoundation.Classes.FiniteCounting
import Lax666725.ZeroError

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax253009Proofs.RegisteredBridge

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding
open Lax253009.FiniteProbability
open scoped Classical BigOperators

namespace FairTests

/-- A polynomial-time predicate with a uniformly generated, polynomially
bounded fair random tape, perfect completeness, and one-sided error. -/
structure CoTest (L : Language) where
  bits : Word → ℕ
  bits_poly : UnaryFn bits
  accepts : Word → Prop
  accepts_poly : FPPred accepts
  complete : ∀ x ∈ L, ∀ r : Fin (bits x) → Bool, accepts (pair x (List.ofFn r))
  sound : ∀ x ∉ L,
    probability (fun r : Fin (bits x) → Bool ↦ accepts (pair x (List.ofFn r))) ≤ 1 / 3

/-- The finite-coin interface required of the final registered compiler. -/
structure ZeroTest (L : Language) where
  bits : Word → ℕ
  bits_poly : UnaryFn bits
  result : Word → Option Bool
  result_poly : (fun z ↦ code (result z)) ∈ FP
  correct : ∀ x (r : Fin (bits x) → Bool) b,
    result (pair x (List.ofFn r)) = some b → Lax666725.ProbabilisticMachines.Correct L x b
  success : ∀ x,
    (2 / 3 : ℝ) ≤ probability (fun r : Fin (bits x) → Bool ↦
      (result (pair x (List.ofFn r))).isSome = true)

theorem probability_not {α : Type} [Fintype α] [Nonempty α] (P : α → Prop) :
    probability (fun a ↦ ¬ P a) = 1 - probability P := by
  have h : probability P + probability (fun a ↦ ¬ P a) = 1 := by
    simp_rw [finite_probability_indicator]
    rw [← Finset.expect_add_distrib]
    calc
      _ = 𝔼 _a : α, (1 : ℝ) := by
        apply Finset.expect_congr rfl
        intro a _
        by_cases ha : P a <;> simp [ha]
      _ = _ := Fintype.expect_const _
  linarith

theorem CoTest.rejects {L : Language} (A : CoTest L) {x : Word} (hx : x ∉ L) :
    ∃ r : Fin (A.bits x) → Bool, ¬ A.accepts (pair x (List.ofFn r)) := by
  by_contra! h
  have hs := A.sound x hx
  have he : probability (fun r : Fin (A.bits x) → Bool ↦ A.accepts (pair x (List.ofFn r))) = 1 := by
    simp [finite_probability_indicator, h]
  rw [he] at hs
  norm_num at hs

/-- A rejection tape is an NP certificate for the complement language.
The verifier is transferred to the registered deterministic class. -/
theorem CoTest.complement_in_NP {L : Language} (A : CoTest L) :
    Lᶜ ∈ Lax434930.NondeterministicPolynomialTime.NP := by
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP A.bits_poly.mem_FP
  have hb (x : Word) : A.bits x ≤ p.eval x.length := by simpa using hp x
  let first := CertificateDecoder.first
  let second := CertificateDecoder.second
  let V : Set Word := {z | (second z).length = A.bits (first z) ∧
    ¬ A.accepts (pair (first z) (second z))}
  have hV : V ∈ Lax434930.PolynomialTime.P := by
    apply P_subset_registered_P
    exact ((FPPred.eq (UnaryFn.length CertificateDecoder.second_mem_FP)
      (A.bits_poly.comp CertificateDecoder.first_mem_FP)).and
        (A.accepts_poly.not.comp (mem_FP_pair CertificateDecoder.first_mem_FP
          CertificateDecoder.second_mem_FP))).mem_P
  have hpair (x y : Word) : Lax434930.Certificates.pair x y ∈ V ↔
      y.length = A.bits x ∧ ¬ A.accepts (pair x y) := by
    simp only [V, Set.mem_setOf_eq, first, second, CertificateDecoder.first_pair,
      CertificateDecoder.second_pair]
  refine ⟨V, hV, p, fun x ↦ ?_⟩
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := A.rejects hx
    exact ⟨List.ofFn r, by simpa using hb x, (hpair x _).mpr ⟨by simp, hr⟩⟩
  · rintro ⟨y, _, hy⟩
    obtain ⟨hlen, hrej⟩ := (hpair x y).mp hy
    let r : Fin (A.bits x) → Bool := fun i ↦ y[i.val]'(by omega)
    have hr : List.ofFn r = y := by
      apply List.ext_getElem
      · simpa using hlen.symm
      · intro i hi hj; simp [r]
    intro hx
    exact hrej (hr ▸ A.complete x hx r)

theorem take_block (a b : ℕ) (r : Fin (a + b) → Bool) :
    (List.ofFn r).take a = List.ofFn (blockFst a b r) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_take, List.getElem_ofFn]
    rfl

theorem drop_block (a b : ℕ) (r : Fin (a + b) → Bool) :
    (List.ofFn r).drop a = List.ofFn (blockSnd a b r) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_drop, List.getElem_ofFn]
    rfl

theorem probability_first (a b : ℕ) (P : (Fin a → Bool) → Prop) :
    probability (fun r : Fin (a + b) → Bool ↦ P (blockFst a b r)) = probability P := by
  unfold blockFst
  rw [finite_probability_equiv (blockEquiv a b) _ (fun z ↦ P z.1) (fun _ ↦ Iff.rfl)]
  rw [finite_probability_product (fun (x : Fin a → Bool) (_ : Fin b → Bool) ↦ P x)]
  simp_rw [finite_probability_indicator, Fintype.expect_const]

theorem probability_second (a b : ℕ) (P : (Fin b → Bool) → Prop) :
    probability (fun r : Fin (a + b) → Bool ↦ P (blockSnd a b r)) = probability P := by
  unfold blockSnd
  rw [finite_probability_equiv (blockEquiv a b) _ (fun z ↦ P z.2) (fun _ ↦ Iff.rfl)]
  rw [finite_probability_product (fun (_ : Fin a → Bool) (y : Fin b → Bool) ↦ P y),
    Fintype.expect_const]

noncomputable def combine {L : Language} (A : CoTest L) (B : CoTest Lᶜ) (z : Word) : Option Bool :=
  if ¬ A.accepts (pair (pairFst z) ((pairSnd z).take (A.bits (pairFst z)))) then some false
  else if ¬ B.accepts (pair (pairFst z) ((pairSnd z).drop (A.bits (pairFst z)))) then some true
  else none

theorem combine_poly {L : Language} (A : CoTest L) (B : CoTest Lᶜ) :
    (fun z ↦ code (combine A B z)) ∈ FP := by
  have ht := Cobham.takeLenFn_mem_FP (A.bits_poly.comp pairFst_mem_FP).mem_FP pairSnd_mem_FP
  have hd := dropLenFn_mem_FP (A.bits_poly.comp pairFst_mem_FP).mem_FP pairSnd_mem_FP
  simp only [List.length_replicate] at ht hd
  have hA := A.accepts_poly.not.comp (mem_FP_pair pairFst_mem_FP ht)
  have hB := B.accepts_poly.not.comp (mem_FP_pair pairFst_mem_FP hd)
  have hconst (v : Option Bool) : (fun _ : Word ↦ code v) ∈ FP :=
    CobhamFP_subset_FP (Cobham.const (code v))
  apply mem_FP_of_eq
    (hA.ite_mem_FP (hconst (some false)) (hB.ite_mem_FP (hconst (some true)) (hconst none)))
  intro z
  simp only [combine, Function.comp_apply]
  split_ifs <;> rfl

theorem combine_coins {L : Language} (A : CoTest L) (B : CoTest Lᶜ)
    (x : Word) (r : Fin (A.bits x + B.bits x) → Bool) :
    combine A B (pair x (List.ofFn r)) =
      if ¬ A.accepts (pair x (List.ofFn (blockFst (A.bits x) (B.bits x) r))) then some false
      else if ¬ B.accepts (pair x (List.ofFn (blockSnd (A.bits x) (B.bits x) r))) then some true
      else none := by
  simp only [combine, pairFst_pair, pairSnd_pair, take_block, drop_block]

/-- Complementary one-sided tests give a zero-error test with success at
least two thirds. Neither the correctness nor success argument assumes
independence between the decisions. -/
noncomputable def zeroTest {L : Language} (A : CoTest L) (B : CoTest Lᶜ) : ZeroTest L where
  bits := fun x ↦ A.bits x + B.bits x
  bits_poly := A.bits_poly.add B.bits_poly
  result := combine A B
  result_poly := combine_poly A B
  correct := by
    intro x r v hv
    rw [combine_coins] at hv
    by_cases hx : x ∈ L
    · have ha := A.complete x hx (blockFst (A.bits x) (B.bits x) r)
      simp only [ha, not_true_eq_false, if_false] at hv
      split_ifs at hv with hb
      · have hv' : v = true := Option.some.inj hv.symm
        simp [Lax666725.ProbabilisticMachines.Correct, hv', hx]
    · have hb := B.complete x hx (blockSnd (A.bits x) (B.bits x) r)
      simp only [hb, not_true_eq_false, if_false] at hv
      split_ifs at hv with ha
      · have hv' : v = false := Option.some.inj hv.symm
        simp [Lax666725.ProbabilisticMachines.Correct, hv', hx]
  success := by
    intro x
    by_cases hx : x ∈ L
    · have hs := B.sound x (by simpa using hx)
      have hrej : (2 / 3 : ℝ) ≤ probability (fun r : Fin (B.bits x) → Bool ↦
          ¬ B.accepts (pair x (List.ofFn r))) := by rw [probability_not]; linarith
      rw [← probability_second (A.bits x) (B.bits x)] at hrej
      refine hrej.trans (finite_probability_mono _ _ ?_)
      intro r hr
      rw [combine_coins]
      by_cases ha : A.accepts (pair x (List.ofFn (blockFst (A.bits x) (B.bits x) r))) <;> simp [hr, ha]
    · have hs := A.sound x hx
      have hrej : (2 / 3 : ℝ) ≤ probability (fun r : Fin (A.bits x) → Bool ↦
          ¬ A.accepts (pair x (List.ofFn r))) := by rw [probability_not]; linarith
      rw [← probability_first (A.bits x) (B.bits x)] at hrej
      refine hrej.trans (finite_probability_mono _ _ ?_)
      intro r hr
      rw [combine_coins]
      simp [hr]

end FairTests

theorem approximation_zero_test (F : PCPFoundation.Complexity.FinBase) (hd : 1 < F.deg)
    (ε : ℝ) (hε : 0 < ε) (happrox : Lax253009.Approximation.Approximable ε) :
    ∀ L ∈ Lax434930.NondeterministicPolynomialTime.NP, Nonempty (FairTests.ZeroTest L) := by
  have htest : ∀ L ∈ Lax434930.NondeterministicPolynomialTime.NP,
      Nonempty (FairTests.CoTest L) := by
    intro L hL
    obtain ⟨b, hb, D, hD, hc, hs⟩ := approximation_random_test F hd ε hε happrox L hL
    exact ⟨⟨b, hb, D, hD, hc, hs⟩⟩
  intro L hL
  obtain ⟨A⟩ := htest L hL
  obtain ⟨B⟩ := htest Lᶜ A.complement_in_NP
  exact ⟨FairTests.zeroTest A B⟩

end Lax253009Proofs.RegisteredBridge
