import Lax323828.MajorityAmplification
import Lax323828Proofs.RegisteredBridge.FairTestCompiler
import Lax666725.RandomizedPolynomialTime

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Lax323828Proofs.RegisteredBridge.BoundedErrorTests

open PCPFoundation.Complexity FiniteEncoding
open Lax434930.PolynomialTime (Word)
open Lax323828.FiniteProbability
open Lax323828.FreshBitSampling Lax323828.MajorityAmplification
open scoped Classical BigOperators

structure Test where
  bits : Word → ℕ
  bits_poly : UnaryFn bits
  answer : Word → Bool
  answer_poly : FPPred (fun z ↦ answer z = true)

def Test.run (A : Test) (x : Word) (r : Fin (A.bits x) → Bool) : Bool :=
  A.answer (pair x (List.ofFn r))

noncomputable def Test.error (A : Test) (x : Word) (b : Bool) : ℝ :=
  probability (fun r ↦ A.run x r ≠ b)

def left (bits : Word → ℕ) (z : Word) : Word :=
  pair (pairFst z) ((pairSnd z).take (bits (pairFst z)))

def right (bits : Word → ℕ) (z : Word) : Word :=
  pair (pairFst z) ((pairSnd z).drop (bits (pairFst z)))

theorem left_poly {bits : Word → ℕ} (hb : UnaryFn bits) : left bits ∈ FP := by
  apply mem_FP_pair pairFst_mem_FP
  simpa only [List.length_replicate] using
    (Cobham.takeLenFn_mem_FP (hb.comp pairFst_mem_FP).mem_FP pairSnd_mem_FP)

theorem right_poly {bits : Word → ℕ} (hb : UnaryFn bits) : right bits ∈ FP := by
  apply mem_FP_pair pairFst_mem_FP
  simpa only [List.length_replicate] using
    (dropLenFn_mem_FP (hb.comp pairFst_mem_FP).mem_FP pairSnd_mem_FP)

noncomputable def Test.triple (A : Test) : Test where
  bits := fun x ↦ A.bits x + (A.bits x + A.bits x)
  bits_poly := A.bits_poly.add (A.bits_poly.add A.bits_poly)
  answer := fun z ↦ vote (A.answer (left A.bits z))
    (A.answer (left A.bits (right A.bits z))) (A.answer (right A.bits (right A.bits z)))
  answer_poly := by
    have h1 := A.answer_poly.comp (left_poly A.bits_poly)
    have h2 := A.answer_poly.comp (mem_FP_comp (right_poly A.bits_poly) (left_poly A.bits_poly))
    have h3 := A.answer_poly.comp (mem_FP_comp (right_poly A.bits_poly) (right_poly A.bits_poly))
    exact (((h1.and h2).or (h1.and h3)).or (h2.and h3)).of_iff
      (fun z ↦ by simp [vote, Bool.or_eq_true, Bool.and_eq_true])

def tripleEquiv (a : ℕ) : (Fin (a + (a + a)) → Bool) ≃
    (Fin a → Bool) × (Fin a → Bool) × (Fin a → Bool) :=
  (blockEquiv a (a + a)).trans (Equiv.prodCongr (Equiv.refl _) (blockEquiv a a))

theorem Test.triple_run (A : Test) (x : Word)
    (r : Fin (A.bits x + (A.bits x + A.bits x)) → Bool) :
    A.triple.run x r = vote (A.run x ((tripleEquiv (A.bits x) r).1))
      (A.run x ((tripleEquiv (A.bits x) r).2.1))
      (A.run x ((tripleEquiv (A.bits x) r).2.2)) := by
  simp only [Test.run, Test.triple, left, right, pairFst_pair, pairSnd_pair,
    FairTests.take_block, FairTests.drop_block]
  rfl

theorem Test.triple_error (A : Test) (x : Word) (b : Bool) :
    A.triple.error x b = errorMap (A.error x b) := by
  unfold Test.error
  rw [finite_probability_equiv (tripleEquiv (A.bits x)) _
    (fun r ↦ vote (A.run x r.1) (A.run x r.2.1) (A.run x r.2.2) ≠ b)
    (fun r ↦ by rw [A.triple_run])]
  exact Lax323828.MajorityAmplification.majority_error (A.run x) b

noncomputable def Test.boost (A : Test) : Test := A.triple.triple.triple

theorem Test.boost_error (A : Test) (x : Word) (b : Bool) (h : A.error x b ≤ 1 / 3) :
    A.boost.error x b ≤ 1 / 12 := by
  simp only [Test.boost, Test.triple_error]
  exact Lax323828.MajorityAmplification.three_rounds _ (finite_probability_nonneg _) h

@[simp] theorem Test.boost_bits (A : Test) (x : Word) : A.boost.bits x = 27 * A.bits x := by
  simp only [Test.boost, Test.triple]; omega

theorem probability_and {α β : Type} [Fintype α] [Fintype β]
    (P : α → Prop) (Q : β → Prop) :
    probability (fun r : α × β ↦ P r.1 ∧ Q r.2) = probability P * probability Q := by
  rw [finite_probability_product (fun a b ↦ P a ∧ Q b)]
  simp_rw [finite_probability_indicator]
  have hi (a : α) (b : β) : (if P a ∧ Q b then (1 : ℝ) else 0) =
      (if P a then (1 : ℝ) else 0) * (if Q b then (1 : ℝ) else 0) := by
    split_ifs <;> simp_all
  simp_rw [hi, ← Finset.mul_expect, ← Finset.expect_mul]

noncomputable def Test.andSelf (A : Test) : Test where
  bits := fun x ↦ A.bits x + A.bits x
  bits_poly := A.bits_poly.add A.bits_poly
  answer := fun z ↦ A.answer (left A.bits z) && A.answer (right A.bits z)
  answer_poly := ((A.answer_poly.comp (left_poly A.bits_poly)).and
    (A.answer_poly.comp (right_poly A.bits_poly))).of_iff (fun z ↦ by simp)

theorem Test.andSelf_probability (A : Test) (x : Word) :
    probability (fun r ↦ A.andSelf.run x r = true) =
      probability (fun r ↦ A.run x r = true) ^ 2 := by
  rw [finite_probability_equiv (blockEquiv (A.bits x) (A.bits x)) _
    (fun r ↦ A.run x r.1 = true ∧ A.run x r.2 = true) ?_]
  · rw [probability_and (fun r ↦ A.run x r = true) (fun r ↦ A.run x r = true)]; ring
  · intro r
    simp only [Test.run, Test.andSelf, left, right, pairFst_pair, pairSnd_pair,
      FairTests.take_block, FairTests.drop_block, Bool.and_eq_true]
    rfl

/-- The finite-tape compiler also implements two-sided Boolean tests in the
registered BPP machine model, preserving the exact answer distribution. -/
theorem Test.in_BPP (A : Test) (L : Language)
    (h : ∀ x, (2 / 3 : ℝ) ≤ probability
      (fun r ↦ Lax666725.ProbabilisticMachines.Correct L x (A.run x r))) :
    L ∈ Lax666725.RandomizedPolynomialTime.BPP := by
  have hf : (fun z ↦ FiniteEncoding.code (some (A.answer z))) ∈ FP := by
    apply mem_FP_of_eq (A.answer_poly.ite_mem_FP
      (constFn_mem_FP (FiniteEncoding.code (some true)))
      (constFn_mem_FP (FiniteEncoding.code (some false))))
    intro z
    cases A.answer z <;> simp
  obtain ⟨C, hC⟩ := FairTestCompiler.compile A.bits A.bits_poly
    (fun z ↦ some (A.answer z)) hf
  let D : Lax666725.ProbabilisticMachines.Procedure Bool :=
    { C with output := fun q ↦ (C.output q).getD false }
  refine ⟨D, fun x ↦ ?_⟩
  have hd : D.probability x (Lax666725.ProbabilisticMachines.Correct L x) =
      C.probability x (fun a ↦ Lax666725.ProbabilisticMachines.Correct L x (a.getD false)) := rfl
  have hc := hC x (fun a ↦ Lax666725.ProbabilisticMachines.Correct L x (a.getD false))
  rw [hd]
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_div, Rat.cast_ofNat, hc, Option.getD_some, Test.run] using h x

/-- Two independent trials, accepting only if both accept, turn our asymmetric
intermediate bounds into the registered two-sided BPP guarantee. -/
theorem Test.andSelf_in_BPP (A : Test) (L : Language)
    (hyes : ∀ x ∈ L, A.error x true ≤ 1 / 12)
    (hno : ∀ x ∉ L, A.error x false ≤ 5 / 12) :
    L ∈ Lax666725.RandomizedPolynomialTime.BPP := by
  apply A.andSelf.in_BPP L
  intro x
  have he := A.andSelf_probability x
  have hn := finite_probability_nonneg (fun r ↦ A.run x r = true)
  by_cases hx : x ∈ L
  · have hy := hyes x hx
    change probability (fun r ↦ ¬ A.run x r = true) ≤ 1 / 12 at hy
    rw [FairTests.probability_not] at hy
    simpa only [Lax666725.ProbabilisticMachines.Correct, hx, iff_true, he] using
      (show (2 / 3 : ℝ) ≤ probability (fun r ↦ A.run x r = true) ^ 2 by nlinarith)
  · have hy := hno x hx
    have hb : (fun r ↦ A.run x r ≠ false) = (fun r ↦ A.run x r = true) := by
      funext r; simp
    change probability (fun r ↦ A.run x r ≠ false) ≤ 5 / 12 at hy
    rw [hb] at hy
    simp only [Lax666725.ProbabilisticMachines.Correct, hx, iff_false,
      FairTests.probability_not, he]
    nlinarith

end Lax323828Proofs.RegisteredBridge.BoundedErrorTests
