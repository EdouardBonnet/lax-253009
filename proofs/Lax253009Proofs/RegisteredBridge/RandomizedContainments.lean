import Lax253009Proofs.RegisteredBridge.CertificateDecoder
import Lax253009Proofs.RegisteredBridge.RandomTapeSimulation
import Lax666725.OneSidedError
import Lax666725.ZeroError

set_option backward.isDefEq.respectTransparency false

namespace Lax253009Proofs.RegisteredBridge

open PCPFoundation.Complexity
open Lax666725.ProbabilisticMachines

theorem positive_probability_witness (A : Procedure Bool) (x : List Bool)
    (h : (0 : ℚ) < A.probability x (fun b ↦ b = true)) :
    ∃ r, A.eval x r = true := by
  classical
  by_contra hn
  have he : Finset.univ.filter (fun r : A.Coins x ↦ A.eval x r = true) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro r _ hr
    exact hn ⟨r, hr⟩
  simp [Procedure.probability, he] at h

theorem registered_RP_subset_NP :
    Lax666725.OneSidedError.RP ⊆ Lax434930.NondeterministicPolynomialTime.NP := by
  classical
  intro L hL
  obtain ⟨A, hA⟩ := hL
  obtain ⟨ruler, hruler, hlen⟩ := Cobham.exists_exact_ruler A.time
  let first := CertificateDecoder.first
  let second := CertificateDecoder.second
  let V : Set (List Bool) := {z | (second z).length = (ruler (first z)).length ∧
    A.output (A.machine.run (first z) (second z)).q = true}
  have hp : FPPred (fun z ↦ A.output (A.machine.run (first z) (second z)).q = true) := by
    have h := mem_FP_comp (mem_FP_pair CertificateDecoder.first_mem_FP CertificateDecoder.second_mem_FP)
      (RandomTapeSimulation.finite_coin_evaluation_mem_FP A.machine A.output)
    have hflag : (fun z ↦ [A.output (A.machine.run (first z) (second z)).q]) ∈ FP := by
      simpa only [Function.comp_def, pairFst_pair, pairSnd_pair] using h
    exact FPPred.of_flag hflag
  have hV : V ∈ Lax434930.PolynomialTime.P := by
    apply P_subset_registered_P
    exact ((FPPred.eq (UnaryFn.length CertificateDecoder.second_mem_FP)
      (UnaryFn.length (mem_FP_comp CertificateDecoder.first_mem_FP hruler))).and hp).mem_P
  have hpair (x y : List Bool) :
      Lax434930.Certificates.pair x y ∈ V ↔
        y.length = A.time.eval x.length ∧ A.output (A.machine.run x y).q = true := by
    simp only [V, Set.mem_setOf_eq, first, second, CertificateDecoder.first_pair,
      CertificateDecoder.second_pair, hlen]
  refine ⟨V, hV, A.time, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := positive_probability_witness A x
      (lt_of_lt_of_le (by norm_num) ((hA x).2 hx))
    refine ⟨List.ofFn r, by simp, (hpair x _).mpr ⟨by simp, ?_⟩⟩
    exact hr
  · rintro ⟨y, hy, hyv⟩
    obtain ⟨hysize, hyout⟩ := (hpair x y).mp hyv
    let r : A.Coins x := fun i ↦ y[i.val]'(by omega)
    have hr : List.ofFn r = y := by
      apply List.ext_getElem
      · simpa only [List.length_ofFn] using hysize.symm
      · intro i hi hj
        simp only [List.getElem_ofFn, r]
    apply (hA x).1 r
    simpa only [Procedure.eval, hr] using hyout

def procedureRelabel {α β : Type} (A : Procedure α) (f : α → β) : Procedure β where
  machine := A.machine
  time := A.time
  output := f ∘ A.output
  halts := A.halts

theorem procedure_probability_mono {α : Type} (A : Procedure α) (x : List Bool)
    (E F : α → Prop) (h : ∀ r, E (A.eval x r) → F (A.eval x r)) :
    A.probability x E ≤ A.probability x F := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show
    Finset.univ.filter (fun r : A.Coins x ↦ E (A.eval x r)) ⊆
      Finset.univ.filter (fun r : A.Coins x ↦ F (A.eval x r)) from by
        intro r hr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, h r (Finset.mem_filter.mp hr).2⟩)

theorem registered_ZPP_subset_RP : Lax666725.ZeroError.ZPP ⊆ Lax666725.OneSidedError.RP := by
  rintro L ⟨A, hA⟩
  refine ⟨procedureRelabel A (fun a ↦ a.getD false), fun x ↦ ?_⟩
  constructor
  · intro r hr
    change (A.eval x r).getD false = true at hr
    cases h : A.eval x r with
    | none => simp [h] at hr
    | some b =>
      have hb : b = true := by simpa only [h, Option.getD_some] using hr
      exact ((hA x).1 r b h).mp hb
  · intro hx
    change (2 / 3 : ℚ) ≤ A.probability x (fun a ↦ a.getD false = true)
    refine (hA x).2.trans (procedure_probability_mono A x _ _ ?_)
    intro r hr
    cases h : A.eval x r with
    | none => simp [h] at hr
    | some b => simpa only [h, Option.getD_some] using ((hA x).1 r b h).mpr hx

theorem registered_ZPP_subset_NP :
    Lax666725.ZeroError.ZPP ⊆ Lax434930.NondeterministicPolynomialTime.NP :=
  fun _ hL ↦ registered_RP_subset_NP (registered_ZPP_subset_RP hL)

end Lax253009Proofs.RegisteredBridge
