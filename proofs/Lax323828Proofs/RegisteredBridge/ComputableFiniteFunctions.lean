import Lax323828Proofs.RegisteredBridge.ComputableEncodings
import Lax323828Proofs.PCPFoundation.Classes.P.BoundedQuant
import Lax323828Proofs.RegisteredBridge.ComputableNumbering
import Mathlib.Data.Fintype.Pi

set_option backward.isDefEq.respectTransparency false

namespace Lax323828Proofs.RegisteredBridge.ComputableEncoding

open PCPFoundation.Complexity FiniteEncoding ComputableNumbering
open scoped Classical

variable {A : Family} {a : Encoding A}

theorem fixed_pair {X Y : Type} [Fintype X] [Fintype Y]
    {f : ∀ z, A z → X} {g : ∀ z, A z → Y}
    (hf : Realizes a (ComputableEncoding.finite X) f)
    (hg : Realizes a (ComputableEncoding.finite Y) g) :
    Realizes a (ComputableEncoding.finite (X × Y)) (fun z v ↦ (f z v, g z v)) := by
  have h := fixed_map (prod (ComputableEncoding.finite X) (ComputableEncoding.finite Y) [])
    (prod_injective (a := ComputableEncoding.finite X) (b := ComputableEncoding.finite Y)
      (fun _ ↦ code_injective) (fun _ ↦ code_injective) []) code id
  exact comp (pair_maps hf hg) h

/-- Assemble a fixed finite function from its polynomial-time evaluations.
Its complete truth table has constant size, independent of the input word. -/
theorem finite_function {I X : Type} [Fintype I] [Fintype X] [DecidableEq I]
    {f : ∀ z, A z → I → X}
    (hf : ∀ i, Realizes a (ComputableEncoding.finite X) (fun z v ↦ f z v i)) :
    Realizes a (ComputableEncoding.finite (I → X)) f := by
  let e := Fintype.equivFin I
  have htuple := tuple_maps (n := Fintype.card I) (fun i ↦ hf (e.symm i))
  have hconvert := fixed_map
    (fun p : Fin (Fintype.card I) → X ↦ tuple (ComputableEncoding.finite X) (Fintype.card I) [] p)
    (tuple_injective (a := ComputableEncoding.finite X) (fun _ ↦ code_injective) (Fintype.card I) [])
    code (fun p i ↦ p (e i))
  have h := comp htuple hconvert
  apply of_pointwise h
  intro z v
  funext i
  simp only [Equiv.symm_apply_apply]

theorem flag {f : ∀ z, A z → Bool} (hf : Realizes a (ComputableEncoding.finite Bool) f) :
    ∃ F : Word → Word, F ∈ FP ∧ ∀ z v, F (pair z (a z v)) = [f z v] := by
  have h := comp hf (fixed_map code code_injective (fun b : Bool ↦ [b]) id)
  exact h

/-- A predicate has one uniform polynomial-time test on valid encodings. -/
def Testable (a : Encoding A) (p : ∀ z, A z → Prop) : Prop :=
  ∃ q : Word → Prop, FPPred q ∧ ∀ z v, q (pair z (a z v)) ↔ p z v

theorem testable_of_flag {f : ∀ z, A z → Bool}
    (hf : Realizes a (ComputableEncoding.finite Bool) f) :
    Testable a (fun z v ↦ f z v = true) := by
  obtain ⟨F, hF, hc⟩ := flag hf
  refine ⟨fun z ↦ (F z).take 1 = [true],
    FPPred.of_bounded_key (take_mem_FP hF 1) (fun _ ↦ List.length_take_le _ _) (fun k ↦ k = [true]), ?_⟩
  intro z v
  simp [hc]

theorem Testable.realizes {p : ∀ z, A z → Prop} [∀ z, DecidablePred (p z)]
    (hp : Testable a p) :
    Realizes a (ComputableEncoding.finite Bool) (fun z v ↦ decide (p z v)) := by
  classical
  obtain ⟨q, ⟨g, hg, hc⟩, hspec⟩ := hp
  let read : Word → Word := fun w ↦ code (w.head?.getD false)
  refine ⟨fun w ↦ read ([g w].take 1), bounded_read_mem_FP hg 1 read, ?_⟩
  intro z v
  have he : g (pair z (a z v)) = decide (p z v) := by
    apply Bool.eq_iff_iff.mpr
    rw [← hc, hspec, decide_eq_true_eq]
  simp [read, he, ComputableEncoding.finite]

theorem Testable.of_iff {p q : ∀ z, A z → Prop} (hp : Testable a p)
    (h : ∀ z v, p z v ↔ q z v) : Testable a q := by
  obtain ⟨P, hP, hc⟩ := hp
  exact ⟨P, hP, fun z v ↦ (hc z v).trans (h z v)⟩

theorem Testable.comp {B : Family} {b : Encoding B} {f : ∀ z, A z → B z}
    {p : ∀ z, B z → Prop} (hp : Testable b p) (hf : Realizes a b f) :
    Testable a (fun z v ↦ p z (f z v)) := by
  obtain ⟨P, hP, hc⟩ := hp
  obtain ⟨F, hF, hFc⟩ := hf
  refine ⟨fun w ↦ P (pair (pairFst w) (F w)),
    hP.comp (mem_FP_pair pairFst_mem_FP hF), ?_⟩
  intro z v
  simp only [pairFst_pair, hFc, hc]

theorem Testable.and {p q : ∀ z, A z → Prop} (hp : Testable a p) (hq : Testable a q) :
    Testable a (fun z v ↦ p z v ∧ q z v) := by
  obtain ⟨P, hP, hcP⟩ := hp
  obtain ⟨Q, hQ, hcQ⟩ := hq
  exact ⟨fun w ↦ P w ∧ Q w, hP.and hQ, fun z v ↦ and_congr (hcP z v) (hcQ z v)⟩

theorem Testable.not {p : ∀ z, A z → Prop} (hp : Testable a p) :
    Testable a (fun z v ↦ ¬ p z v) := by
  obtain ⟨P, hP, hc⟩ := hp
  exact ⟨fun w ↦ ¬ P w, hP.not, fun z v ↦ not_congr (hc z v)⟩

theorem testable_fin_eq {n : Word → ℕ} {f g : ∀ z, A z → Fin (n z)}
    (hf : Realizes a (unary n) f) (hg : Realizes a (unary n) g) :
    Testable a (fun z v ↦ f z v = g z v) := by
  obtain ⟨F, hF, hcF⟩ := hf
  obtain ⟨G, hG, hcG⟩ := hg
  refine ⟨fun w ↦ (F w).length = (G w).length,
    FPPred.eq (UnaryFn.length hF) (UnaryFn.length hG), ?_⟩
  intro z v
  simp only [hcF, hcG, unary, List.length_replicate, Fin.ext_iff]

theorem Testable.forall_fin {n : Word → ℕ} (hn : UnaryFn n)
    {p : ∀ z, A z → Fin (n z) → Prop}
    (hp : Testable (prod a (unary n)) (fun z v ↦ p z v.1 v.2)) :
    Testable a (fun z v ↦ ∀ i, p z v i) := by
  obtain ⟨P, hP, hc⟩ := hp
  let arg : Word → Word := fun w ↦
    pair (pairFst (pairFst w)) (pair (pairSnd (pairFst w)) (pairSnd w))
  have harg : arg ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)
  refine ⟨fun w ↦ ∀ i < n (pairFst w), P (arg (pair w (List.replicate i true))),
    FPPred.forall_lt (hn.comp pairFst_mem_FP) (hP.comp harg), ?_⟩
  intro z v
  simp only [pairFst_pair]
  constructor
  · intro h i
    apply (hc z (v, i)).mp
    simpa only [arg, pairFst_pair, pairSnd_pair, prod, unary] using h i.val i.isLt
  · intro h i hi
    have hh := (hc z (v, ⟨i, hi⟩)).mpr (h ⟨i, hi⟩)
    simpa only [arg, pairFst_pair, pairSnd_pair, prod, unary] using hh

end Lax323828Proofs.RegisteredBridge.ComputableEncoding
