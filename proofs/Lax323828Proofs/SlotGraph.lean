import Lax323828Proofs.EncodedReduction
import Lax323828Proofs.TestRepetition
import Lax323828Proofs.RandomizedReduction

namespace Lax323828Proofs.SlotGraph

open Lax323828 LocalTests TestSampling TestRepetition Graphs GraphEncoding
open scoped Classical

/-- A fixed number of possible transcripts per seed, with unused positions
marked invalid. Numbering never requires enumerating an input-dependent subtype. -/
structure Enumeration {r m : ℕ} (C : LocalTests.System r m) (A : ℕ) where
  valid : Fin r → Fin A → Bool
  view : Fin r → Fin A → View m
  sound : ∀ i j, valid i j = true → view i j ∈ C.accepting i
  complete : ∀ i a, a ∈ C.accepting i → ∃ j, valid i j = true ∧ view i j = a

variable {r m A : ℕ} {C : LocalTests.System r m}

def graph (E : Enumeration C A) : SimpleGraph (Fin r × Fin A) where
  Adj x y := x.1 ≠ y.1 ∧ E.valid x.1 x.2 = true ∧ E.valid y.1 y.2 = true ∧
    Compatible (E.view x.1 x.2) (E.view y.1 y.2)
  symm := ⟨by
    rintro x y ⟨hne, hx, hy, h⟩
    exact ⟨Ne.symm hne, hy, hx, fun i a b ha hb ↦ (h i b a hb ha).symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

noncomputable def output (E : Enumeration C A) : Graph (r * A) :=
  numbered (graph E) finProdFinEquiv.symm

theorem output_cliqueNumber (E : Enumeration C A) :
    (output E).cliqueNumber = (graph E).cliqueNum := Lax323828.GraphEncoding.cliqueNumber_numbered _ _

theorem completeness (E : Enumeration C A) (π : Oracle m) :
    (C.acceptedSeeds π).card ≤ (graph E).cliqueNum := by
  classical
  let seeds := C.acceptedSeeds π
  have accepted (i : seeds) : ∃ a ∈ C.accepting i.1, Extends π a := by
    simpa [seeds, LocalTests.System.acceptedSeeds] using i.2
  choose a ha he using accepted
  choose j hj hview using fun i ↦ E.complete i.1 (a i) (ha i)
  let vertex : seeds → Fin r × Fin A := fun i ↦ (i.1, j i)
  have hinj : Function.Injective vertex := fun _ _ h ↦ Subtype.ext (congrArg Prod.fst h)
  have hc : (graph E).IsClique (Finset.univ.image vertex) := by
    intro x hx y hy hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨fun h ↦ hne (congrArg vertex (Subtype.ext h)), hj i, hj j, ?_⟩
    change Compatible (E.view i.1 _) (E.view j.1 _)
    rw [hview, hview]
    exact fun p b c hb hc ↦ (he i p b hb).symm.trans (he j p c hc)
  have h := hc.card_le_cliqueNum
  simpa [Finset.card_image_of_injective _ hinj, seeds] using h

noncomputable def extend (E : Enumeration C A) (s : Finset (Fin r × Fin A)) : Oracle m :=
  fun i ↦ decide (∃ v ∈ s, E.view v.1 v.2 i = some true)

theorem extend_extends (E : Enumeration C A) (s : Finset (Fin r × Fin A))
    (hs : (graph E).IsClique s) (v : Fin r × Fin A) (hv : v ∈ s) :
    Extends (extend E s) (E.view v.1 v.2) := by
  classical
  intro i b hb
  cases b with
  | true => exact decide_eq_true ⟨v, hv, hb⟩
  | false =>
    apply decide_eq_false
    rintro ⟨u, hu, hval⟩
    by_cases he : u = v
    · subst u
      simp [hb] at hval
    · exact Bool.noConfusion ((hs hu hv he).2.2.2 i true false hval hb)

/-- Invalid positions are isolated. Every clique with at least two vertices
therefore gives one accepted seed per vertex under a single global proof. -/
theorem soundness (E : Enumeration C A) (s : Finset (Fin r × Fin A))
    (hs : (graph E).IsClique s) (hcard : 1 < s.card) :
    s.card ≤ (C.acceptedSeeds (extend E s)).card := by
  classical
  have hinj : Set.InjOn (fun v : Fin r × Fin A ↦ v.1) (s : Set _) := by
    intro u hu v hv heq
    by_contra hne
    exact (hs hu hv hne).1 heq
  have hsub : s.image Prod.fst ⊆ C.acceptedSeeds (extend E s) := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨u, hu, hne⟩ := s.exists_mem_ne hcard v
    have hvalid := (hs hv hu hne.symm).2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨E.view v.1 v.2, E.sound _ _ hvalid, extend_extends E s hs v hv⟩⟩
  calc
    s.card = (s.image Prod.fst).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem optimum_bounds (E : Enumeration C A) :
    C.optimum ≤ (output E).cliqueNumber ∧
      (output E).cliqueNumber ≤ max 1 C.optimum := by
  classical
  rw [output_cliqueNumber]
  constructor
  · exact Finset.sup_le fun π _ ↦ completeness E π
  · obtain ⟨s, hs, hc⟩ := (graph E).exists_isNClique_cliqueNum
    by_cases hcard : 1 < s.card
    · have h := soundness E s hs hcard
      have ho := Finset.le_sup (f := fun π ↦ (C.acceptedSeeds π).card)
        (Finset.mem_univ (extend E s))
      exact hc ▸ (h.trans ho).trans (le_max_right _ _)
    · exact hc ▸ (Nat.le_of_not_gt hcard).trans (le_max_left _ _)

/-- Number a repeated transcript using base-A digits. Each sampled test keeps
its own index; equal random choices at different indices remain distinct. -/
noncomputable def sampledRepetition (E : Enumeration C A) (k N : ℕ)
    (z : Fin N → Fin k → Fin r) :
    Enumeration (sampled (repeated C k) (fun i ↦ seedEquiv r k (z i))) (A ^ k) where
  valid i j := decide ((∀ a, E.valid (z i a) (finFunctionFinEquiv.symm j a) = true) ∧
    Coherent (fun a ↦ E.view (z i a) (finFunctionFinEquiv.symm j a)))
  view i j := merge (fun a ↦ E.view (z i a) (finFunctionFinEquiv.symm j a))
  sound i j h := by
    obtain ⟨hv, hc⟩ := of_decide_eq_true h
    apply Finset.mem_image.mpr
    refine ⟨fun a ↦ E.view (z i a) (finFunctionFinEquiv.symm j a), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun a ↦ ?_), hc⟩
    simpa only [Equiv.symm_apply_apply] using E.sound (z i a) _ (hv a)
  complete i a ha := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hv, hc⟩ := Finset.mem_filter.mp hv
    have hmem (j : Fin k) : v j ∈ C.accepting (z i j) := by
      simpa only [Equiv.symm_apply_apply] using Fintype.mem_piFinset.mp hv j
    choose d hd hview using fun j ↦ E.complete (z i j) (v j) (hmem j)
    refine ⟨finFunctionFinEquiv d, ?_, ?_⟩
    · simp only [Equiv.symm_apply_apply, decide_eq_true_eq]
      exact ⟨hd, by simpa only [hview] using hc⟩
    · simp only [Equiv.symm_apply_apply, hview]

end Lax323828Proofs.SlotGraph
