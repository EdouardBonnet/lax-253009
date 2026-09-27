import Lax253009.CliqueCorrespondence
import Mathlib.Tactic

namespace Lax253009Proofs

open Lax253009.LocalTests Lax253009.ConsistencyGraph

variable {r m : ℕ}

private theorem compatible_of_extends {π : Oracle m} {a b : View m}
    (ha : Extends π a) (hb : Extends π b) : Compatible a b := by
  intro i x y hx hy
  exact (ha i x hx).symm.trans (hb i y hy)

/--
---
conclusion: Lax253009.CliqueCorrespondence.completeness
---
Choose one accepting local view for each accepting random choice. All the
chosen views extend the given proof, so they are pairwise compatible.
-/
theorem consistency_completeness (C : System r m) (π : Oracle m) :
    ∃ s : Finset (Vertex C), (graph C).IsClique s ∧
      s.card = (C.acceptedSeeds π).card := by
  classical
  let seeds := C.acceptedSeeds π
  have accepted (x : seeds) : ∃ a ∈ C.accepting x.1, Extends π a := by
    simpa [seeds, System.acceptedSeeds] using x.2
  choose view mem_view h_ext using accepted
  let vertex (x : seeds) : Vertex C := ⟨x.1, view x, mem_view x⟩
  have hinj : Function.Injective vertex := by
    intro x y h
    exact Subtype.ext (congrArg Sigma.fst h)
  refine ⟨Finset.univ.image vertex, ?_, ?_⟩
  · intro u hu v hv huv
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hv
    refine ⟨?_, compatible_of_extends (h_ext x) (h_ext y)⟩
    intro h
    exact huv (congrArg vertex (Subtype.ext h))
  · rw [Finset.card_image_of_injective _ hinj]
    simp [seeds]

private noncomputable def extendClique (C : System r m) (s : Finset (Vertex C)) :
    Oracle m := by
  classical
  exact fun i ↦ decide (∃ v ∈ s, v.2.1 i = some true)

private theorem extendClique_extends (C : System r m) (s : Finset (Vertex C))
    (hs : (graph C).IsClique s) (v : Vertex C) (hv : v ∈ s) :
    Extends (extendClique C s) v.2.1 := by
  classical
  intro i b hb
  cases b with
  | true =>
    exact decide_eq_true (show ∃ u ∈ s, u.2.1 i = some true from ⟨v, hv, hb⟩)
  | false =>
    apply decide_eq_false
    rintro ⟨u, hu, huval⟩
    by_cases huv : u = v
    · subst u
      simp [hb] at huval
    · have h := (hs hu hv huv).2 i true false huval hb
      cases h

/--
---
conclusion: Lax253009.CliqueCorrespondence.soundness
---
Glue the compatible partial assignments in a clique, assigning false at
positions no view fixes. Distinct vertices have distinct random choices.
-/
theorem consistency_soundness (C : System r m) (s : Finset (Vertex C))
    (hs : (graph C).IsClique s) :
    ∃ π : Oracle m, s.card ≤ (C.acceptedSeeds π).card := by
  classical
  refine ⟨extendClique C s, ?_⟩
  have hinj : Set.InjOn (fun v : Vertex C ↦ v.1) (s : Set (Vertex C)) := by
    intro u hu v hv heq
    by_contra hne
    exact (hs hu hv hne).1 heq
  have hsub : s.image (fun v ↦ v.1) ⊆ C.acceptedSeeds (extendClique C s) := by
    intro seed hseed
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hseed
    simp only [System.acceptedSeeds, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v.2.1, v.2.2, extendClique_extends C s hs v hv⟩
  calc
    s.card = (s.image (fun v ↦ v.1)).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

/--
---
conclusion: Lax253009.CliqueCorrespondence.cliqueNumber_eq_optimum
---
Apply soundness to a maximum clique and completeness to every proof.
-/
theorem consistency_cliqueNumber (C : System r m) :
    (graph C).cliqueNum = C.optimum := by
  classical
  apply le_antisymm
  · obtain ⟨s, hs, hcard⟩ := (graph C).exists_isNClique_cliqueNum
    obtain ⟨π, hπ⟩ := Lax253009.CliqueCorrespondence.soundness C s hs
    exact hcard ▸ hπ.trans (Finset.le_sup (f := fun π ↦ (C.acceptedSeeds π).card)
      (Finset.mem_univ π))
  · apply Finset.sup_le
    intro π _
    obtain ⟨s, hs, hcard⟩ := Lax253009.CliqueCorrespondence.completeness C π
    exact hcard ▸ hs.card_le_cliqueNum

/--
---
conclusion: Lax253009.CliqueCorrespondence.vertex_count
---
Count the vertices separately for each random choice.
-/
theorem consistency_vertex_count (C : System r m) :
    Fintype.card (Vertex C) = ∑ seed, (C.accepting seed).card := by
  classical
  simp [Vertex, Fintype.card_sigma]

/--
---
conclusion: Lax253009.CliqueCorrespondence.vertex_bound
---
Sum the per-choice bound on accepting local views.
-/
theorem consistency_vertex_bound (C : System r m) (A : ℕ)
    (hA : ∀ seed, (C.accepting seed).card ≤ A) :
    Fintype.card (Vertex C) ≤ r * A := by
  rw [Lax253009.CliqueCorrespondence.vertex_count]
  calc
    ∑ seed, (C.accepting seed).card ≤ ∑ _ : Fin r, A := Finset.sum_le_sum fun i _ ↦ hA i
    _ = r * A := by simp

/--
---
conclusion: Lax253009.CliqueCorrespondence.perfect_completeness
---
An always-accepted proof attains all random choices, the universal upper bound.
-/
theorem consistency_perfect_completeness (C : System r m)
    (h : ∃ π : Oracle m, ∀ seed, seed ∈ C.acceptedSeeds π) :
    (graph C).cliqueNum = r := by
  classical
  rw [Lax253009.CliqueCorrespondence.cliqueNumber_eq_optimum, System.optimum]
  apply le_antisymm
  · exact Finset.sup_le fun π _ ↦ by simpa using (C.acceptedSeeds π).card_le_univ
  · obtain ⟨π, hπ⟩ := h
    have heq : C.acceptedSeeds π = Finset.univ := Finset.eq_univ_of_forall hπ
    have hle := Finset.le_sup (f := fun π ↦ (C.acceptedSeeds π).card) (Finset.mem_univ π)
    simpa [heq] using hle

/--
---
conclusion: Lax253009.CliqueCorrespondence.soundness_bound
---
The universal acceptance bound also bounds its maximum.
-/
theorem consistency_soundness_bound (C : System r m) (s : ℕ)
    (h : ∀ π : Oracle m, (C.acceptedSeeds π).card ≤ s) :
    (graph C).cliqueNum ≤ s := by
  rw [Lax253009.CliqueCorrespondence.cliqueNumber_eq_optimum]
  exact Finset.sup_le fun π _ ↦ h π

end Lax253009Proofs
