import Lax253009Proofs.SlotGraph

namespace Lax253009Proofs.RepeatedSlotViews

open Lax253009 LocalTests TestRepetition TestSampling
open scoped Classical

theorem merge_none_iff {m k : ℕ} (a : Fin k → View m) (i : Fin m) :
    merge a i = none ↔ ∀ j, a j i = none := by
  induction k with
  | zero => simp [merge]
  | succ k ih =>
    cases hz : a 0 i <;> simp [merge, hz, ih, Fin.forall_fin_succ]

theorem merge_source {m k : ℕ} (a : Fin k → View m) (i : Fin m) (b : Bool)
    (h : merge a i = some b) : ∃ j, a j i = some b := by
  induction k with
  | zero => simp [merge] at h
  | succ k ih =>
    cases hz : a 0 i with
    | none =>
      obtain ⟨j, hj⟩ := ih (fun j ↦ a j.succ) (by simpa [merge, hz] using h)
      exact ⟨j.succ, hj⟩
    | some c =>
      have he : c = b := by simpa [merge, hz] using h
      exact ⟨0, he ▸ hz⟩

/-- Union by two bounded existence queries. This agrees with the ordered
merge whenever the candidate transcripts are mutually consistent. -/
noncomputable def unionView {m k : ℕ} (a : Fin k → View m) : View m :=
  fun i ↦ if ∃ j, a j i = some true then some true
    else if ∃ j, a j i = some false then some false else none

theorem union_eq_merge {m k : ℕ} (a : Fin k → View m) (ha : Coherent a) :
    unionView a = merge a := by
  funext i
  cases hm : merge a i with
  | none =>
    have hnone := (merge_none_iff a i).mp hm
    simp [unionView, hnone]
  | some b =>
    obtain ⟨j, hj⟩ := merge_source a i b hm
    cases b with
    | true => simp [unionView, show ∃ j, a j i = some true from ⟨j, hj⟩]
    | false =>
      have hn : ¬ ∃ l, a l i = some true := by
        rintro ⟨l, hl⟩
        exact Bool.noConfusion (ha l j i true false hl hj)
      simp [unionView, hn, show ∃ j, a j i = some false from ⟨j, hj⟩]

noncomputable def replaceView {r m A : ℕ} {C : LocalTests.System r m}
    (E : SlotGraph.Enumeration C A) (v : Fin r → Fin A → View m)
    (hv : ∀ i j, E.valid i j = true → v i j = E.view i j) :
    SlotGraph.Enumeration C A where
  valid := E.valid
  view := v
  sound i j hj := hv i j hj ▸ E.sound i j hj
  complete i a ha := by
    obtain ⟨j, hj, he⟩ := E.complete i a ha
    exact ⟨j, hj, (hv i j hj).trans he⟩

noncomputable def repeatedEnumeration {r m A : ℕ} {C : LocalTests.System r m}
    (E : SlotGraph.Enumeration C A) (k N : ℕ) (z : Fin N → Fin k → Fin r) :
    SlotGraph.Enumeration (sampled (repeated C k) (fun i ↦ seedEquiv r k (z i))) (A ^ k) :=
  replaceView (SlotGraph.sampledRepetition E k N z)
    (fun i j ↦ unionView (fun a ↦ E.view (z i a) (finFunctionFinEquiv.symm j a)))
    (fun i j h ↦ union_eq_merge _ (of_decide_eq_true h).2)

end Lax253009Proofs.RepeatedSlotViews
