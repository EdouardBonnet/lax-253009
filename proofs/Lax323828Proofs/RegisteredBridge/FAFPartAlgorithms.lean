import Lax323828Proofs.RegisteredBridge.FAFDataAlgorithms
import Lax323828Proofs.RegisteredBridge.SumNumbering
import Lax323828Proofs.RegisteredBridge.ComputablePredicates

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax323828Proofs.RegisteredBridge.FAFPartAlgorithms

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding ComputableNumbering
open Lax323828 CenteredProjection FAFLocalTests LongCodePatterns
open FAFDataAlgorithms
open scoped Classical

variable {U Ω W : Family}

noncomputable def indexCode (eu : Encoding U) (ew : Encoding W) (u w : ℕ) :
    Encoding (fun z ↦ Index (U z) (W z) u w) :=
  ComputableEncoding.sum (prod eu (ComputableEncoding.finite (LongCode.Coordinate u)))
    (prod ew (ComputableEncoding.finite (LongCode.Coordinate w)))

noncomputable def indexNumbering {eu : Encoding U} {ew : Encoding W}
    (pu : Numbering eu) (pw : Numbering ew) (u w : ℕ) :
    Numbering (indexCode eu ew u w) :=
  ComputableNumbering.sum (product pu (ComputableNumbering.finite code code_injective))
    (product pw (ComputableNumbering.finite code code_injective))

noncomputable def part {U Ω W : Type} {u w n s q : ℕ} (question : U → Ω → W)
    (v : Randomness U Ω u w n s q) (p : LongCode.Word q × (Fin n → Pattern w)) :
    Fin (q + n) → Index U W u w → Option Bool :=
  Fin.addCases
    (fun j x ↦ if x = Sum.inl (v.1, v.2.1.2 j) then some (p.1 j) else none)
    (fun i x ↦ match x with
      | .inl _ => none
      | .inr (a, g) => if a = question v.1 (v.2.1.1 i) then p.2 i g else none)

theorem parts_at {U Ω W : Type} [Fintype U] [Fintype W] {u w n s q : ℕ}
    (question : U → Ω → W) (v : Randomness U Ω u w n s q)
    (p : LongCode.Word q × (Fin n → Pattern w)) (j : Fin (q + n)) (x : Index U W u w) :
    parts question v p j (indexEquiv U W u w x) = part question v p j x := by
  refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) j
  · simp [parts, part, Equiv.apply_eq_iff_eq]
  · simp only [parts, part, Fin.addCases_right, Equiv.symm_apply_apply]
    cases x <;> rfl

variable {eu : Encoding U} {eo : Encoding Ω} {ew : Encoding W} {u w n s q : ℕ}

theorem compute_part (pu : Numbering eu) (pw : Numbering ew)
    (G : ∀ z, System (U z) (Ω z) (W z) (LongCode.Word u) (LongCode.Word w))
    (h : ComputableAmplification.Algorithms eu eo ew code code G)
    (p : LongCode.Word q × (Fin n → Pattern w)) (j : Fin (q + n)) :
    Realizes (prod (seedCode eu eo u w n s q) (indexCode eu ew u w))
      (ComputableEncoding.finite (Option Bool)) (fun z v ↦ part (G z).question v.1 p j v.2) := by
  let es := seedCode eu eo u w n s q
  let ec := ComputableEncoding.finite (LongCode.Coordinate u)
  let ed := ComputableEncoding.finite (LongCode.Coordinate w)
  let left := prod eu ec
  let right := prod ew ed
  refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) j
  · have hL : Realizes (prod es left) (ComputableEncoding.finite (Option Bool))
        (fun z v ↦ if v.2 = (v.1.1, v.1.2.1.2 j) then some (p.1 j) else none) := by
      have hu := comp (fst es left) (center (eu := eu) (eo := eo))
      have hg := comp (comp (fst es left) (referenceFunctions (eu := eu) (eo := eo)))
        (finite_map (fun gs : Fin q → LongCode.Coordinate u ↦ gs j))
      have hp := testable_eq (product pu (ComputableNumbering.finite code code_injective))
        (snd es left) (pair_maps hu hg)
      have hh := hp.ite_realizes (finite_constant _ (some (p.1 j))) (finite_constant _ none)
      apply of_pointwise hh
      intro z v
      by_cases hv : v.2 = (v.1.1, v.1.2.1.2 j) <;> simp [hv]
    have hR := finite_constant (prod es right) (none : Option Bool)
    have hh := prod_sum_cases hL hR
    apply of_pointwise hh
    intro z v
    rcases v with ⟨v, x | y⟩ <;> simp [part]
  · have hL := finite_constant (prod es left) (none : Option Bool)
    have hR : Realizes (prod es right) (ComputableEncoding.finite (Option Bool))
        (fun z v ↦ if v.2.1 = (G z).question v.1.1 (v.1.2.1.1 i) then p.2 i v.2.2 else none) := by
      have hquestion := comp (comp (fst es right) (questions G h)) (tuple_entry ew i)
      have hname := comp (snd es right) (fst ew ed)
      have hc := testable_eq pw hname hquestion
      have hg := comp (comp (snd es right) (snd ew ed)) (finite_map (p.2 i))
      exact hc.ite_realizes hg (finite_constant _ none)
    have hh := prod_sum_cases hL hR
    apply of_pointwise hh
    intro z v
    rcases v with ⟨v, x | y⟩ <;> simp [part]

end Lax323828Proofs.RegisteredBridge.FAFPartAlgorithms
