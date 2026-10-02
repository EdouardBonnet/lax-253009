import Lax323828Proofs.RegisteredBridge.FAFPartAlgorithms

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax323828Proofs.RegisteredBridge.FAFTranscriptAlgorithms

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding ComputableNumbering
open Lax323828 CenteredProjection FAFLocalTests LongCodePatterns TestRepetition LocalTests
open FAFDataAlgorithms FAFPartAlgorithms
open scoped Classical

def mergeValues {k : ℕ} (v : Fin k → Option Bool) : Option Bool :=
  merge (fun (j : Fin k) (_ : Fin 1) ↦ v j) 0

theorem mergeValues_eq {k m : ℕ} (v : Fin k → View m) (i : Fin m) :
    mergeValues (fun j ↦ v j i) = merge v i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (v 0 i).or (mergeValues (fun j : Fin k ↦ v j.succ i)) =
      (v 0 i).or (merge (fun j : Fin k ↦ v j.succ) i)
    rw [ih]

def CoherentValues {k : ℕ} (v : Fin k → Option Bool) : Prop :=
  ∀ j j' b c, v j = some b → v j' = some c → b = c

variable {U Ω W : Family} [∀ z, Fintype (U z)] [∀ z, Fintype (W z)]
variable {eu : Encoding U} {eo : Encoding Ω} {ew : Encoding W} {u w n s q : ℕ}

theorem compute_merge (pu : Numbering eu) (pw : Numbering ew)
    (G : ∀ z, CenteredProjection.System (U z) (Ω z) (W z) (LongCode.Word u) (LongCode.Word w))
    (h : ComputableAmplification.Algorithms eu eo ew code code G)
    (p : LongCode.Word q × (Fin n → Pattern w)) :
    Realizes (prod (seedCode eu eo u w n s q) (indexCode eu ew u w))
      (ComputableEncoding.finite (Option Bool)) (fun z v ↦
        merge (parts (G z).question v.1 p) (indexEquiv (U z) (W z) u w v.2)) := by
  have hv := finite_function (fun j ↦ compute_part (s := s) pu pw G h p j)
  have hh := comp hv (finite_map (@mergeValues (q + n)))
  apply of_pointwise hh
  intro z v
  rw [← mergeValues_eq]
  congr 1
  funext j
  exact (parts_at _ _ _ _ _).symm

theorem coherent_iff (question : ∀ z, U z → Ω z → W z) (z : Word)
    (v : Randomness (U z) (Ω z) u w n s q) (p : LongCode.Word q × (Fin n → Pattern w))
    (pi : Numbering (indexCode eu ew u w)) :
    (∀ i : Fin (pi.size z), CoherentValues
      (fun j ↦ part (question z) v p j ((pi.equiv z).symm i))) ↔
      Coherent (parts (question z) v p) := by
  constructor
  · intro hh j j' x b c hb hc
    let a := (indexEquiv (U z) (W z) u w).symm x
    have he : indexEquiv (U z) (W z) u w a = x := Equiv.apply_symm_apply _ _
    apply hh (pi.equiv z a) j j' b c
    · simpa only [Equiv.symm_apply_apply, ← he, parts_at] using hb
    · simpa only [Equiv.symm_apply_apply, ← he, parts_at] using hc
  · intro hh i j j' b c hb hc
    apply hh j j' (indexEquiv (U z) (W z) u w ((pi.equiv z).symm i)) b c
    · simpa only [parts_at] using hb
    · simpa only [parts_at] using hc

theorem compute_coherent (pu : Numbering eu) (pw : Numbering ew)
    (G : ∀ z, CenteredProjection.System (U z) (Ω z) (W z) (LongCode.Word u) (LongCode.Word w))
    (h : ComputableAmplification.Algorithms eu eo ew code code G)
    (p : LongCode.Word q × (Fin n → Pattern w)) :
    Realizes (seedCode eu eo u w n s q) (ComputableEncoding.finite Bool)
      (fun z v ↦ decide (Coherent (parts (G z).question v p))) := by
  let pi := indexNumbering pu pw u w
  let es := seedCode eu eo u w n s q
  have hv := finite_function (fun j ↦ compute_part (s := s) pu pw G h p j)
  have hc := comp hv (finite_map (fun v : Fin (q + n) → Option Bool ↦ decide (CoherentValues v)))
  have hi := pair_maps (fst es (unary pi.size))
    (comp (snd es (unary pi.size)) pi.element)
  have ht := (testable_of_flag (comp hi hc)).of_iff (fun _ _ ↦ decide_eq_true_iff)
  have hh := Testable.forall_fin (a := es)
    (p := fun z v i ↦ CoherentValues (fun j ↦ part (G z).question v p j ((pi.equiv z).symm i)))
    pi.size_poly ht
  have hx := hh.of_iff (fun z v ↦ coherent_iff (fun z ↦ (G z).question) z v p pi)
  exact hx.realizes

theorem valid_slot (pu : Numbering eu) (pw : Numbering ew)
    (G : ∀ z, CenteredProjection.System (U z) (Ω z) (W z) (LongCode.Word u) (LongCode.Word w))
    (h : ComputableAmplification.Algorithms eu eo ew code code G) :
    Realizes (prod (seedCode eu eo u w n s q)
      (ComputableEncoding.finite (Fin (2 ^ (q + n * s)))))
      (ComputableEncoding.finite Bool) (fun z v ↦
        match FAFSlots.patternSlot (FAFSlots.data (G z).project (G z).valid v.1) v.2 with
        | none => false
        | some p => decide (Coherent (parts (G z).question v.1 p))) := by
  let es := seedCode eu eo u w n s q
  let ej := ComputableEncoding.finite (Fin (2 ^ (q + n * s)))
  apply finite_dispatch (b := ComputableEncoding.finite Bool) (f := fun p z v ↦
    match p with | none => false | some p => decide (Coherent (parts (G z).question v.1 p)))
    (candidate (n := n) (s := s) (q := q) G h)
  intro p
  cases p with
  | none => exact finite_constant (prod es ej) false
  | some p =>
    have hh := comp (fst es ej) (compute_coherent (s := s) pu pw G h p)
    exact hh

theorem view_slot (pu : Numbering eu) (pw : Numbering ew)
    (G : ∀ z, CenteredProjection.System (U z) (Ω z) (W z) (LongCode.Word u) (LongCode.Word w))
    (h : ComputableAmplification.Algorithms eu eo ew code code G) :
    Realizes (prod (prod (seedCode eu eo u w n s q)
      (ComputableEncoding.finite (Fin (2 ^ (q + n * s))))) (indexCode eu ew u w))
      (ComputableEncoding.finite (Option Bool)) (fun z v ↦
        match FAFSlots.patternSlot (FAFSlots.data (G z).project (G z).valid v.1.1) v.1.2 with
        | none => none
        | some p => merge (parts (G z).question v.1.1 p) (indexEquiv (U z) (W z) u w v.2)) := by
  let es := seedCode eu eo u w n s q
  let ej := ComputableEncoding.finite (Fin (2 ^ (q + n * s)))
  let ei := indexCode eu ew u w
  have hk := comp (fst (prod es ej) ei) (candidate (n := n) (s := s) (q := q) G h)
  apply finite_dispatch (b := ComputableEncoding.finite (Option Bool))
    (f := fun p z v ↦ match p with
      | none => none
      | some p => merge (parts (G z).question v.1.1 p) (indexEquiv (U z) (W z) u w v.2)) hk
  intro p
  cases p with
  | none => exact finite_constant (prod (prod es ej) ei) none
  | some p =>
    have hi := pair_maps (comp (fst (prod es ej) ei) (fst es ej)) (snd (prod es ej) ei)
    have hh := comp hi (compute_merge (s := s) pu pw G h p)
    exact hh

end Lax323828Proofs.RegisteredBridge.FAFTranscriptAlgorithms
