import Lax253009Proofs.RegisteredBridge.ComputableFiniteFunctions
import Lax253009Proofs.RegisteredBridge.ComputableAmplification
import Lax253009Proofs.FAFSlots

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax253009Proofs.RegisteredBridge.FAFDataAlgorithms

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding ComputableNumbering
open Lax253009 CenteredProjection FAFLocalTests
open scoped Classical

variable {U Ω W : Family} (eu : Encoding U) (eo : Encoding Ω)

noncomputable def seedCode (u w n s q : ℕ) :
    Encoding (fun z ↦ Randomness (U z) (Ω z) u w n s q) :=
  prod eu (prod (prod (tuple eo n) (ComputableEncoding.finite (Fin q → LongCode.Coordinate u)))
    (ComputableEncoding.finite (Fin n → Fin s → LongCode.Coordinate w)))

noncomputable def seedNumbering (pu : Numbering eu) (po : Numbering eo) (u w n s q : ℕ) :
    Numbering (seedCode eu eo u w n s q) :=
  product pu (product
    (product (tuples po n) (ComputableNumbering.finite code code_injective))
    (ComputableNumbering.finite code code_injective))

variable {eu eo} {ew : Encoding W} {u w n s q : ℕ}

theorem center : Realizes (seedCode eu eo u w n s q) eu (fun _ z ↦ z.1) := fst _ _

theorem extensions : Realizes (seedCode eu eo u w n s q) (tuple eo n) (fun _ z ↦ z.2.1.1) := by
  let er := ComputableEncoding.finite (Fin q → LongCode.Coordinate u)
  let el := ComputableEncoding.finite (Fin n → Fin s → LongCode.Coordinate w)
  have hh := comp (snd eu (prod (prod (tuple eo n) er) el)) (fst (prod (tuple eo n) er) el)
  have hh' := comp hh (fst (tuple eo n) er)
  exact hh'

theorem referenceFunctions : Realizes (seedCode eu eo u w n s q)
    (ComputableEncoding.finite (Fin q → LongCode.Coordinate u)) (fun _ z ↦ z.2.1.2) := by
  let er := ComputableEncoding.finite (Fin q → LongCode.Coordinate u)
  let el := ComputableEncoding.finite (Fin n → Fin s → LongCode.Coordinate w)
  have hh := comp (snd eu (prod (prod (tuple eo n) er) el)) (fst (prod (tuple eo n) er) el)
  have hh' := comp hh (snd (tuple eo n) er)
  exact hh'

theorem largerFunctions : Realizes (seedCode eu eo u w n s q)
    (ComputableEncoding.finite (Fin n → Fin s → LongCode.Coordinate w)) (fun _ z ↦ z.2.2) := by
  let er := ComputableEncoding.finite (Fin q → LongCode.Coordinate u)
  let el := ComputableEncoding.finite (Fin n → Fin s → LongCode.Coordinate w)
  have hh := comp (snd eu (prod (prod (tuple eo n) er) el)) (snd (prod (tuple eo n) er) el)
  exact hh

/-- Query every answer in the fixed binary alphabets at the finitely many
sampled extensions. The resulting tables are fixed finite lookup data. -/
theorem localData
    (G : ∀ z, System (U z) (Ω z) (W z) (LongCode.Word u) (LongCode.Word w))
    (h : ComputableAmplification.Algorithms eu eo ew code code G) :
    Realizes (seedCode eu eo u w n s q) (ComputableEncoding.finite (FAFSlots.Data u w n s q))
      (fun z v ↦ FAFSlots.data (G z).project (G z).valid v) := by
  have harg (i : Fin n) := pair_maps
    (center (eu := eu) (eo := eo) (u := u) (w := w) (n := n) (s := s) (q := q))
    (comp extensions (tuple_entry eo i))
  have hinput (i : Fin n) (y : LongCode.Word w) :=
    pair_maps (harg i) (finite_constant (seedCode eu eo u w n s q) y)
  have hρ : Realizes (seedCode eu eo u w n s q)
      (ComputableEncoding.finite (Fin n → LongCode.Word w → LongCode.Word u))
      (fun z v i y ↦ (G z).project v.1 (v.2.1.1 i) y) := by
    apply finite_function (I := Fin n) (X := LongCode.Word w → LongCode.Word u)
    intro i
    apply finite_function (I := LongCode.Word w) (X := LongCode.Word u)
    intro y
    have hh := comp (hinput i y) h.project
    exact hh
  have hv : Realizes (seedCode eu eo u w n s q)
      (ComputableEncoding.finite (Fin n → LongCode.Coordinate w))
      (fun z v i y ↦ (G z).valid v.1 (v.2.1.1 i) y) := by
    apply finite_function (I := Fin n) (X := LongCode.Coordinate w)
    intro i
    apply finite_function (I := LongCode.Word w) (X := Bool)
    intro y
    have hh := comp (hinput i y) h.valid
    exact hh
  exact fixed_pair hρ (fixed_pair hv (fixed_pair referenceFunctions largerFunctions))

theorem questions
    (G : ∀ z, System (U z) (Ω z) (W z) (LongCode.Word u) (LongCode.Word w))
    (h : ComputableAmplification.Algorithms eu eo ew code code G) :
    Realizes (seedCode eu eo u w n s q) (tuple ew n)
      (fun z v i ↦ (G z).question v.1 (v.2.1.1 i)) := by
  apply tuple_maps
  intro i
  have harg := pair_maps
    (center (eu := eu) (eo := eo) (u := u) (w := w) (n := n) (s := s) (q := q))
    (comp extensions (tuple_entry eo i))
  have hh := comp harg h.question
  exact hh

theorem candidate
    (G : ∀ z, System (U z) (Ω z) (W z) (LongCode.Word u) (LongCode.Word w))
    (h : ComputableAmplification.Algorithms eu eo ew code code G) :
    Realizes (prod (seedCode eu eo u w n s q)
      (ComputableEncoding.finite (Fin (2 ^ (q + n * s)))))
      (ComputableEncoding.finite (Option (LongCode.Word q × (Fin n → LongCodePatterns.Pattern w))))
      (fun z v ↦ FAFSlots.patternSlot (FAFSlots.data (G z).project (G z).valid v.1) v.2) := by
  have hd := comp (fst (seedCode eu eo u w n s q)
    (ComputableEncoding.finite (Fin (2 ^ (q + n * s))))) (localData G h)
  have hj := snd (seedCode eu eo u w n s q) (ComputableEncoding.finite (Fin (2 ^ (q + n * s))))
  have hh := comp (fixed_pair hd hj) (finite_map (fun p ↦ FAFSlots.patternSlot p.1 p.2))
  exact hh

end Lax253009Proofs.RegisteredBridge.FAFDataAlgorithms
