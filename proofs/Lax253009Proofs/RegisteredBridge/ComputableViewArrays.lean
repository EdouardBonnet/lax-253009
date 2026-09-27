import Lax253009Proofs.RegisteredBridge.ComputablePredicates
import Lax253009Proofs.RepeatedSlotViews

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax253009Proofs.RegisteredBridge

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding ComputableNumbering
open Lax253009 LocalTests TestRepetition
open scoped Classical

namespace ComputableEncoding

theorem Testable.exists_fin {A : Family} {a : Encoding A} {n : Word → ℕ}
    (hn : UnaryFn n) {p : ∀ z, A z → Fin (n z) → Prop}
    (hp : Testable (prod a (unary n)) (fun z v ↦ p z v.1 v.2)) :
    Testable a (fun z v ↦ ∃ i, p z v i) := by
  have h := (Testable.forall_fin (a := a) (p := fun z v i ↦ ¬ p z v i) hn hp.not).not
  apply h.of_iff
  intro z v
  simp

end ComputableEncoding

namespace ComputableViewArrays

variable {A : Family} {a : Encoding A} {k m : Word → ℕ}
variable (v : ∀ z, A z → Fin (k z) → View (m z))

def Algorithms : Prop := Realizes (prod (prod a (unary k)) (unary m))
  (ComputableEncoding.finite (Option Bool)) (fun z w ↦ v z w.1.1 w.1.2 w.2)

theorem coherent (h : Algorithms (a := a) v) (hk : UnaryFn k) (hm : UnaryFn m) :
    Testable a (fun z w ↦ Coherent (v z w)) := by
  let ek := unary k
  let em := unary m
  let ak := prod a ek
  let akk := prod ak ek
  have houter := fst akk em
  have hfirst := comp houter (fst ak ek)
  have horiginal := comp hfirst (fst a ek)
  have hsecond := comp houter (snd ak ek)
  have hcoordinate := snd akk em
  have hv₁ := comp (pair_maps hfirst hcoordinate) h
  have hv₂ := comp (pair_maps (pair_maps horiginal hsecond) hcoordinate) h
  have hp := comp (fixed_pair hv₁ hv₂) (finite_map (fun p : Option Bool × Option Bool ↦
    decide (∀ b c, p.1 = some b → p.2 = some c → b = c)))
  have ht := (testable_of_flag hp).of_iff (fun _ _ ↦ decide_eq_true_iff)
  have hm' := Testable.forall_fin (a := akk)
    (p := fun z w i ↦ ∀ b c, v z w.1.1 w.1.2 i = some b →
      v z w.1.1 w.2 i = some c → b = c) hm ht
  have hk' := Testable.forall_fin (a := ak)
    (p := fun z w j ↦ ∀ i b c, v z w.1 w.2 i = some b → v z w.1 j i = some c → b = c) hk hm'
  exact Testable.forall_fin (a := a)
    (p := fun z w j ↦ ∀ j' i b c, v z w j i = some b → v z w j' i = some c → b = c) hk hk'

theorem union (h : Algorithms (a := a) v) (hk : UnaryFn k) :
    Realizes (prod a (unary m)) (ComputableEncoding.finite (Option Bool))
      (fun z w ↦ RepeatedSlotViews.unionView (v z w.1) w.2) := by
  let am := prod a (unary m)
  have houter := fst am (unary k)
  have horiginal := comp houter (fst a (unary m))
  have hcoordinate := comp houter (snd a (unary m))
  have hindex := snd am (unary k)
  have hv := comp (pair_maps (pair_maps horiginal hindex) hcoordinate) h
  have hbit (b : Bool) := comp hv (finite_map (fun c : Option Bool ↦ decide (c = some b)))
  have htest (b : Bool) := (testable_of_flag (hbit b)).of_iff (fun _ _ ↦ decide_eq_true_iff)
  have hex (b : Bool) := Testable.exists_fin (a := am)
    (p := fun z w j ↦ v z w.1 j w.2 = some b) hk (htest b)
  have hfalse := (hex false).ite_realizes (finite_constant am (some false)) (finite_constant am none)
  have htrue := (hex true).ite_realizes (finite_constant am (some true)) hfalse
  apply of_pointwise htrue
  intro z w
  by_cases ht : ∃ i, v z w.1 i w.2 = some true <;>
    by_cases hf : ∃ i, v z w.1 i w.2 = some false <;>
      simp [RepeatedSlotViews.unionView, ht, hf]

end ComputableViewArrays
end Lax253009Proofs.RegisteredBridge
