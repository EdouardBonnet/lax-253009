import Lax323828Proofs.RegisteredBridge.ComputableFiniteFunctions
import Lax323828Proofs.RegisteredBridge.GraphAlgorithm
import Lax323828Proofs.SlotGraph

set_option backward.isDefEq.respectTransparency false

namespace Lax323828Proofs.RegisteredBridge.SlotGraphAlgorithms

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding ComputableNumbering
open Lax323828 LocalTests
open scoped Classical

variable {r m A : Word → ℕ} {C : ∀ z, LocalTests.System (r z) (m z)}

structure Algorithms (E : ∀ z, SlotGraph.Enumeration (C z) (A z)) : Prop where
  valid : Realizes (prod (unary r) (unary A)) (ComputableEncoding.finite Bool)
    (fun z v ↦ (E z).valid v.1 v.2)
  view : Realizes (prod (prod (unary r) (unary A)) (unary m))
    (ComputableEncoding.finite (Option Bool)) (fun z v ↦ (E z).view v.1.1 v.1.2 v.2)

theorem adjacency (E : ∀ z, SlotGraph.Enumeration (C z) (A z)) (h : Algorithms E)
    (hm : UnaryFn m) :
    Testable (prod (prod (unary r) (unary A)) (prod (unary r) (unary A)))
      (fun z v ↦ (SlotGraph.graph (E z)).Adj v.1 v.2) := by
  let ev := prod (unary r) (unary A)
  let edge := prod ev ev
  have hleft := fst ev ev
  have hright := snd ev ev
  have hne := (testable_fin_eq (comp hleft (fst (unary r) (unary A)))
    (comp hright (fst (unary r) (unary A)))).not
  have hv₁ := (testable_of_flag h.valid).comp hleft
  have hv₂ := (testable_of_flag h.valid).comp hright
  have hl := comp (fst edge (unary m)) hleft
  have hr := comp (fst edge (unary m)) hright
  have hi := snd edge (unary m)
  have ha := comp (pair_maps hl hi) h.view
  have hb := comp (pair_maps hr hi) h.view
  have hp := comp (fixed_pair ha hb)
    (finite_map (fun p : Option Bool × Option Bool ↦
      decide (∀ b c, p.1 = some b → p.2 = some c → b = c)))
  have ht := (testable_of_flag hp).of_iff (fun z v ↦ decide_eq_true_iff)
  have hc := Testable.forall_fin (a := edge)
    (p := fun z v i ↦ ∀ b c, (E z).view v.1.1 v.1.2 i = some b →
      (E z).view v.2.1 v.2.2 i = some c → b = c) hm ht
  exact hne.and (hv₁.and (hv₂.and hc))

/-- Explicit mixed-radix numbering plus a polynomial loop through proof
coordinates gives the adjacency matrix in the estimator's required format. -/
theorem encode_mem_FP (E : ∀ z, SlotGraph.Enumeration (C z) (A z)) (h : Algorithms E)
    (hr : UnaryFn r) (hm : UnaryFn m) (hA : UnaryFn A) :
    (fun z ↦ (SlotGraph.output (E z)).encode) ∈ FP := by
  let ev := prod (unary r) (unary A)
  let count := fun z ↦ r z * A z
  let pv := product (fin r hr) (fin A hA)
  have hl := comp (fst (unary count) (unary count)) pv.element
  have hg := comp (snd (unary count) (unary count)) pv.element
  have hadj := (adjacency E h hm).comp (pair_maps hl hg)
  have hb := flag hadj.realizes
  obtain ⟨F, hF, hc⟩ := hb
  let arg : Word → Word := fun w ↦
    pair (pairFst (pairFst w)) (pair (pairSnd (pairFst w)) (pairSnd w))
  have harg : arg ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)
  apply graph_encode_mem_FP (fun z ↦ SlotGraph.output (E z)) (hr.mul hA)
    (mem_FP_comp harg hF)
  intro z i j
  simpa [Function.comp_apply, arg, pairFst_pair, pairSnd_pair, prod, unary,
    SlotGraph.output, GraphEncoding.numbered, pv, product, fin, count] using hc z (i, j)

end Lax323828Proofs.RegisteredBridge.SlotGraphAlgorithms
