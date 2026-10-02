import Lax323828Proofs.RegisteredBridge.ConstraintAlgorithms
import Lax323828Proofs.RegisteredBridge.ComputableNumbering

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax323828Proofs.RegisteredBridge.RegularGameAlgorithms

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding

variable {A : Type} [Fintype A] [DecidableEq A]

def vertexCode (G : Word → ConstraintGraph A) : Encoding (fun z ↦ (G z).HalfEdge) :=
  fun _ v ↦ List.replicate (NumEnc.enc v) true

def dartCode (E : ExpanderFamily) : Encoding (fun _ ↦ ConstraintGraph.PreDart E) :=
  fun _ d ↦ List.replicate (NumEnc.enc d) true

theorem vertex_bound (G : ConstraintGraph A) (v : G.HalfEdge) : NumEnc.enc v < 2 * G.numEdges := by
  rw [G.enc_halfEdge, ConstraintGraph.halfCode]
  have hv := v.1.isLt
  cases v.2 <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

theorem vertex_div (G : ConstraintGraph A) (v : G.HalfEdge) : NumEnc.enc v / 2 = v.1.val := by
  rw [G.enc_halfEdge, ConstraintGraph.halfCode]
  cases v.2 <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

theorem dart_bound (E : ExpanderFamily) (d : ConstraintGraph.PreDart E) :
    NumEnc.enc d < 2 + 2 * E.degree := by
  have h := NumEnc.enc_lt d
  change NumEnc.enc d < 1 + ((E.degree + 1) + E.degree) at h
  omega

theorem algorithms (F : FinBase) (hd : 1 < F.deg)
    (E : Word → Word) (G : Word → ConstraintGraph A) (hE : E ∈ FP)
    (he : ∀ z, E z = encGraph (G z)) :
    ConstraintAlgorithms.Algorithms (vertexCode G) (dartCode (F.toFamily hd))
      (fun z ↦ GapBridge.system ((G z).preprocess (F.toFamily hd))) := by
  obtain ⟨R, hR, hRc⟩ := regular_rotation_mem_FP (A := A) F hd
  constructor
  · refine ⟨fun w ↦ R (pair (E (pairFst w)) (pairSnd w)),
      mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hE) pairSnd_mem_FP) hR, ?_⟩
    intro z v
    dsimp only
    simp only [prod, vertexCode, dartCode, pairFst_pair, pairSnd_pair, he]
    rw [hRc (G z) _ _ (vertex_bound _ v.1) (dart_bound _ v.2)]
    rw [ConstraintGraph.preRotNum_eq]
    rfl
  · let args : Word → Word := fun w ↦
      pair (pair (pair (E (pairFst w)) (pairFst (pairFst (pairSnd w))))
        (pairSnd (pairFst (pairSnd w)))) (pairSnd (pairSnd w))
    have hu := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
    have ha : args ∈ FP := mem_FP_pair
      (mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP hE)
        (mem_FP_comp hu pairFst_mem_FP)) (mem_FP_comp hu pairSnd_mem_FP))
      (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
    have hflag : Realizes
        (prod (prod (vertexCode G) (dartCode (F.toFamily hd))) (ComputableEncoding.finite (A × A)))
        (fun _ b ↦ [b])
        (fun z p ↦ (GapBridge.system ((G z).preprocess (F.toFamily hd))).relation p.1 p.2.1 p.2.2) := by
      refine ⟨RegularRelation.flag A (F.toFamily hd).degree ∘ args,
        mem_FP_comp ha (RegularRelation.flag_mem_FP A _), ?_⟩
      intro z p
      have hv : NumEnc.enc p.1.1 / 2 < (G z).numEdges := by
        rw [vertex_div]
        exact p.1.1.1.isLt
      have hfin : (⟨NumEnc.enc p.1.1 / 2, hv⟩ : Fin (G z).numEdges) = p.1.1.1 := by
        apply Fin.ext
        exact vertex_div _ _
      simp only [Function.comp_apply, args, prod, vertexCode, dartCode, ComputableEncoding.finite,
        pairFst_pair, pairSnd_pair, he]
      rw [RegularRelation.flag_eq A (F.toFamily hd).degree (G z) (NumEnc.enc p.1.1) (NumEnc.enc p.1.2) hv (dart_bound _ p.1.2)]
      rw [hfin]
      congr 1
      exact (preRel_eq (G z) (F.toFamily hd) p.1.1 p.1.2 p.2.1 p.2.2).symm
    exact comp hflag (fixed_map (fun b : Bool ↦ [b])
      (fun _ _ h ↦ List.cons.inj h |>.1) code id)

theorem edges_unary (E : Word → Word) (G : Word → ConstraintGraph A) (hE : E ∈ FP)
    (he : ∀ z, E z = encGraph (G z)) : UnaryFn (fun z ↦ (G z).numEdges) := by
  have h := UnaryFn.length (gEdgesFn_mem_FP hE)
  apply h.of_eq
  intro z
  change gEdges (E z) = (G z).numEdges
  rw [he, gEdges_encGraph]

noncomputable def vertexNumbering (E : Word → Word) (G : Word → ConstraintGraph A) (hE : E ∈ FP)
    (he : ∀ z, E z = encGraph (G z)) : ComputableNumbering.Numbering (vertexCode G) :=
  ComputableNumbering.transport
    (ComputableNumbering.fin (fun z ↦ (G z).numEdges * 2)
      ((edges_unary E G hE he).mul (UnaryFn.const 2)))
    (fun z ↦ NumEnc.equivFin (G z).HalfEdge)

noncomputable def dartNumbering (E : ExpanderFamily) : ComputableNumbering.Numbering (dartCode E) :=
  ComputableNumbering.finite (fun d : ConstraintGraph.PreDart E ↦ List.replicate (NumEnc.enc d) true)
    (fun d e h ↦ NumEnc.enc_injective (by
      simpa only [List.length_replicate] using congrArg List.length h))

end Lax323828Proofs.RegisteredBridge.RegularGameAlgorithms
