import Lax323828Proofs.RegisteredBridge.RegisteredNP
import Lax323828Proofs.PCPFoundation.Classes.PCP.Internal.AlgPreRot
import Lax323828Proofs.PCPFoundation.Classes.PCP.Internal.AlgPreRel

namespace Lax323828Proofs.RegisteredBridge

open PCPFoundation.Complexity FiniteEncoding

/-- The canonical numerical rotation map for the regularized graph is polynomial-time. -/
theorem regular_rotation_mem_FP {A : Type} [Fintype A] [DecidableEq A] (F : FinBase) (hd : 1 < F.deg) :
    ∃ R : List Bool → List Bool, R ∈ FP ∧
      ∀ (G : ConstraintGraph A) (v d : ℕ), v < 2 * G.numEdges →
        d < 2 + 2 * (F.toFamily hd).degree →
        R (pair (encGraph G) (pair (List.replicate v true) (List.replicate d true))) =
          pair (List.replicate (G.preRotNum (F.toFamily hd) v d).1 true)
            (List.replicate (G.preRotNum (F.toFamily hd) v d).2 true) := by
  refine ⟨preRotFn F (2 * Polynomial.X) (F.toFamily hd).degree,
    preRotFn_mem_FP _ _ _, ?_⟩
  intro G v d hv hdlt
  apply preRotFn_eq G F (2 * Polynomial.X) hd v d hv hdlt
  · intro u
    simpa using F.fitLevel_le hd (G.cloudList u).length
  · simpa using F.fitLevel_le hd (2 * G.numEdges)

namespace RegularRelation

variable (A : Type) [Fintype A] [DecidableEq A]

/-- Arguments are `pair (pair (pair graph vertex) dart) (code (a,b))`. -/
def graphArg (z : List Bool) : List Bool := pairFst (pairFst (pairFst z))
def vertexArg (z : List Bool) : List Bool := pairSnd (pairFst (pairFst z))
def dartArg (z : List Bool) : List Bool := pairSnd (pairFst z)

theorem graph_arg_mem_FP : graphArg ∈ FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP

theorem vertex_arg_mem_FP : vertexArg ∈ FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

theorem dart_arg_mem_FP : dartArg ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

noncomputable def constraintKey (z : List Bool) : List Bool :=
  (recThd (pairSnd (graphArg z)) (vertexArg z).length.div2).take (Fintype.card (A → A → Bool))

theorem constraint_key_mem_FP : constraintKey A ∈ FP := by
  have hi : (fun z ↦ List.replicate ((vertexArg z).length / 2) true) ∈ FP :=
    (UnaryFn.div (UnaryFn.length vertex_arg_mem_FP) (UnaryFn.const 2)).mem_FP
  have hc := gCodeFn_mem_FP hi graph_arg_mem_FP
  have htake := take_mem_FP hc (Fintype.card (A → A → Bool))
  apply mem_FP_of_eq htake
  intro z
  simp only [constraintKey, List.length_replicate, Nat.div2_val]

noncomputable def key (deg : ℕ) (z : List Bool) : List Bool :=
  pair (constraintKey A z) (pair (List.replicate ((vertexArg z).length % 2) true)
    (pair ((dartArg z).take (2 + 2 * deg)) ((pairSnd z).take (Fintype.card (A × A)))))

theorem key_mem_FP (deg : ℕ) : key A deg ∈ FP :=
  mem_FP_pair (constraint_key_mem_FP A)
    (mem_FP_pair ((UnaryFn.mod (UnaryFn.length vertex_arg_mem_FP) (UnaryFn.const 2)).mem_FP)
      (mem_FP_pair (take_mem_FP dart_arg_mem_FP _) (take_mem_FP pairSnd_mem_FP _)))

theorem key_length (deg : ℕ) (z : List Bool) :
    (key A deg z).length ≤
      2 * Fintype.card (A → A → Bool) + 8 + 2 * (2 + 2 * deg) + Fintype.card (A × A) := by
  have hc : (constraintKey A z).length ≤ Fintype.card (A → A → Bool) :=
    List.length_take_le _ _
  have hd : ((dartArg z).take (2 + 2 * deg)).length ≤ 2 + 2 * deg := List.length_take_le _ _
  have ha : ((pairSnd z).take (Fintype.card (A × A))).length ≤ Fintype.card (A × A) :=
    List.length_take_le _ _
  have hv : (vertexArg z).length % 2 < 2 := Nat.mod_lt _ (by omega)
  simp only [key, pair_length, List.length_replicate]
  omega

noncomputable def readKey (deg : ℕ) (z : List Bool) : List Bool :=
  [((decode (pairSnd (pairSnd (pairSnd z))) : Option (A × A)).map fun ab ↦
      preRelCode A deg (pairFst z).length (pairFst (pairSnd z)).length
        (pairFst (pairSnd (pairSnd z))).length ab.1 ab.2).getD false]

noncomputable def flag (deg : ℕ) (z : List Bool) : List Bool := readKey A deg (key A deg z)

theorem flag_mem_FP (deg : ℕ) : flag A deg ∈ FP :=
  mem_FP_of_bounded_key (key_mem_FP A deg) (key_length A deg) (readKey A deg)

theorem flag_eq (deg : ℕ) (G : ConstraintGraph A) (v d : ℕ)
    (hv : v / 2 < G.numEdges) (hd : d < 2 + 2 * deg) (a b : A) :
    flag A deg (pair (pair (pair (encGraph G) (List.replicate v true)) (List.replicate d true))
      (code (a, b))) =
      [preRelCode A deg (codeOfRel (G.rel ⟨v / 2, hv⟩)) v d a b] := by
  have hc : (recThd (pairSnd (encGraph G)) (v / 2)).length = codeOfRel (G.rel ⟨v / 2, hv⟩) :=
    gCode_encGraph G (v / 2) hv
  have hclen : (recThd (pairSnd (encGraph G)) (v / 2)).length ≤ Fintype.card (A → A → Bool) :=
    hc ▸ (codeOfRel_lt _).le
  unfold flag readKey key constraintKey graphArg vertexArg dartArg
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate, Nat.div2_val,
    List.take_of_length_le hclen, List.take_replicate, Nat.min_eq_right hd.le,
    ← code_length (a, b), List.take_length, decode_code, Option.map_some, Option.getD_some,
    hc, preRelCode_mod]

end RegularRelation
end Lax323828Proofs.RegisteredBridge
