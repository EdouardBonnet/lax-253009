import Lax253009.GapSatisfiability
import Lax253009Proofs.ProjectionGames
import Lax253009Proofs.PCPFoundation.Classes.PCP.Internal.GapTheorem

set_option maxRecDepth 1024

namespace Lax253009Proofs

open Lax253009 Lax253009.ProjectionGames Lax253009.FiniteProbability
open Lax253009Proofs.PCPFoundation.Complexity

attribute [local irreducible] Lax253009Proofs.PCPFoundation.Complexity.algFamily

namespace GapBridge

def formula (φ : GapSatisfiability.Formula) : SAT.CNF :=
  φ.map (List.map fun l ↦ ⟨l.1, l.2⟩)

@[simp] theorem formula_length (φ : GapSatisfiability.Formula) :
    (formula φ).length = φ.length := List.length_map _

theorem formula_three (φ : GapSatisfiability.Formula) (h : GapSatisfiability.Is3CNF φ) :
    (formula φ).Is3CNF := by
  simpa [SAT.CNF.Is3CNF, formula, GapSatisfiability.Is3CNF] using h

theorem formula_satisfiable (φ : GapSatisfiability.Formula) :
    (formula φ).Satisfiable ↔ GapSatisfiability.Satisfiable φ := by
  simp [formula, SAT.CNF.Satisfiable, SAT.CNF.eval, SAT.Clause.eval,
    SAT.Lit.eval, SAT.Assignment.get, GapSatisfiability.Satisfiable]

def system {A : Type} (R : RegCSP A) : System R.graph.V R.graph.D A where
  reverse := R.graph.rot
  reverse_involutive := R.graph.rot_involutive
  relation z := R.rel z.1 z.2

theorem system_complete {A : Type} (R : RegCSP A) (h : R.Satisfiable) :
    (system R).Satisfiable := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun z hv ↦ hv (ha z)⟩

theorem system_fraction {A : Type} (R : RegCSP A) (a : R.Assignment) :
    probability ((system R).Violated a) = (R.unsatFrac a : ℝ) := by
  classical
  have hf : Finset.univ.filter ((system R).Violated a) = R.unsatDarts a := by
    unfold RegCSP.unsatDarts
    apply Finset.filter_congr
    intro z _
    rfl
  unfold probability RegCSP.unsatFrac
  rw [hf, R.card_dart]
  push_cast
  rfl

theorem system_sound {A : Type} [Fintype A] [Nonempty A] (R : RegCSP A)
    (γ : ℝ) (h : γ ≤ (R.unsatVal : ℝ)) : (system R).Sound γ := by
  intro a
  rw [system_fraction]
  exact h.trans (by exact_mod_cast R.unsatVal_le a)

def relabel {V D A V' D' A' : Type} (C : System V D A)
    (ev : V ≃ V') (ed : D ≃ D') (ea : A ≃ A') : System V' D' A' where
  reverse z := (Equiv.prodCongr ev ed) (C.reverse ((Equiv.prodCongr ev ed).symm z))
  reverse_involutive := by
    intro z
    simp only [Equiv.symm_apply_apply, projection_reverse_reverse, Equiv.apply_symm_apply]
  relation z a b := C.relation ((Equiv.prodCongr ev ed).symm z) (ea.symm a) (ea.symm b)

theorem relabel_complete {V D A V' D' A' : Type} (C : System V D A)
    (ev : V ≃ V') (ed : D ≃ D') (ea : A ≃ A') (h : C.Satisfiable) :
    (relabel C ev ed ea).Satisfiable := by
  obtain ⟨a, ha⟩ := h
  refine ⟨fun v ↦ ea (a (ev.symm v)), ?_⟩
  intro z
  simpa [System.Violated, relabel] using ha ((Equiv.prodCongr ev ed).symm z)

theorem relabel_sound {V D A V' D' A' : Type}
    [Fintype V] [Fintype D] [Fintype V'] [Fintype D']
    (C : System V D A) (ev : V ≃ V') (ed : D ≃ D') (ea : A ≃ A')
    (γ : ℝ) (h : C.Sound γ) : (relabel C ev ed ea).Sound γ := by
  intro a
  have he := finite_probability_equiv (Equiv.prodCongr ev ed)
    (C.Violated (fun v ↦ ea.symm (a (ev v)))) ((relabel C ev ed ea).Violated a)
    (fun z ↦ by rcases z with ⟨v, d⟩; simp [System.Violated, relabel])
  rw [← he]
  exact h _

noncomputable def regular (φ : GapSatisfiability.Formula) : RegCSP DinurAlpha :=
  (gapGraph (formula φ)).preprocess algFamily

noncomputable def gap : ℝ :=
  ConstraintGraph.preprocessConst algFamily DinurAlpha * (dinurAmp.gap : ℝ)

theorem gap_pos : 0 < gap := mul_pos (Dinur.preprocessConst_pos algFamily)
  (by exact_mod_cast dinurAmp_gap_pos)

theorem regular_complete (φ : GapSatisfiability.Formula)
    (h3 : GapSatisfiability.Is3CNF φ) (h : GapSatisfiability.Satisfiable φ) :
    (regular φ).Satisfiable :=
  ConstraintGraph.satisfiable_preprocess_of_satisfiable _ _
    (satisfiable_gapGraph (formula_three φ h3) ((formula_satisfiable φ).mpr h))

theorem regular_sound (φ : GapSatisfiability.Formula)
    (h3 : GapSatisfiability.Is3CNF φ) (h : ¬ GapSatisfiability.Satisfiable φ) :
    gap ≤ ((regular φ).unsatVal : ℝ) := by
  apply le_trans _ ((gapGraph (formula φ)).le_unsatVal_preprocess algFamily)
  apply mul_le_mul_of_nonneg_left _ (Dinur.preprocessConst_pos algFamily).le
  exact_mod_cast gap_le_unsatVal_gapGraph (formula_three φ h3)
    (fun hs ↦ h ((formula_satisfiable φ).mp hs))

noncomputable def exponent : ℕ := Nat.log 2 dinurAmp.edgeFactor + 2
noncomputable def sizeConstant : ℕ := 6 * 8 ^ (Nat.log 2 dinurAmp.edgeFactor + 1) + 1

private theorem size_bound (m E N : ℕ)
    (hb : N ≤ (2 * (3 * m) + 2) ^ (Nat.log 2 E + 1) * (3 * m)) :
    2 * N ≤ (6 * 8 ^ (Nat.log 2 E + 1) + 1) * (m + 1) ^ (Nat.log 2 E + 2) := by
  have hbase : 2 * (3 * m) + 2 ≤ 8 * (m + 1) := by omega
  have hpow := Nat.pow_le_pow_left hbase (Nat.log 2 E + 1)
  have hh := Nat.mul_le_mul hpow (show 3 * m ≤ 3 * (m + 1) by omega)
  calc
    _ ≤ 2 * ((8 * (m + 1)) ^ (Nat.log 2 E + 1) * (3 * (m + 1))) :=
      Nat.mul_le_mul_left 2 (hb.trans hh)
    _ = (6 * 8 ^ (Nat.log 2 E + 1)) * (m + 1) ^ (Nat.log 2 E + 2) := by
      rw [show Nat.log 2 E + 2 = (Nat.log 2 E + 1) + 1 from rfl, mul_pow, pow_succ]
      ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ _)

private theorem preprocessed_size {A : Type} [Fintype A] [DecidableEq A]
    (G : ConstraintGraph A) (F : ExpanderFamily) (m E : ℕ)
    (hb : G.numEdges ≤ (2 * (3 * m) + 2) ^ (Nat.log 2 E + 1) * (3 * m)) :
    (G.preprocess F).graph.order ≤
      (6 * 8 ^ (Nat.log 2 E + 1) + 1) * (m + 1) ^ (Nat.log 2 E + 2) :=
  (G.order_preprocess F).le.trans (size_bound m E G.numEdges hb)

theorem regular_size (φ : GapSatisfiability.Formula) :
    (regular φ).graph.order ≤ sizeConstant * (φ.length + 1) ^ exponent := by
  have h := preprocessed_size (gapGraph (formula φ)) algFamily
    (formula φ).length dinurAmp.edgeFactor (numEdges_gapGraph_le (formula φ))
  simpa only [regular, sizeConstant, exponent, formula_length] using h

def trivial (a d : ℕ) : System (Fin 1) (Fin d) (Fin a) where
  reverse := id
  reverse_involutive := fun _ ↦ rfl
  relation := fun _ _ _ ↦ true

theorem trivial_complete (a d : ℕ) (ha : 0 < a) : (trivial a d).Satisfiable :=
  ⟨fun _ ↦ ⟨0, ha⟩, fun _ h ↦ h rfl⟩

theorem regular_empty_satisfiable (φ : GapSatisfiability.Formula)
    (h3 : GapSatisfiability.Is3CNF φ) (h0 : (regular φ).graph.order = 0) :
    GapSatisfiability.Satisfiable φ := by
  classical
  by_contra hn
  have hs := regular_sound φ h3 hn
  have hz := (regular φ).unsatVal_le (fun _ ↦ Classical.arbitrary DinurAlpha)
  have hz' : (regular φ).unsatVal ≤ 0 := by
    simpa only [RegCSP.unsatFrac, h0, zero_mul, Nat.cast_zero, div_zero] using hz
  have hz'' : ((regular φ).unsatVal : ℝ) ≤ 0 := by exact_mod_cast hz'
  linarith [gap_pos]

end GapBridge

/--
---
conclusion: Lax253009.GapSatisfiability.regular_gap
---
Apply the ported Dinur gap amplifier, regularize with its fixed expander
family, and number the finite label, vertex, and dart-label spaces.
An empty output can occur only on satisfiable inputs and is replaced
by one unconstrained vertex of the same fixed degree.
-/
theorem regular_gap_satisfiability :
  ∃ a d K e : ℕ, 0 < a ∧ 0 < d ∧ 0 < K ∧
    ∃ γ : ℝ, 0 < γ ∧
      ∀ φ : GapSatisfiability.Formula, GapSatisfiability.Is3CNF φ →
        ∃ n : ℕ, 0 < n ∧ n ≤ K * (φ.length + 1) ^ e ∧
          ∃ C : System (Fin n) (Fin d) (Fin a),
            (GapSatisfiability.Satisfiable φ → C.Satisfiable) ∧
              (¬ GapSatisfiability.Satisfiable φ → C.Sound γ) := by
  classical
  let a := Fintype.card DinurAlpha
  let d := 2 + 2 * algFamily.degree
  have ha : 0 < a := Fintype.card_pos
  refine ⟨a, d, GapBridge.sizeConstant, GapBridge.exponent, ha, by omega,
    by unfold GapBridge.sizeConstant; positivity, GapBridge.gap, GapBridge.gap_pos, ?_⟩
  intro φ h3
  let R := GapBridge.regular φ
  by_cases hpos : 0 < R.graph.order
  · let ev := Fintype.equivFin R.graph.V
    let ed : R.graph.D ≃ Fin d := (Fintype.equivFin R.graph.D).trans
      (finCongr ((gapGraph (GapBridge.formula φ)).deg_preprocess algFamily))
    let ea := Fintype.equivFin DinurAlpha
    refine ⟨R.graph.order, hpos, GapBridge.regular_size φ,
      GapBridge.relabel (GapBridge.system R) ev ed ea, ?_, ?_⟩
    · intro hsat
      exact GapBridge.relabel_complete _ ev ed ea
        (GapBridge.system_complete R (GapBridge.regular_complete φ h3 hsat))
    · intro hno
      exact GapBridge.relabel_sound _ ev ed ea _
        (GapBridge.system_sound R _ (GapBridge.regular_sound φ h3 hno))
  · refine ⟨1, by decide, ?_, GapBridge.trivial a d, ?_, ?_⟩
    · have : 0 < GapBridge.sizeConstant * (φ.length + 1) ^ GapBridge.exponent := by
        unfold GapBridge.sizeConstant
        positivity
      exact this
    · exact fun _ ↦ GapBridge.trivial_complete a d ha
    · intro hno
      exact (hno (GapBridge.regular_empty_satisfiable φ h3
        (Nat.eq_zero_of_not_pos hpos))).elim

end Lax253009Proofs
