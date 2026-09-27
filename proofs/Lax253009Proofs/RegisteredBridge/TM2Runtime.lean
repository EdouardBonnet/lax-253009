import Lax253009Proofs.RegisteredBridge.TM2Encoding
import Lax253009Proofs.PCPFoundation.Classes.P.Iterate

namespace Lax253009Proofs.RegisteredBridge.StackEncoding

open PCPFoundation.Complexity FiniteEncoding Turing
open scoped BigOperators

variable {K Λ σ : Type} {Γ : K → Type}
  [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [Nonempty σ]
  [∀ k, Fintype (Γ k)]

/-- A halted machine remains at its final configuration. -/
def totalStep (M : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ σ :=
  match c.l with
  | none => c
  | some l => TM2.stepAux (M l) c.var c.stk

theorem compile_step (M : Λ → TM2.Stmt Γ Λ σ) :
    ∃ F : List Bool → List Bool, F ∈ FP ∧
      ∀ c : TM2.Cfg Γ Λ σ, F (encode c) = encode (totalStep M c) := by
  classical
  choose f hf hsim using fun l ↦ compile_statement (M l)
  let F : List Bool → List Bool := fun z ↦
    match (readState Λ σ z).1 with
    | none => z
    | some l => f l z
  refine ⟨F, ?_, ?_⟩
  · apply state_dispatch_mem_FP (fun q z ↦ match q.1 with | none => z | some l => f l z)
    intro q
    cases q.1
    · exact CobhamFP_subset_FP (Cobham.proj (0 : Fin 1))
    · exact hf _
  · intro c
    dsimp only [F]
    rw [read_state_encode]
    cases h : c.l <;> simp only [h, totalStep, hsim]

def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .pop _ _ q | .peek _ _ q | .load _ q => pushes q
  | .branch _ p q => max (pushes p) (pushes q)
  | .goto _ | .halt => 0

theorem stepAux_length (q : TM2.Stmt Γ Λ σ) (v : σ)
    (s : (k : K) → List (Γ k)) (k : K) :
    ((TM2.stepAux q v s).stk k).length ≤ (s k).length + pushes q := by
  induction q generalizing v s with
  | push j f q ih =>
    have h := ih v (Function.update s j (f v :: s j))
    have hu : ((Function.update s j (f v :: s j)) k).length ≤ (s k).length + 1 := by
      by_cases hj : k = j
      · subst k; simp
      · simp [Function.update_of_ne hj]
    dsimp only [TM2.stepAux, pushes]
    omega
  | pop j f q ih =>
    have h := ih (f v (s j).head?) (Function.update s j (s j).tail)
    have hu : ((Function.update s j (s j).tail) k).length ≤ (s k).length := by
      by_cases hj : k = j
      · subst k; simp
      · simp [Function.update_of_ne hj]
    dsimp only [TM2.stepAux, pushes]
    omega
  | peek j f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f p q ihp ihq =>
    cases hf : f v
    · simpa only [TM2.stepAux, pushes, hf, Bool.cond_false] using
        (ihq v s).trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
    · simpa only [TM2.stepAux, pushes, hf, Bool.cond_true] using
        (ihp v s).trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  | goto f => simp [TM2.stepAux, pushes]
  | halt => simp [TM2.stepAux, pushes]

noncomputable def growth (M : Λ → TM2.Stmt Γ Λ σ) : ℕ := ∑ l, pushes (M l)

theorem total_step_length (M : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) (k : K) :
    ((totalStep M c).stk k).length ≤ (c.stk k).length + growth M := by
  classical
  cases hl : c.l with
  | none => simp [totalStep, hl]
  | some l =>
    simp only [totalStep, hl]
    exact (stepAux_length (M l) c.var c.stk k).trans (Nat.add_le_add_left
      (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (pushes (M j))) (Finset.mem_univ l)) _)

theorem total_run_length (M : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) (t : ℕ) (k : K) :
    (((totalStep M)^[t] c).stk k).length ≤ (c.stk k).length + growth M * t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have h := total_step_length M ((totalStep M)^[t] c) k
    rw [Nat.mul_succ]
    omega

theorem encode_length_bound : ∃ a b : ℕ, ∀ c : TM2.Cfg Γ Λ σ, ∀ n : ℕ,
    (∀ k, (c.stk k).length ≤ n) → (encode c).length ≤ a * n + b := by
  let m := Fintype.card K
  let w : Fin m → ℕ := fun i ↦ Fintype.card (Γ ((Fintype.equivFin K).symm i)) + 1
  refine ⟨2 ^ m * ∑ i, w i,
    2 * Fintype.card (Control Λ σ) + 2 + 2 ^ m * (2 * m), ?_⟩
  intro c n hn
  have h := Cobham.encodeVec_length_le (fun i : Fin m ↦
    packets (c.stk ((Fintype.equivFin K).symm i)))
  have hs : (∑ i : Fin m, (packets (c.stk ((Fintype.equivFin K).symm i))).length) ≤
      (∑ i, w i) * n := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [packets_length]
    exact Nat.mul_le_mul_left _ (hn _)
  simp only [encode, pair_length, code_length]
  have hh := h.trans (Nat.mul_le_mul_left (2 ^ m) (Nat.add_le_add_right hs (2 * m)))
  nlinarith

/-- A polynomially clocked stack-machine execution is an `FP` function on encodings. -/
theorem compile_run (M : Λ → TM2.Stmt Γ Λ σ)
    (start : List Bool → TM2.Cfg Γ Λ σ) (ruler : List Bool → List Bool)
    (hstart : (fun z ↦ encode (start z)) ∈ FP) (hruler : ruler ∈ FP)
    (hstart_len : ∀ z k, ((start z).stk k).length ≤ z.length) :
    (fun z ↦ encode ((totalStep M)^[(ruler z).length] (start z))) ∈ FP := by
  obtain ⟨F, hF, hsim⟩ := compile_step M
  obtain ⟨a, b, hab⟩ := encode_length_bound (Γ := Γ) (Λ := Λ) (σ := σ)
  obtain ⟨q, hq⟩ := Cobham.output_length_poly_of_mem_FP hruler
  have hsemi : Function.Semiconj encode (totalStep M) F := fun c ↦ (hsim c).symm
  have h := iterate_mem_FP_of_polyBound hF hstart hruler
    (((PolyBound.const a).mul (PolyBound.id.add
      ((PolyBound.const (growth M)).mul (PolyBound.eval q)))).add (PolyBound.const b))
    (fun z t ht ↦ ?bound)
  · exact mem_FP_of_eq h (fun z ↦ (hsemi.iterate_right _ (start z)).symm)
  case bound =>
    rw [← hsemi.iterate_right t (start z)]
    apply hab
    intro k
    exact (total_run_length M (start z) t k).trans (Nat.add_le_add (hstart_len z k)
      (Nat.mul_le_mul_left _ (ht.trans (hq z))))

end Lax253009Proofs.RegisteredBridge.StackEncoding
