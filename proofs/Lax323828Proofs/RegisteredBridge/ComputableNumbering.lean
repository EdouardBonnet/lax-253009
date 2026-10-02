import Lax323828Proofs.RegisteredBridge.ComputableEncodings
import Mathlib.Logic.Equiv.Fin.Basic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax323828Proofs.RegisteredBridge.ComputableNumbering

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding

def unary (n : Word → ℕ) : Encoding (fun z ↦ Fin (n z)) :=
  fun _ i ↦ List.replicate i.val true

/-- An explicit polynomial-time numbering, in both directions, of a family
of finite encoded sets. Its cardinality is available in unary. -/
structure Numbering {A : Family} (e : Encoding A) where
  size : Word → ℕ
  equiv : ∀ z, A z ≃ Fin (size z)
  size_poly : UnaryFn size
  index : Realizes e (unary size) (fun z ↦ equiv z)
  element : Realizes (unary size) e (fun z ↦ (equiv z).symm)

noncomputable def finite {X : Type} [Fintype X] (ex : X → Word) (hx : Function.Injective ex) :
    Numbering (fun _ ↦ ex) where
  size := fun _ ↦ Fintype.card X
  equiv := fun _ ↦ Fintype.equivFin X
  size_poly := UnaryFn.const _
  index := fixed_map ex hx (fun i : Fin (Fintype.card X) ↦ List.replicate i.val true) (Fintype.equivFin X)
  element := fixed_map (fun i : Fin (Fintype.card X) ↦ List.replicate i.val true)
    (fun i j h ↦ Fin.ext (by simpa only [List.length_replicate] using congrArg List.length h))
    ex (Fintype.equivFin X).symm

noncomputable def fin (n : Word → ℕ) (hn : UnaryFn n) : Numbering (unary n) where
  size := n
  equiv := fun _ ↦ Equiv.refl _
  size_poly := hn
  index := identity _
  element := identity _

variable {A B : Family} {a : Encoding A} {b : Encoding B}

theorem product_index (p : Numbering a) (q : Numbering b) :
    Realizes (prod a b) (unary (fun z ↦ p.size z * q.size z))
      (fun z v ↦ finProdFinEquiv (p.equiv z v.1, q.equiv z v.2)) := by
  obtain ⟨F, hF, hFc⟩ := comp (fst a b) p.index
  obtain ⟨G, hG, hGc⟩ := comp (snd a b) q.index
  have hnum := (UnaryFn.length hG).add
    ((q.size_poly.comp pairFst_mem_FP).mul (UnaryFn.length hF))
  refine ⟨fun w ↦ List.replicate ((G w).length + q.size (pairFst w) * (F w).length) true,
    hnum.mem_FP, ?_⟩
  intro z v
  simp only [hFc, hGc, unary, List.length_replicate, pairFst_pair]
  rfl

theorem product_element (p : Numbering a) (q : Numbering b) :
    Realizes (unary (fun z ↦ p.size z * q.size z)) (prod a b)
      (fun z v ↦ ((p.equiv z).symm ((@finProdFinEquiv (p.size z) (q.size z)).symm v).1,
        (q.equiv z).symm ((@finProdFinEquiv (p.size z) (q.size z)).symm v).2)) := by
  obtain ⟨F, hF, hFc⟩ := p.element
  obtain ⟨G, hG, hGc⟩ := q.element
  have hd := (UnaryFn.length pairSnd_mem_FP).div (q.size_poly.comp pairFst_mem_FP)
  have hm := (UnaryFn.length pairSnd_mem_FP).mod (q.size_poly.comp pairFst_mem_FP)
  let leftArg : Word → Word := fun w ↦
    pair (pairFst w) (List.replicate ((pairSnd w).length / q.size (pairFst w)) true)
  let rightArg : Word → Word := fun w ↦
    pair (pairFst w) (List.replicate ((pairSnd w).length % q.size (pairFst w)) true)
  refine ⟨fun w ↦ pair (F (leftArg w)) (G (rightArg w)),
    mem_FP_pair (mem_FP_comp (mem_FP_pair pairFst_mem_FP hd.mem_FP) hF)
      (mem_FP_comp (mem_FP_pair pairFst_mem_FP hm.mem_FP) hG), ?_⟩
  intro z v
  change pair (F (leftArg (pair z (unary (fun w ↦ p.size w * q.size w) z v)))) (G (rightArg (pair z (unary (fun w ↦ p.size w * q.size w) z v)))) = _
  have hl : leftArg (pair z (unary (fun w ↦ p.size w * q.size w) z v)) =
      pair z (unary p.size z ((@finProdFinEquiv (p.size z) (q.size z)).symm v).1) := by
    simp only [leftArg, pairFst_pair, pairSnd_pair, unary, List.length_replicate]
    rfl
  have hr : rightArg (pair z (unary (fun w ↦ p.size w * q.size w) z v)) =
      pair z (unary q.size z ((@finProdFinEquiv (p.size z) (q.size z)).symm v).2) := by
    simp only [rightArg, pairFst_pair, pairSnd_pair, unary, List.length_replicate]
    rfl
  rw [hl, hr, hFc, hGc]
  rfl

noncomputable def product (p : Numbering a) (q : Numbering b) : Numbering (prod a b) where
  size := fun z ↦ p.size z * q.size z
  equiv := fun z ↦ (Equiv.prodCongr (p.equiv z) (q.equiv z)).trans finProdFinEquiv
  size_poly := p.size_poly.mul q.size_poly
  index := product_index p q
  element := product_element p q

noncomputable def transport (p : Numbering a) (r : ∀ z, B z ≃ A z) :
    Numbering (fun z v ↦ a z (r z v)) where
  size := p.size
  equiv := fun z ↦ (r z).trans (p.equiv z)
  size_poly := p.size_poly
  index := by
    obtain ⟨F, hF, hc⟩ := p.index
    exact ⟨F, hF, fun z v ↦ hc z (r z v)⟩
  element := by
    obtain ⟨F, hF, hc⟩ := p.element
    refine ⟨F, hF, fun z v ↦ ?_⟩
    change F (pair z (unary p.size z v)) = a z (r z ((r z).symm ((p.equiv z).symm v)))
    rw [Equiv.apply_symm_apply]
    exact hc z v

def emptyTupleEquiv (A : Type) : (Fin 0 → A) ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := Fin.elim0
  left_inv f := by funext i; exact Fin.elim0 i
  right_inv u := by cases u; rfl

def tupleSuccEquiv (n : ℕ) (A : Type) : (Fin (n + 1) → A) ≃ (Fin n → A) × A where
  toFun f := (Fin.tail f, f 0)
  invFun p := Fin.cons p.2 p.1
  left_inv f := by funext i; exact Fin.cases rfl (fun _ ↦ rfl) i
  right_inv p := by cases p; rfl

noncomputable def tuples (p : Numbering a) : (n : ℕ) → Numbering (ComputableEncoding.tuple a n)
  | 0 => transport (finite (fun _ : PUnit ↦ []) (fun _ _ _ ↦ Subsingleton.elim _ _))
      (fun z ↦ emptyTupleEquiv (A z))
  | n + 1 => transport (product (tuples p n) p) (fun z ↦ tupleSuccEquiv n (A z))

theorem encoding_injective (p : Numbering a) : ∀ z, Function.Injective (a z) := by
  obtain ⟨F, _, hc⟩ := p.index
  intro z u v h
  apply (p.equiv z).injective
  apply Fin.ext
  have he : unary p.size z (p.equiv z u) = unary p.size z (p.equiv z v) := by
    rw [← hc z u, ← hc z v, h]
  simpa only [unary, List.length_replicate] using congrArg List.length he

theorem tuples_size (p : Numbering a) (n : ℕ) (z : Word) :
    (tuples p n).size z = p.size z ^ n := by
  induction n with
  | zero => simp [tuples, transport, finite]
  | succ n ih =>
    simpa only [tuples, transport, product, pow_succ] using
      (congrArg (fun x ↦ x * p.size z) ih)

theorem encoding_size_bound (p : Numbering a) :
    ∃ q : Polynomial ℕ, ∀ z v, (a z v).length ≤ q.eval z.length := by
  obtain ⟨q, hq⟩ := Cobham.output_length_poly_of_mem_FP p.size_poly.mem_FP
  have hsize : ∀ z, p.size z ≤ q.eval z.length := by
    intro z
    simpa only [List.length_replicate] using hq z
  obtain ⟨F, hF, hFc⟩ := p.element
  obtain ⟨r, hr⟩ := Cobham.output_length_poly_of_mem_FP hF
  refine ⟨r.comp (Polynomial.C 2 * Polynomial.X + 2 + q), fun z v ↦ ?_⟩
  have h := hr (pair z (unary p.size z (p.equiv z v)))
  rw [hFc] at h
  simp only [Equiv.symm_apply_apply] at h
  apply h.trans
  rw [Polynomial.eval_comp]
  apply polynomial_eval_mono_nat
  simp only [pair_length, unary, List.length_replicate, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  have hi := (p.equiv z v).isLt
  have hs := hsize z
  omega

end Lax323828Proofs.RegisteredBridge.ComputableNumbering
