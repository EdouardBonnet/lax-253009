import Lax323828Proofs.RegisteredBridge.ComputableNumbering

set_option backward.isDefEq.respectTransparency false

namespace Lax323828Proofs.RegisteredBridge

open PCPFoundation.Complexity FiniteEncoding

namespace ComputableEncoding

variable {A B C : Family} {a : Encoding A} {b : Encoding B} {c : Encoding C}

def sum (a : Encoding A) (b : Encoding B) : Encoding (fun z ↦ A z ⊕ B z) :=
  fun z v ↦ match v with | .inl x => false :: a z x | .inr x => true :: b z x

theorem inl (a : Encoding A) (b : Encoding B) :
    Realizes a (sum a b) (fun _ v ↦ Sum.inl v) :=
  ⟨fun w ↦ false :: pairSnd w, Cobham.appendFn_mem_FP (constFn_mem_FP [false]) pairSnd_mem_FP,
    fun _ _ ↦ by simp [sum]⟩

theorem inr (a : Encoding A) (b : Encoding B) :
    Realizes b (sum a b) (fun _ v ↦ Sum.inr v) :=
  ⟨fun w ↦ true :: pairSnd w, Cobham.appendFn_mem_FP (constFn_mem_FP [true]) pairSnd_mem_FP,
    fun _ _ ↦ by simp [sum]⟩

theorem prod_sum_distrib (a : Encoding A) (b : Encoding B) (c : Encoding C) :
    Realizes (prod a (sum b c)) (sum (prod a b) (prod a c))
      (fun _ p ↦ Sum.elim (fun x ↦ Sum.inl (p.1, x)) (fun x ↦ Sum.inr (p.1, x)) p.2) := by
  let left : Word → Word := fun w ↦ pairFst (pairSnd w)
  let right : Word → Word := fun w ↦ pairSnd (pairSnd w)
  have hl : left ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hr : right ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  let payload : Word → Word := fun w ↦ pair (left w) ((right w).drop 1)
  have hp : payload ∈ FP := mem_FP_pair hl (drop_mem_FP hr 1)
  let read : Word → Bool := fun w ↦ w.head?.getD false
  refine ⟨fun w ↦ read ((right w).take 1) :: payload w,
    bounded_dispatch_mem_FP (take_mem_FP hr 1) (fun _ ↦ List.length_take_le _ _)
      read (fun b w ↦ b :: payload w)
      (fun b ↦ Cobham.appendFn_mem_FP (constFn_mem_FP [b]) hp), ?_⟩
  intro z p
  rcases p with ⟨v, x | y⟩ <;> simp [prod, sum, left, right, read, payload]

theorem sum_cases {f : ∀ z, A z → C z} {g : ∀ z, B z → C z}
    (hf : Realizes a c f) (hg : Realizes b c g) :
    Realizes (sum a b) c (fun z v ↦ Sum.elim (f z) (g z) v) := by
  obtain ⟨F, hF, hcF⟩ := hf
  obtain ⟨G, hG, hcG⟩ := hg
  let arg : Word → Word := fun w ↦ pair (pairFst w) ((pairSnd w).drop 1)
  have ha : arg ∈ FP := mem_FP_pair pairFst_mem_FP (drop_mem_FP pairSnd_mem_FP 1)
  let read : Word → Bool := fun w ↦ w.head?.getD false
  let branch : Bool → Word → Word := fun v w ↦ if v then G (arg w) else F (arg w)
  refine ⟨fun w ↦ branch (read ((pairSnd w).take 1)) w,
    bounded_dispatch_mem_FP (take_mem_FP pairSnd_mem_FP 1) (fun _ ↦ List.length_take_le _ _)
      read branch (fun v ↦ ?_), ?_⟩
  · cases v
    · exact mem_FP_comp ha hF
    · exact mem_FP_comp ha hG
  · intro z v
    cases v <;> simp [sum, read, branch, arg, hcF, hcG]

theorem prod_sum_cases {D : Family} {d : Encoding D}
    {f : ∀ z, A z × B z → D z} {g : ∀ z, A z × C z → D z}
    (hf : Realizes (prod a b) d f) (hg : Realizes (prod a c) d g) :
    Realizes (prod a (sum b c)) d
      (fun z p ↦ Sum.elim (fun x ↦ f z (p.1, x)) (fun x ↦ g z (p.1, x)) p.2) := by
  have h := comp (prod_sum_distrib a b c) (sum_cases hf hg)
  apply of_pointwise h
  intro z p
  rcases p with ⟨v, x | y⟩ <;> rfl

end ComputableEncoding

namespace ComputableNumbering

open ComputableEncoding

variable {A B : Family} {a : Encoding A} {b : Encoding B}

theorem sum_index (p : Numbering a) (q : Numbering b) :
    Realizes (ComputableEncoding.sum a b) (unary (fun z ↦ p.size z + q.size z))
      (fun z v ↦ finSumFinEquiv (Sum.map (p.equiv z) (q.equiv z) v)) := by
  have hl : Realizes a (unary (fun z ↦ p.size z + q.size z))
      (fun z v ↦ Fin.castAdd (q.size z) (p.equiv z v)) := by
    obtain ⟨F, hF, hc⟩ := p.index
    exact ⟨F, hF, hc⟩
  have hr : Realizes b (unary (fun z ↦ p.size z + q.size z))
      (fun z v ↦ Fin.natAdd (p.size z) (q.equiv z v)) := by
    obtain ⟨F, hF, hc⟩ := q.index
    refine ⟨fun w ↦ List.replicate (p.size (pairFst w) + (F w).length) true,
      ((p.size_poly.comp pairFst_mem_FP).add (UnaryFn.length hF)).mem_FP, ?_⟩
    intro z v
    simp only [pairFst_pair, hc, unary, List.length_replicate]
    rfl
  have h := sum_cases hl hr
  apply of_pointwise h
  intro z v
  cases v <;> rfl

theorem sum_element (p : Numbering a) (q : Numbering b) :
    Realizes (unary (fun z ↦ p.size z + q.size z)) (ComputableEncoding.sum a b)
      (fun z v ↦ Sum.map (p.equiv z).symm (q.equiv z).symm
        ((@finSumFinEquiv (p.size z) (q.size z)).symm v)) := by
  obtain ⟨F, hF, hcF⟩ := p.element
  obtain ⟨G, hG, hcG⟩ := q.element
  let right : Word → Word := fun w ↦
    pair (pairFst w) (List.replicate ((pairSnd w).length - p.size (pairFst w)) true)
  have hright : right ∈ FP := mem_FP_pair pairFst_mem_FP
    ((UnaryFn.length pairSnd_mem_FP).sub (p.size_poly.comp pairFst_mem_FP)).mem_FP
  refine ⟨fun w ↦ if (pairSnd w).length < p.size (pairFst w) then false :: F w else true :: G (right w),
    (FPPred.lt (UnaryFn.length pairSnd_mem_FP) (p.size_poly.comp pairFst_mem_FP)).ite_mem_FP
      (Cobham.appendFn_mem_FP (constFn_mem_FP [false]) hF)
      (Cobham.appendFn_mem_FP (constFn_mem_FP [true]) (mem_FP_comp hright hG)), ?_⟩
  intro z v
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) v
  · simp only [unary, Fin.val_castAdd, pairFst_pair, pairSnd_pair, List.length_replicate,
      if_pos i.isLt, finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, ComputableEncoding.sum]
    exact congrArg (List.cons false) (hcF z i)
  · simp only [unary, Fin.val_natAdd, pairFst_pair, pairSnd_pair, List.length_replicate,
      Nat.not_lt.mpr (Nat.le_add_right _ _), if_false, finSumFinEquiv_symm_apply_natAdd,
      Sum.map_inr, ComputableEncoding.sum]
    congr 1
    simpa only [right, pairFst_pair, pairSnd_pair, unary, List.length_replicate, Nat.add_sub_cancel_left]
      using hcG z j

noncomputable def sum (p : Numbering a) (q : Numbering b) : Numbering (ComputableEncoding.sum a b) where
  size := fun z ↦ p.size z + q.size z
  equiv := fun z ↦ (Equiv.sumCongr (p.equiv z) (q.equiv z)).trans finSumFinEquiv
  size_poly := p.size_poly.add q.size_poly
  index := sum_index p q
  element := sum_element p q

end ComputableNumbering
end Lax323828Proofs.RegisteredBridge
