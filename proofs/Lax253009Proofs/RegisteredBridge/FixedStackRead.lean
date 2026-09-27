import Lax253009Proofs.RegisteredBridge.StackSubroutine
import Lax253009Proofs.RegisteredBridge.FiniteWordEncoding

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Lax253009Proofs.RegisteredBridge.FixedStackRead

open Turing Function StackSubroutine
open scoped Classical

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]
variable {N : ℕ}

def program (k : K) (decode : Γ k → Bool) (v : Lens (Fin N → Bool) σ)
    (tail : TM2.Stmt Γ Λ σ) : List (Fin N) → TM2.Stmt Γ Λ σ
  | [] => tail
  | i :: is => .pop k
      (fun s a ↦ v.put s (update (v.get s) i ((a.map decode).getD false)))
      (program k decode v tail is)

def assign (h : Fin N → Bool) (u : Fin N → Bool) (is : List (Fin N)) : Fin N → Bool :=
  is.foldl (fun u i ↦ update u i (h i)) u

theorem assign_apply (h u : Fin N → Bool) (is : List (Fin N)) (j : Fin N) :
    assign h u is j = if j ∈ is then h j else u j := by
  induction is generalizing u with
  | nil => simp [assign]
  | cons i is ih =>
    simp only [assign, List.foldl_cons] at *
    rw [ih]
    by_cases hji : j = i
    · subst j; simp
    · simp [hji, update_of_ne hji]

theorem assign_all (h u : Fin N → Bool) : assign h u (List.finRange N) = h := by
  funext j
  simp [assign_apply]

theorem block (k : K) (encode : Bool → Γ k) (decode : Γ k → Bool)
    (hd : ∀ b, decode (encode b) = b) (v : Lens (Fin N → Bool) σ)
    (tail : TM2.Stmt Γ Λ σ) (is : List (Fin N)) (h : Fin N → Bool)
    (s : σ) (S : ∀ k, List (Γ k)) (rest : List (Γ k)) :
    TM2.stepAux (program k decode v tail is) s
      (update S k (is.map (fun i ↦ encode (h i)) ++ rest)) =
    TM2.stepAux tail (v.put s (assign h (v.get s) is)) (update S k rest) := by
  induction is generalizing s with
  | nil => simp [program, assign, v.put_get]
  | cons i is ih =>
    simp only [program, TM2.stepAux, update_self, List.map_cons, List.cons_append,
      List.head?_cons, Option.map_some, Option.getD_some, hd, List.tail_cons, update_idem]
    rw [ih]
    simp only [v.get_put, v.put_put, assign, List.foldl_cons]

theorem all (k : K) (encode : Bool → Γ k) (decode : Γ k → Bool)
    (hd : ∀ b, decode (encode b) = b) (v : Lens (Fin N → Bool) σ)
    (tail : TM2.Stmt Γ Λ σ) (h : Fin N → Bool)
    (s : σ) (S : ∀ k, List (Γ k)) (rest : List (Γ k)) :
    TM2.stepAux (program k decode v tail (List.finRange N)) s
      (update S k ((List.ofFn h).map encode ++ rest)) =
    TM2.stepAux tail (v.put s h) (update S k rest) := by
  have he : (List.finRange N).map (fun i ↦ encode (h i)) = (List.ofFn h).map encode := by
    apply List.ext_getElem
    · simp
    · intro i hi hj; simp
  simpa only [he, assign_all] using block k encode decode hd v tail (List.finRange N) h s S rest

end Lax253009Proofs.RegisteredBridge.FixedStackRead
