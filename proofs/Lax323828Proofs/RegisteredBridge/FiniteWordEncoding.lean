import Lax323828Proofs.PCPFoundation.Classes.P.Cobham
import Lax323828Proofs.PCPFoundation.Classes.P.Pairing
import Lax323828Proofs.PCPFoundation.Classes.P.FinsetDomain
import Lax323828Proofs.PCPFoundation.Classes.P.Unary
import Mathlib.Tactic

namespace Lax323828Proofs.RegisteredBridge

open PCPFoundation.Complexity
open scoped BigOperators

namespace FiniteEncoding

noncomputable def code {A : Type} [Fintype A] (a : A) : List Bool := by
  classical
  exact List.ofFn fun i : Fin (Fintype.card A) ↦ decide (Fintype.equivFin A a = i)

@[simp] theorem code_length {A : Type} [Fintype A] (a : A) :
    (code a).length = Fintype.card A := List.length_ofFn

theorem code_injective {A : Type} [Fintype A] : Function.Injective (@code A _) := by
  classical
  intro a b hab
  have hf := List.ofFn_injective hab
  have hh := congrFun hf (Fintype.equivFin A a)
  simp only [decide_true, true_eq_decide_iff] at hh
  exact (Fintype.equivFin A).injective hh.symm

noncomputable def decode {A : Type} [Fintype A] (w : List Bool) : Option A := by
  classical
  exact if h : ∃ a : A, code a = w then some h.choose else none

@[simp] theorem decode_code {A : Type} [Fintype A] (a : A) : decode (code a) = some a := by
  classical
  unfold decode
  rw [dif_pos ⟨a, rfl⟩]
  congr 1
  exact code_injective (Classical.choose_spec (show ∃ b : A, code b = code a from ⟨a, rfl⟩))

noncomputable def packet {A : Type} [Fintype A] (a : A) : List Bool := true :: code a

@[simp] theorem packet_length {A : Type} [Fintype A] (a : A) :
    (packet a).length = Fintype.card A + 1 := by simp [packet]

noncomputable def packets {A : Type} [Fintype A] (a : List A) : List Bool := a.flatMap packet

@[simp] theorem packets_nil {A : Type} [Fintype A] : packets ([] : List A) = [] := rfl

@[simp] theorem packets_cons {A : Type} [Fintype A] (a : A) (l : List A) :
    packets (a :: l) = packet a ++ packets l := rfl

@[simp] theorem packets_length {A : Type} [Fintype A] (l : List A) :
    (packets l).length = (Fintype.card A + 1) * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.mul_add, Nat.add_comm]

noncomputable def readHead {A : Type} [Fintype A] (key : List Bool) : Option A :=
  if key.head? = some true then decode key.tail else none

theorem read_head_packets {A : Type} [Fintype A] (l : List A) :
    readHead ((packets l).take (Fintype.card A + 1)) = l.head? := by
  cases l with
  | nil => simp [readHead]
  | cons a l =>
    rw [packets_cons, ← packet_length a, List.take_left]
    simp [readHead, packet]

theorem drop_packets {A : Type} [Fintype A] (l : List A) :
    (packets l).drop (Fintype.card A + 1) = packets l.tail := by
  cases l with
  | nil => simp
  | cons a l =>
    rw [packets_cons, ← packet_length a, List.drop_left]
    rfl

theorem take_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) (n : ℕ) :
    (fun z ↦ (f z).take n) ∈ FP := by
  have h := Cobham.takeFn (Cobham.const (List.replicate n false)) (FP_subset_CobhamFP hf)
  apply CobhamFP_subset_FP
  change Cobham (fun v : Fin 1 → List Bool ↦ (f (v 0)).take n)
  simpa only [List.length_replicate] using h

theorem drop_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) (n : ℕ) :
    (fun z ↦ (f z).drop n) ∈ FP := by
  have h := Cobham.dropFn (Cobham.const (List.replicate n false)) (FP_subset_CobhamFP hf)
  apply CobhamFP_subset_FP
  change Cobham (fun v : Fin 1 → List Bool ↦ (f (v 0)).drop n)
  simpa only [List.length_replicate] using h

theorem bounded_read_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP)
    (n : ℕ) (g : List Bool → List Bool) : (fun z ↦ g ((f z).take n)) ∈ FP :=
  mem_FP_of_bounded_key (take_mem_FP hf n) (fun _z ↦ List.length_take_le _ _) g

theorem finite_dispatch_mem_FP {A : Type} [Fintype A]
    (key : List Bool → A) (hkey : ∀ a, FPPred fun z ↦ key z = a)
    (F : A → List Bool → List Bool) (hF : ∀ a, F a ∈ FP) :
    (fun z ↦ F (key z) z) ∈ FP := by
  classical
  have hs : ∀ S : Finset A, (fun z ↦ if key z ∈ S then F (key z) z else []) ∈ FP := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using constFn_mem_FP []
    | @insert a S ha ih =>
      have h := (hkey a).ite_mem_FP (hF a) ih
      apply mem_FP_of_eq h
      intro z
      by_cases hz : key z = a <;> simp [hz]
  simpa using hs Finset.univ

theorem bounded_dispatch_mem_FP {A : Type} [Fintype A]
    {key : List Bool → List Bool} (hkey : key ∈ FP)
    {N : ℕ} (hlen : ∀ z, (key z).length ≤ N) (read : List Bool → A)
    (F : A → List Bool → List Bool) (hF : ∀ a, F a ∈ FP) :
    (fun z ↦ F (read (key z)) z) ∈ FP :=
  finite_dispatch_mem_FP _
    (fun a ↦ FPPred.of_bounded_key hkey hlen (fun k ↦ read k = a)) F hF

def entry : ℕ → List Bool → List Bool
  | 0, z => pairSnd z
  | n + 1, z => entry n (pairFst z)

theorem entry_mem_FP (n : ℕ) : entry n ∈ FP := by
  induction n with
  | zero => exact pairSnd_mem_FP
  | succ n ih => exact mem_FP_comp pairFst_mem_FP ih

theorem entry_encodeVec {n : ℕ} (v : Fin n → List Bool) (i : Fin n) :
    entry i.val (Cobham.encodeVec v) = v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [entry, Cobham.encodeVec]
    · simp only [Fin.val_succ, entry, Cobham.encodeVec_succ, pairFst_pair]
      convert ih (Fin.tail v) j using 1 <;> rfl

theorem encodeVec_mem_FP {n : ℕ} (f : Fin n → List Bool → List Bool)
    (hf : ∀ i, f i ∈ FP) : (fun z ↦ Cobham.encodeVec (fun i ↦ f i z)) ∈ FP := by
  induction n with
  | zero => exact constFn_mem_FP []
  | succ n ih =>
    exact mem_FP_pair (ih (fun i ↦ f i.succ) (fun i ↦ hf i.succ)) (hf 0)

end FiniteEncoding
end Lax323828Proofs.RegisteredBridge
