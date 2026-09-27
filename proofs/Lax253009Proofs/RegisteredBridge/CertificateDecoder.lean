import Lax253009Proofs.RegisteredBridge.RegisteredNP
import Lax253009Proofs.RegisteredBridge.MultitapeBridge

set_option backward.isDefEq.respectTransparency false

namespace Lax253009Proofs.RegisteredBridge.CertificateDecoder

open PCPFoundation.Complexity FiniteEncoding

def step (z : List Bool) : List Bool :=
  if (pairSnd z).head? = some false then
    pair (pairFst z ++ [((pairSnd z).drop 1).head?.getD false]) ((pairSnd z).drop 2)
  else z

theorem step_mem_FP : step ∈ FP := by
  have hid : (id : List Bool → List Bool) ∈ FP :=
    CobhamFP_subset_FP (Cobham.proj (0 : Fin 1))
  have hbit : (fun z ↦ [((pairSnd z).drop 1).head?.getD false]) ∈ FP := by
    have h := bounded_read_mem_FP (drop_mem_FP pairSnd_mem_FP 1) 1
      (fun l ↦ [l.head?.getD false])
    simpa only [List.head?_take, show (1 : ℕ) ≠ 0 by decide, if_false] using h
  have hyes := mem_FP_pair
    (Cobham.appendFn_mem_FP pairFst_mem_FP hbit) (drop_mem_FP pairSnd_mem_FP 2)
  have hp : FPPred (fun z ↦ (pairSnd z).head? = some false) := by
    have h := FPPred.of_bounded_key (take_mem_FP pairSnd_mem_FP 1)
      (fun z ↦ List.length_take_le 1 (pairSnd z)) (fun k ↦ k.head? = some false)
    simpa only [List.head?_take, show (1 : ℕ) ≠ 0 by decide, if_false] using h
  exact hp.ite_mem_FP hyes hid

def advance (s : List Bool × List Bool) : List Bool × List Bool :=
  if s.2.head? = some false then (s.1 ++ [((s.2).drop 1).head?.getD false], s.2.drop 2) else s

theorem step_pair (p r : List Bool) : step (pair p r) = pair (advance (p, r)).1 (advance (p, r)).2 := by
  simp only [step, pairFst_pair, pairSnd_pair, advance]
  split <;> rfl

theorem step_size (p r : List Bool) : (step (pair p r)).length ≤ (pair p r).length + 2 := by
  simp only [step, pairFst_pair, pairSnd_pair]
  split
  · simp only [pair_length, List.length_append, List.length_singleton, List.length_drop]
    omega
  · omega

def parseState (z : List Bool) : List Bool := step^[z.length] (pair [] z)

theorem parse_state_mem_FP : parseState ∈ FP := by
  have hid : (id : List Bool → List Bool) ∈ FP :=
    CobhamFP_subset_FP (Cobham.proj (0 : Fin 1))
  have hsemi : Function.Semiconj (fun s : List Bool × List Bool ↦ pair s.1 s.2) advance step :=
    fun s ↦ (step_pair s.1 s.2).symm
  apply iterate_mem_FP_of_step_le step_mem_FP (mem_FP_pair (constFn_mem_FP []) hid) hid 2
  intro z m hm
  change (step^[m + 1] (pair [] z)).length ≤ (step^[m] (pair [] z)).length + 2
  erw [Function.iterate_succ_apply', ← hsemi.iterate_right m ([], z)]
  exact step_size _ _

theorem step_registered_cons (p x y : List Bool) (b : Bool) :
    step (pair p (Lax434930.Certificates.pair (b :: x) y)) =
      pair (p ++ [b]) (Lax434930.Certificates.pair x y) := by
  simp [step, Lax434930.Certificates.pair]

theorem step_registered_nil (p y : List Bool) :
    step (pair p (Lax434930.Certificates.pair [] y)) =
      pair p (Lax434930.Certificates.pair [] y) := by
  simp [step, Lax434930.Certificates.pair]

theorem parse_registered_prefix (p x y : List Bool) :
    step^[x.length] (pair p (Lax434930.Certificates.pair x y)) =
      pair (p ++ x) (true :: y) := by
  induction x generalizing p with
  | nil => simp [Lax434930.Certificates.pair]
  | cons b x ih =>
    rw [List.length_cons, Function.iterate_succ_apply, step_registered_cons, ih]
    simp [List.append_assoc]

theorem iterate_terminal (p y : List Bool) (m : ℕ) :
    step^[m] (pair p (true :: y)) = pair p (true :: y) := by
  apply Function.IsFixedPt.iterate
  exact step_registered_nil p y

theorem parse_registered_pair (x y : List Bool) :
    parseState (Lax434930.Certificates.pair x y) = pair x (true :: y) := by
  have hlen0 : ∀ x : List Bool,
      (Lax434930.Certificates.pair x y).length = 2 * x.length + y.length + 1 := by
    intro x
    induction x with
    | nil => simp [Lax434930.Certificates.pair]
    | cons b x ih => simp [Lax434930.Certificates.pair, ih]; omega
  have hlen : (Lax434930.Certificates.pair x y).length =
      x.length + (x.length + y.length + 1) := by rw [hlen0]; omega
  rw [parseState, hlen, Nat.add_comm x.length, Function.iterate_add_apply,
    parse_registered_prefix, List.nil_append, iterate_terminal]

def first (z : List Bool) : List Bool := pairFst (parseState z)
def second (z : List Bool) : List Bool := (pairSnd (parseState z)).drop 1

theorem first_mem_FP : first ∈ FP := mem_FP_comp parse_state_mem_FP pairFst_mem_FP
theorem second_mem_FP : second ∈ FP :=
  drop_mem_FP (mem_FP_comp parse_state_mem_FP pairSnd_mem_FP) 1

@[simp] theorem first_pair (x y : List Bool) : first (Lax434930.Certificates.pair x y) = x := by
  simp [first, parse_registered_pair]

@[simp] theorem second_pair (x y : List Bool) : second (Lax434930.Certificates.pair x y) = y := by
  simp [second, parse_registered_pair]

end Lax253009Proofs.RegisteredBridge.CertificateDecoder
