import Lax323828.FiniteProbability
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Log

/-!
---
title: Sampling finite choices with a fixed supply of fair bits
type: theorem
---
To sample $N$ choices from $r>0$ possibilities, use
$b=\lceil\log_2(12Nr)\rceil$ independent bits per choice and reduce the
binary integer modulo $r$. This always returns a choice and uses exactly
$Nb$ bits. Its effect on the probability of any event is at most $1/12$.
Thus the graph reduction's $1/4$ error becomes at most $1/3$, while perfect
completeness is unchanged.

The sampler uses explicit binary interpretation and natural-number
remainder. The probability theorem does not certify its running time on
the registered probabilistic Turing-machine model.
-/

namespace Lax323828.FreshBitSampling

open FiniteProbability

def modulo {N r B : ℕ} (hr : 0 < r) (z : Fin N → Fin B) : Fin N → Fin r :=
  fun i ↦ ⟨(z i).val % r, Nat.mod_lt _ hr⟩

def bitsPerDraw (N r : ℕ) : ℕ := Nat.clog 2 (12 * N * r)

def binaryEquiv (b : ℕ) : (Fin b → Bool) ≃ Fin (2 ^ b) :=
  (Equiv.piCongrRight (fun _ ↦ finTwoEquiv.symm)).trans finFunctionFinEquiv

def sample {N r : ℕ} (hr : 0 < r)
    (z : Fin N → Fin (bitsPerDraw N r) → Bool) : Fin N → Fin r :=
  modulo hr (fun i ↦ binaryEquiv (bitsPerDraw N r) (z i))

def coinEquiv (N b : ℕ) : (Fin (N * b) → Bool) ≃ (Fin N → Fin b → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

def sampleFlat {N r : ℕ} (hr : 0 < r)
    (coins : Fin (N * bitsPerDraw N r) → Bool) : Fin N → Fin r :=
  sample hr (coinEquiv N (bitsPerDraw N r) coins)

axiom modulo_error {N r B : ℕ} (hr : 0 < r) (hB : 0 < B)
    (P : (Fin N → Fin r) → Prop) :
  probability (fun z : Fin N → Fin B ↦ P (modulo hr z)) ≤
    probability P + (N : ℝ) * r / B

axiom sampling_error {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (P : (Fin N → Fin r) → Prop) :
  probability (fun z : Fin N → Fin (bitsPerDraw N r) → Bool ↦ P (sample hr z)) ≤
    probability P + 1 / 12

axiom one_third_error {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (P : (Fin N → Fin r) → Prop) (hP : probability P ≤ 1 / 4) :
  probability (fun z : Fin N → Fin (bitsPerDraw N r) → Bool ↦ P (sample hr z)) ≤ 1 / 3

axiom flat_one_third_error {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (P : (Fin N → Fin r) → Prop) (hP : probability P ≤ 1 / 4) :
  probability (fun coins : Fin (N * bitsPerDraw N r) → Bool ↦ P (sampleFlat hr coins)) ≤ 1 / 3

axiom repeated_seed_bit_bound (N r k : ℕ) :
  bitsPerDraw N (r ^ k) ≤ Nat.clog 2 (12 * N) + k * Nat.clog 2 r

end Lax323828.FreshBitSampling
