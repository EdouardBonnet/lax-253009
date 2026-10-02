import Lax323828.TestSampling
import Mathlib.Algebra.BigOperators.Fin

/-!
---
title: Repetition of local proof tests
type: theorem
---
Repeat a verifier $k$ times against the same global proof and accept only
when every run accepts. Accepting local views are unions of compatible
base views. The acceptance probability of each fixed proof is raised to
the $k$th power, and $A$ base accepting views give at most $A^k$ repeated
views per random choice. Perfect completeness is preserved.

This is repetition of a one-oracle PCP verifier. It is distinct from the
two-prover parallel-repetition theorem, whose strategies may depend on
entire question tuples.
-/

namespace Lax323828.TestRepetition

open scoped Classical

open LocalTests TestSampling FiniteProbability

/-- Every pair of local views gives the same answer wherever both are defined. -/
def Coherent {m k : ℕ} (a : Fin k → View m) : Prop :=
  ∀ i j, Compatible (a i) (a j)

/-- Combine the views into one partial assignment, using the first available answer at each coordinate. -/
def merge {m : ℕ} : {k : ℕ} → (Fin k → View m) → View m
  | 0, _ => fun _ ↦ none
  | k + 1, a => fun i ↦ (a 0 i).or (merge (fun j : Fin k ↦ a j.succ) i)

/-- Number the `r^k` sequences of `k` random choices using their base-`r` digits. -/
def seedEquiv (r k : ℕ) : (Fin k → Fin r) ≃ Fin (r ^ k) :=
  finFunctionFinEquiv

/-- Keep every coherent combination of accepting views from the `k` runs, and merge each combination. -/
noncomputable def repeated {r m : ℕ} (C : System r m) (k : ℕ) : System (r ^ k) m :=
  ⟨fun z ↦ ((Fintype.piFinset (fun i : Fin k ↦ C.accepting ((seedEquiv r k).symm z i))).filter
    Coherent).image merge⟩

axiom passes_iff {r m : ℕ} (C : System r m) (k : ℕ) (π : Oracle m) (z : Fin (r ^ k)) :
  Passes (repeated C k) π z ↔ ∀ i, Passes C π ((seedEquiv r k).symm z i)

axiom acceptance_probability {r m : ℕ} (C : System r m) (k : ℕ) (π : Oracle m) :
  probability (Passes (repeated C k) π) = probability (Passes C π) ^ k

axiom free_bits {r m : ℕ} (C : System r m) (k A : ℕ)
    (hA : ∀ z, (C.accepting z).card ≤ A) :
  ∀ z, ((repeated C k).accepting z).card ≤ A ^ k

axiom perfect_completeness {r m : ℕ} (C : System r m) (k : ℕ) (hC : Complete C) :
  Complete (repeated C k)

axiom soundness {r m : ℕ} (C : System r m) (k : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hC : Sound C p) : Sound (repeated C k) (p ^ k)

end Lax323828.TestRepetition
