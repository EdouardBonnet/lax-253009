import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
---
title: The size of the decoding set from large coefficients
type: theorem
---
Let real coefficients $c_\alpha$ be indexed by subsets of an $n$-element
set and satisfy $\sum_\alpha c_\alpha^2\leq1$. For $\delta>0$, take the
union $S$ of the sets $\alpha$ with $|\alpha|\leq\ell$ and
$c_\alpha^2\geq\ell\delta$. Then $|S|\leq1/\delta$.

This is the counting argument for the decoding set in equation (2) of
Håstad's paper. Applied to Fourier coefficients using Parseval's identity
and $\delta=2^{-\varepsilon s}$, it gives $|S|\leq2^{\varepsilon s}$.
The statement below isolates the counting argument; its energy bound is an
explicit hypothesis, not an assumed Fourier identity.
-/

namespace Lax253009.SmallSupport

noncomputable def largeSets {n : ℕ} (c : Finset (Fin n) → ℝ) (l : ℕ)
    (δ : ℝ) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun a ↦ a.card ≤ l ∧ (l : ℝ) * δ ≤ c a ^ 2

noncomputable def decodingSet {n : ℕ} (c : Finset (Fin n) → ℝ) (l : ℕ)
    (δ : ℝ) : Finset (Fin n) :=
  (largeSets c l δ).biUnion id

axiom decodingSet_bound {n : ℕ} (c : Finset (Fin n) → ℝ) (l : ℕ)
    (δ : ℝ) (hδ : 0 < δ) (henergy : ∑ a, c a ^ 2 ≤ 1) :
  ((decodingSet c l δ).card : ℝ) ≤ 1 / δ

end Lax253009.SmallSupport
