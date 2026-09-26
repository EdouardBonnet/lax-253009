import Lax253009.LongCode

/-!
---
title: Normalizing a long-code table to an odd table
type: theorem
---
The Fourier analysis assumes $A(-g)=-A(g)$. This loses no accepting
transcripts: repair every inconsistent pair of complementary coordinates
by using evaluation at a fixed word. An accepting CNA transcript only
queries consistent pairs, so all its answers are preserved. Acceptance
and its side-condition extension are preserved as well.

This justifies the normalization in footnote (4) preceding equation (2),
including the strengthened test used for Theorem 4.17. Boolean negation
represents sign negation.
-/

namespace Lax253009.OddNormalization

open LongCode

def negate {w : ℕ} (g : Coordinate w) : Coordinate w := fun x ↦ !(g x)

def oddify {w : ℕ} (x₀ : Word w) (A : Table w) : Table w :=
  fun g ↦ if A (negate g) = !(A g) then A g else g x₀

axiom odd {w : ℕ} (x₀ : Word w) (A : Table w) (g : Coordinate w) :
  oddify x₀ A (negate g) = !(oddify x₀ A g)

axiom same_queries {w s : ℕ} (x₀ : Word w) (A : Table w)
    (f : Fin s → Coordinate w) (hA : Accepts A f)
    (g : Coordinate w) (hg : Queried f g) : oddify x₀ A g = A g

axiom preserves_acceptance {w s : ℕ} (x₀ : Word w) (A : Table w)
    (f : Fin s → Coordinate w) (hA : Accepts A f) :
  Accepts (oddify x₀ A) f

axiom preserves_side_acceptance {w s : ℕ} (x₀ : Word w) (A : Table w)
    (f : Fin s → Coordinate w) (h : Coordinate w) (hA : AcceptsWithCondition A f h) :
  AcceptsWithCondition (oddify x₀ A) f h

end Lax253009.OddNormalization
