import Lax253009.FiniteProbability
import Mathlib.Data.Fintype.Prod

/-!
---
title: Repeated squaring of fortified projection tests
type: theorem
---
A projection test compares two locally valid answers after mapping them
to a common alphabet B. Suppose its value is at most s, and every
rectangular restriction has unnormalized winning probability at most
v times the rectangle's probability plus eta. Two parallel copies then
have value at most v*s + |B|*eta.

The error depends on the common projection alphabet, which remains fixed
when tuple questions enlarge the prover-answer alphabet. This is the
squaring step in the fortification approach to soundness amplification.
-/

namespace Lax253009.FortifiedSquaring

open FiniteProbability

structure Game (Z W A B : Type) where
  left : Z → W
  right : Z → W
  validLeft : Z → A → Bool
  validRight : Z → A → Bool
  projectLeft : Z → A → B
  projectRight : Z → A → B

namespace Game

variable {Z W A B : Type} (G : Game Z W A B)

def Test (z : Z) (a b : A) : Prop :=
  G.validLeft z a = true ∧ G.validRight z b = true ∧
    G.projectLeft z a = G.projectRight z b

def Wins (P Q : W → A) (z : Z) : Prop := G.Test z (P (G.left z)) (Q (G.right z))

def Sound [Fintype Z] (s : ℝ) : Prop :=
  ∀ P Q : W → A, probability (G.Wins P Q) ≤ s

def Fortified [Fintype Z] (v η : ℝ) : Prop :=
  ∀ (P Q : W → A) (S T : W → Prop),
    probability (fun z ↦ G.Wins P Q z ∧ S (G.left z) ∧ T (G.right z)) ≤
      v * probability (fun z ↦ S (G.left z) ∧ T (G.right z)) + η

def DoubleWins (P Q : W × W → A × A) (z : Z × Z) : Prop :=
  let a := P (G.left z.1, G.left z.2)
  let b := Q (G.right z.1, G.right z.2)
  G.Test z.1 a.1 b.1 ∧ G.Test z.2 a.2 b.2

end Game

axiom soundness {Z W A B : Type} [Fintype Z] [Nonempty Z] [Fintype B]
    (G : Game Z W A B) (s v η : ℝ) (hv : 0 ≤ v)
    (hs : G.Sound s) (hfort : G.Fortified v η)
    (P Q : W × W → A × A) :
    probability (G.DoubleWins P Q) ≤ v * s + (Fintype.card B : ℝ) * η

end Lax253009.FortifiedSquaring
