import Lax253009.DecodedStrategies
import Mathlib.Data.Fintype.Prod

/-!
---
title: Projection games from regular constraint systems
type: theorem
---
A regular constraint system gives a two-prover projection game. The first
prover labels both ends of a dart; the second labels one uniformly chosen
endpoint. Reversing darts preserves the uniform distribution, so the verifier
can equivalently start with a uniformly chosen vertex and extension.

Perfect completeness is preserved. If every vertex assignment violates at
least a fraction $\gamma$ of the constraints, every pair of prover strategies
wins with probability at most $1-\gamma/2$. The bound also allows provers to
return no answer.
-/

namespace Lax253009.ProjectionGames

open FiniteProbability

structure System (V D A : Type) where
  reverse : V × D → V × D
  reverse_involutive : Function.Involutive reverse
  relation : V × D → A → A → Bool

namespace System

variable {V D A : Type} (C : System V D A)

def question (v : V) (ω : D × Bool) : V × D :=
  if ω.2 then C.reverse (v, ω.1) else (v, ω.1)

def endpoint (z : V × D) (b : Bool) : V :=
  if b then (C.reverse z).1 else z.1

def project (b : Bool) (p : A × A) : A := if b then p.2 else p.1

def Test (v : V) (ω : D × Bool) (p : A × A) (a : A) : Prop :=
  C.relation (C.question v ω) p.1 p.2 = true ∧ project ω.2 p = a

def Violated (a : V → A) (z : V × D) : Prop :=
  C.relation z (a z.1) (a (C.reverse z).1) ≠ true

def Satisfiable : Prop := ∃ a : V → A, ∀ z, ¬ C.Violated a z

def Sound [Fintype V] [Fintype D] (γ : ℝ) : Prop :=
  ∀ a : V → A, γ ≤ probability (C.Violated a)

end System

axiom completeness {V D A : Type} (C : System V D A) (h : C.Satisfiable) :
  ∃ P : V × D → A × A, ∃ Q : V → A,
    ∀ v ω, C.Test v ω (P (C.question v ω)) (Q v)

axiom soundness {V D A : Type} [Fintype V] [Nonempty V]
    [Fintype D] [Nonempty D] [Nonempty A]
    (C : System V D A) (γ : ℝ) (h : C.Sound γ)
    (P : V × D → Option (A × A)) (Q : V → Option A) :
    probability (DecodedStrategies.Wins C.question C.Test P Q) ≤ 1 - γ / 2

end Lax253009.ProjectionGames
