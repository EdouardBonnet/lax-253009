import Mathlib.Data.Fintype.Pi

/-!
---
title: Long codes and the complete nonadaptive test
type: definition
---
The long code of a Boolean word $x\in\{0,1\}^w$ is its evaluation table:
at the coordinate indexed by a Boolean function $g$, it stores $g(x)$.
A purported long code is an arbitrary table of the same shape.

The complete nonadaptive test chooses $s$ Boolean functions $f_i$. After
reading their table entries $a_i=A(f_i)$, it checks
$A(B\circ f)=B(a)$ for every Boolean predicate $B$ of $s$ bits.
Only the initial $s$ answers are free: they determine every checked answer.
These are the long code of Section 3 and the CNA test of Section 4 of
Håstad's paper, written with Boolean values instead of signs.

With a side condition $h$, the test additionally checks that each queried
answer is unchanged when its function is replaced by any function agreeing
with it on the set where $h$ is true. This is step (3) of the test preceding
Theorem 4.17. The definitions below describe a fixed choice of the functions;
the probabilistic soundness estimates are separate statements.
-/

namespace Lax323828.LongCode

abbrev Word (w : ℕ) := Fin w → Bool
abbrev Coordinate (w : ℕ) := Word w → Bool
abbrev Table (w : ℕ) := Coordinate w → Bool

def evaluation {w : ℕ} (x : Word w) : Table w := fun g ↦ g x

def compose {w s : ℕ} (f : Fin s → Coordinate w) (B : Word s → Bool) : Coordinate w :=
  fun x ↦ B (fun i ↦ f i x)

def Accepts {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w) : Prop :=
  ∀ B : Word s → Bool, A (compose f B) = B (fun i ↦ A (f i))

def LooksLike {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w) (x : Word w) : Prop :=
  (∀ i, A (f i) = f i x) ∧
  (∀ B : Word s → Bool, A (compose f B) = compose f B x)

def AgreesOn {w : ℕ} (h g g' : Coordinate w) : Prop :=
  ∀ x, h x = true → g x = g' x

def Queried {w s : ℕ} (f : Fin s → Coordinate w) (g : Coordinate w) : Prop :=
  (∃ i, g = f i) ∨ ∃ B : Word s → Bool, g = compose f B

def AcceptsWithCondition {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w)
    (h : Coordinate w) : Prop :=
  Accepts A f ∧ ∀ g, Queried f g → ∀ g', AgreesOn h g g' → A g = A g'

end Lax323828.LongCode
