import Lax253009.TupleFortification
import Lax253009.ProjectionGames

/-!
---
title: Soundness amplification for centered projection games
type: theorem
---
Two independently sampled extensions of a common center define a symmetric
projection test. Its value is at most the original game's value, while
original value at most the square root of symmetric value follows from
Cauchy–Schwarz. Fortification followed by tensor squaring preserves this
centered structure and has value at most s² + 4|X|r.

Regular constraint systems supply uniformly distributed questions in this
model. Both transformations preserve perfect completeness and uniform
question marginals.
-/

namespace Lax253009.CenteredProjection

open FiniteProbability FortifiedSquaring TupleFortification
open scoped BigOperators

structure System (U Ω W X Y : Type) where
  question : U → Ω → W
  valid : U → Ω → Y → Bool
  project : U → Ω → Y → X

namespace System

variable {U Ω W X Y : Type} (G : System U Ω W X Y)

def Test (u : U) (ω : Ω) (y : Y) (x : X) : Prop :=
  G.valid u ω y = true ∧ G.project u ω y = x

def Complete : Prop := ∃ P : W → Y, ∃ Q : U → X,
  ∀ u ω, G.Test u ω (P (G.question u ω)) (Q u)

def Sound [Fintype U] [Fintype Ω] (s : ℝ) : Prop :=
  ∀ (P : W → Y) (Q : U → X),
    probability (fun z : U × Ω ↦ G.Test z.1 z.2 (P (G.question z.1 z.2)) (Q z.1)) ≤ s

def Uniform [Fintype U] [Fintype Ω] [Fintype W] : Prop :=
  ∀ f : W → ℝ, (𝔼 u, 𝔼 ω, f (G.question u ω)) = 𝔼 w, f w

def symmetrize : Game (U × (Ω × Ω)) W Y X where
  left z := G.question z.1 z.2.1
  right z := G.question z.1 z.2.2
  validLeft z y := G.valid z.1 z.2.1 y
  validRight z y := G.valid z.1 z.2.2 y
  projectLeft z y := G.project z.1 z.2.1 y
  projectRight z y := G.project z.1 z.2.2 y

def fortify (t : ℕ) : System U (Ω × History t W) (Fin t → W) X (Fin t → Y) where
  question u ω := plant (G.question u ω.1) ω.2
  valid u ω y := G.valid u ω.1 (y ω.2.1)
  project u ω y := G.project u ω.1 (y ω.2.1)

def tensor : System (U × U) (Ω × Ω) (W × W) (X × X) (Y × Y) where
  question u ω := (G.question u.1 ω.1, G.question u.2 ω.2)
  valid u ω y := G.valid u.1 ω.1 y.1 && G.valid u.2 ω.2 y.2
  project u ω y := (G.project u.1 ω.1 y.1, G.project u.2 ω.2 y.2)

end System

def fromConstraints {V D A : Type} (C : ProjectionGames.System V D A) :
    System V (D × Bool) (V × D) A (A × A) where
  question := C.question
  valid v ω p := C.relation (C.question v ω) p.1 p.2
  project _ ω p := ProjectionGames.System.project ω.2 p

axiom symmetrize_sound {U Ω W X Y : Type}
    [Fintype U] [Fintype Ω] [Nonempty Ω]
    (G : System U Ω W X Y) (s : ℝ) (h : G.Sound s) : G.symmetrize.Sound s

axiom fortify_complete {U Ω W X Y : Type}
    (G : System U Ω W X Y) (h : G.Complete) (t : ℕ) : (G.fortify t).Complete

axiom tensor_complete {U Ω W X Y : Type}
    (G : System U Ω W X Y) (h : G.Complete) : G.tensor.Complete

axiom fortify_uniform {U Ω W X Y : Type}
    [Fintype U] [Fintype Ω] [Fintype W] [Nonempty W]
    (G : System U Ω W X Y) (h : G.Uniform) (t : ℕ) (ht : 0 < t) :
    (G.fortify t).Uniform

axiom tensor_uniform {U Ω W X Y : Type}
    [Fintype U] [Fintype Ω] [Fintype W]
    (G : System U Ω W X Y) (h : G.Uniform) : G.tensor.Uniform

axiom fortify_square_sound {U Ω W X Y : Type}
    [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
    [Fintype W] [Nonempty W] [DecidableEq W]
    [Fintype X] [Fintype Y] [Nonempty Y]
    (G : System U Ω W X Y) (hu : G.Uniform)
    (t : ℕ) (ht : 0 < t) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (h : G.symmetrize.Sound s) (r : ℝ) (hr : 0 ≤ r) (htr : 1 / (t : ℝ) ≤ r ^ 2) :
    (G.fortify t).tensor.symmetrize.Sound (s ^ 2 + (Fintype.card X : ℝ) * (4 * r))

axiom center_sound_of_sym {U Ω W X Y : Type}
    [Fintype U] [Nonempty U] [Fintype Ω]
    (G : System U Ω W X Y) (s : ℝ) (hs : 0 ≤ s)
    (h : G.symmetrize.Sound (s ^ 2)) : G.Sound s

axiom from_constraints_complete {V D A : Type}
    (C : ProjectionGames.System V D A) (h : C.Satisfiable) : (fromConstraints C).Complete

axiom from_constraints_sound {V D A : Type} [Fintype V] [Nonempty V]
    [Fintype D] [Nonempty D] [Nonempty A]
    (C : ProjectionGames.System V D A) (γ : ℝ) (h : C.Sound γ) :
    (fromConstraints C).Sound (1 - γ / 2)

axiom from_constraints_uniform {V D A : Type} [Fintype V] [Fintype D]
    (C : ProjectionGames.System V D A) : (fromConstraints C).Uniform

end Lax253009.CenteredProjection
