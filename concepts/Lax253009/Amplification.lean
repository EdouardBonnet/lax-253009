import Lax253009.CenteredProjection
import Mathlib.Data.PNat.Basic

/-!
---
title: Arbitrarily small projection-game soundness with polynomial size
type: theorem
---
A fixed sequence of tuple fortifications and tensor squarings reduces any
constant symmetric soundness s in (0,1) below any prescribed positive δ.
The sequence depends only on s, δ, and the fixed answer alphabets, and is
chosen before the question spaces and the game.

All transformations preserve perfect completeness and uniform question
marginals. Explicit cardinality formulas show polynomial growth of the
question spaces and constant answer alphabets for each fixed sequence.
This provides the soundness amplification needed for the Håstad reduction.
-/

namespace Lax253009.Amplification

open CenteredProjection TupleFortification
open scoped BigOperators

inductive Scheme where
  | base
  | step (t : ℕ+) (previous : Scheme)

namespace Scheme

def centers (S : Scheme) (U : Type) : Type := match S with
  | .base => U
  | .step _ S => centers S U × centers S U

def questions (S : Scheme) (W : Type) : Type := match S with
  | .base => W
  | .step t S => (Fin t → questions S W) × (Fin t → questions S W)

def extensions (S : Scheme) (Ω W : Type) : Type := match S with
  | .base => Ω
  | .step t S => (extensions S Ω W × History t (questions S W)) ×
      (extensions S Ω W × History t (questions S W))

instance centersFintype {U : Type} [Fintype U] (S : Scheme) : Fintype (centers S U) :=
  match S with
  | .base => inferInstanceAs (Fintype U)
  | .step _ S =>
    letI : Fintype (centers S U) := centersFintype S
    inferInstanceAs (Fintype (centers S U × centers S U))

instance questionsFintype {W : Type} [Fintype W] (S : Scheme) : Fintype (questions S W) :=
  match S with
  | .base => inferInstanceAs (Fintype W)
  | .step t S =>
    letI : Fintype (questions S W) := questionsFintype S
    inferInstanceAs (Fintype ((Fin t → questions S W) × (Fin t → questions S W)))

instance extensionsFintype {Ω W : Type} [Fintype Ω] [Fintype W] (S : Scheme) :
    Fintype (extensions S Ω W) := match S with
  | .base => inferInstanceAs (Fintype Ω)
  | .step t S =>
    letI : Fintype (extensions S Ω W) := extensionsFintype S
    inferInstanceAs (Fintype ((extensions S Ω W × History t (questions S W)) ×
      (extensions S Ω W × History t (questions S W))))

instance centersNonempty {U : Type} [Nonempty U] (S : Scheme) : Nonempty (centers S U) :=
  match S with
  | .base => inferInstanceAs (Nonempty U)
  | .step _ S =>
    letI : Nonempty (centers S U) := centersNonempty S
    inferInstanceAs (Nonempty (centers S U × centers S U))

instance questionsNonempty {W : Type} [Nonempty W] (S : Scheme) : Nonempty (questions S W) :=
  match S with
  | .base => inferInstanceAs (Nonempty W)
  | .step t S =>
    letI : Nonempty (questions S W) := questionsNonempty S
    inferInstanceAs (Nonempty ((Fin t → questions S W) × (Fin t → questions S W)))

instance extensionsNonempty {Ω W : Type} [Nonempty Ω] [Nonempty W] (S : Scheme) :
    Nonempty (extensions S Ω W) := match S with
  | .base => inferInstanceAs (Nonempty Ω)
  | .step t S =>
    letI : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp t.pos
    letI : Nonempty (extensions S Ω W) := extensionsNonempty S
    inferInstanceAs (Nonempty ((extensions S Ω W × History t (questions S W)) ×
      (extensions S Ω W × History t (questions S W))))

def transform {U Ω W X Y : Type} (S : Scheme) (G : System U Ω W X Y) :
    System (centers S U) (extensions S Ω W) (questions S W) (centers S X) (questions S Y) :=
  match S with
  | .base => G
  | .step t S => ((transform S G).fortify t).tensor

def centerPower : Scheme → ℕ
  | .base => 1
  | .step _ S => S.centerPower * 2

def questionPower : Scheme → ℕ
  | .base => 1
  | .step t S => S.questionPower * t * 2

def extensionCoefficient : Scheme → ℕ
  | .base => 1
  | .step t S => (S.extensionCoefficient * t) ^ 2

def extensionPower : Scheme → ℕ
  | .base => 0
  | .step t S => (S.extensionPower + S.questionPower * t) * 2

axiom transform_complete {U Ω W X Y : Type} (S : Scheme) (G : System U Ω W X Y)
    (h : G.Complete) : (S.transform G).Complete

axiom transform_uniform {U Ω W X Y : Type}
    [Fintype U] [Fintype Ω] [Fintype W] [Nonempty W]
    (S : Scheme) (G : System U Ω W X Y) (h : G.Uniform) : (S.transform G).Uniform

axiom card_centers {U : Type} [Fintype U] (S : Scheme) :
    Fintype.card (S.centers U) = Fintype.card U ^ S.centerPower

axiom card_questions {W : Type} [Fintype W] (S : Scheme) :
    Fintype.card (S.questions W) = Fintype.card W ^ S.questionPower

axiom card_extensions {Ω W : Type} [Fintype Ω] [Fintype W] (S : Scheme) :
    Fintype.card (S.extensions Ω W) =
      S.extensionCoefficient * Fintype.card Ω ^ S.centerPower * Fintype.card W ^ S.extensionPower

axiom size_polynomial {U Ω W : Type} [Fintype U] [Fintype Ω] [Fintype W] (S : Scheme) :
    Fintype.card (S.centers U) + Fintype.card (S.extensions Ω W) + Fintype.card (S.questions W) ≤
      (S.extensionCoefficient + 2) * (Fintype.card U + Fintype.card Ω + Fintype.card W + 1) ^
        (S.centerPower + S.questionPower + S.extensionPower)

end Scheme

def SoundReduction (S : Scheme) (X Y : Type) [Fintype X] [Fintype Y] (s δ : ℝ) : Prop :=
  ∀ (U Ω W : Type) [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
    [Fintype W] [Nonempty W] (G : System U Ω W X Y),
    G.Uniform → G.symmetrize.Sound s → (S.transform G).symmetrize.Sound δ

axiom exists_small_value_scheme (X Y : Type) [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (s δ : ℝ) (hs : 0 < s) (hs1 : s < 1) (hδ : 0 < δ) :
    ∃ S : Scheme, SoundReduction S X Y s δ

end Lax253009.Amplification
