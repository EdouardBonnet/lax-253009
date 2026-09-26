import Lax253009.FAFStrategyExtraction

/-!
---
title: Encoding finite projection-game answers as binary words
type: theorem
---
Inject finite answer alphabets into fixed-length Boolean words, reject
invalid first-prover encodings, and project valid answers through the
encoding of the second alphabet. This preserves perfect completeness and
cannot increase soundness, including for partial prover strategies.
The first answer width can be enlarged arbitrarily without changing either
property, as required by the FAF composition's minimum-width condition.
-/

namespace Lax253009.ProjectionEncoding

open LongCode FiniteProbability

noncomputable def decode {A B : Type} (e : A ↪ B) (b : B) : Option A := by
  classical
  exact if h : ∃ a, e a = b then some h.choose else none

noncomputable def valid {U Ω Y : Type} {w : ℕ}
    (ey : Y ↪ Word w) (v : U → Ω → Y → Bool) (u : U) (ω : Ω) (b : Word w) : Bool :=
  match decode ey b with
  | some y => v u ω y
  | none => false

noncomputable def project {U Ω X Y : Type} {u w : ℕ}
    (ex : X ↪ Word u) (ey : Y ↪ Word w) (ρ : U → Ω → Y → X)
    (v : U) (ω : Ω) (b : Word w) : Word u :=
  match decode ey b with
  | some y => ex (ρ v ω y)
  | none => fun _ ↦ false

axiom encoding_exists {A : Type} [Fintype A] (w : ℕ) (h : Fintype.card A ≤ w) :
    Nonempty (A ↪ Word w)

axiom completeness {U Ω W X Y : Type} {u w : ℕ}
    (ex : X ↪ Word u) (ey : Y ↪ Word w) (question : U → Ω → W)
    (v : U → Ω → Y → Bool) (ρ : U → Ω → Y → X)
    (P : W → Y) (Q : U → X)
    (hv : ∀ a ω, v a ω (P (question a ω)) = true)
    (hρ : ∀ a ω, ρ a ω (P (question a ω)) = Q a) :
    (∀ a ω, valid ey v a ω (ey (P (question a ω))) = true) ∧
    (∀ a ω, project ex ey ρ a ω (ey (P (question a ω))) = ex (Q a))

axiom soundness {U Ω W X Y : Type} [Fintype U] [Fintype Ω]
    [Nonempty X] [Nonempty Y] {u w : ℕ}
    (ex : X ↪ Word u) (ey : Y ↪ Word w) (question : U → Ω → W)
    (v : U → Ω → Y → Bool) (ρ : U → Ω → Y → X) (s : ℝ)
    (h : ∀ (P : W → Y) (Q : U → X),
      probability (fun z : U × Ω ↦ v z.1 z.2 (P (question z.1 z.2)) = true ∧
        ρ z.1 z.2 (P (question z.1 z.2)) = Q z.1) ≤ s)
    (P : W → Option (Word w)) (Q : U → Option (Word u)) :
    probability (DecodedStrategies.Wins question
      (FAFStrategyExtraction.Relation (project ex ey ρ) (valid ey v)) P Q) ≤ s

end Lax253009.ProjectionEncoding
