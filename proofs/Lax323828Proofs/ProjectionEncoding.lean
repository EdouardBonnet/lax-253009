import Lax323828.ProjectionEncoding
import Lax323828Proofs.FiniteProbability

namespace Lax323828Proofs

open Lax323828 Lax323828.ProjectionEncoding Lax323828.LongCode
open Lax323828.FiniteProbability

@[simp] theorem projection_decode_encode {A B : Type} (e : A ↪ B) (a : A) :
    decode e (e a) = some a := by
  classical
  unfold decode
  rw [dif_pos ⟨a, rfl⟩]
  congr 1
  exact e.injective (Exists.choose_spec (show ∃ a', e a' = e a from ⟨a, rfl⟩))

/--
---
conclusion: Lax323828.ProjectionEncoding.encoding_exists
---
There are at least w Boolean words of length w; apply finite cardinality.
-/
theorem projection_encoding_exists {A : Type} [Fintype A]
    (w : ℕ) (h : Fintype.card A ≤ w) : Nonempty (A ↪ Word w) := by
  apply Function.Embedding.nonempty_of_card_le
  simpa [Word, Fintype.card_fun] using h.trans (Nat.lt_two_pow_self (n := w)).le

/--
---
conclusion: Lax323828.ProjectionEncoding.completeness
---
An encoded honest answer decodes to the original answer.
-/
theorem projection_encoding_complete {U Ω W X Y : Type} {u w : ℕ}
    (ex : X ↪ Word u) (ey : Y ↪ Word w) (question : U → Ω → W)
    (v : U → Ω → Y → Bool) (ρ : U → Ω → Y → X)
    (P : W → Y) (Q : U → X)
    (hv : ∀ a ω, v a ω (P (question a ω)) = true)
    (hρ : ∀ a ω, ρ a ω (P (question a ω)) = Q a) :
    (∀ a ω, valid ey v a ω (ey (P (question a ω))) = true) ∧
    (∀ a ω, project ex ey ρ a ω (ey (P (question a ω))) = ex (Q a)) := by
  constructor <;> intro a ω
  · simpa [valid] using hv a ω
  · simp [project, hρ]

/--
---
conclusion: Lax323828.ProjectionEncoding.soundness
---
A winning encoded transcript has two valid encodings. Decoding and filling
missing answers arbitrarily gives total original strategies that still win
on each such transcript.
-/
theorem projection_encoding_sound {U Ω W X Y : Type} [Fintype U] [Fintype Ω]
    [Nonempty X] [Nonempty Y] {u w : ℕ}
    (ex : X ↪ Word u) (ey : Y ↪ Word w) (question : U → Ω → W)
    (v : U → Ω → Y → Bool) (ρ : U → Ω → Y → X) (s : ℝ)
    (h : ∀ (P : W → Y) (Q : U → X),
      probability (fun z : U × Ω ↦ v z.1 z.2 (P (question z.1 z.2)) = true ∧
        ρ z.1 z.2 (P (question z.1 z.2)) = Q z.1) ≤ s)
    (P : W → Option (Word w)) (Q : U → Option (Word u)) :
    probability (DecodedStrategies.Wins question
      (FAFStrategyExtraction.Relation (project ex ey ρ) (valid ey v)) P Q) ≤ s := by
  classical
  let P' := fun a ↦ ((P a).bind (decode ey)).getD (Classical.arbitrary Y)
  let Q' := fun a ↦ ((Q a).bind (decode ex)).getD (Classical.arbitrary X)
  apply le_trans (Lax323828.FiniteProbability.monotone _ _ ?_) (h P' Q')
  rintro z ⟨by', bx, hP, hQ, hv, hρ⟩
  obtain ⟨y, hy⟩ : ∃ y, decode ey by' = some y := by
    cases hd : decode ey by' with
    | none => simp [valid, hd] at hv
    | some y => exact ⟨y, rfl⟩
  have hp : P' (question z.1 z.2) = y := by simp [P', hP, hy]
  have hρ' : ex (ρ z.1 z.2 y) = bx := by simpa [project, hy] using hρ
  have hq : Q' z.1 = ρ z.1 z.2 y := by simp [Q', hQ, ← hρ']
  rw [hp, hq]
  exact ⟨by simpa [valid, hy] using hv, rfl⟩

end Lax323828Proofs
