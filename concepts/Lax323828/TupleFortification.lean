import Lax323828.FortifiedSquaring
import Mathlib.Data.Fintype.Pi

/-!
---
title: Fortification by uniformly sampled tuples
type: theorem
---
Replace each prover question by a uniform tuple with the original question
planted at a hidden uniformly chosen coordinate, and ask the prover to
answer every coordinate. This preserves perfect completeness, soundness,
and uniform question marginals. For tuple length t, the resulting game is
fortified with additive error at most 4r whenever 1/t ≤ r².

The construction uses all tuples. Its size is polynomial in the original
question count for each fixed t; its mixing bound is independent of the
prover-answer alphabet.
-/

namespace Lax323828.TupleFortification

open FortifiedSquaring
open scoped BigOperators

abbrev History (t : ℕ) (W : Type) := Fin t × (Fin t → W)

def plant {W : Type} {t : ℕ} (w : W) (h : History t W) : Fin t → W :=
  Function.update h.2 h.1 w

def lift {Z W A B : Type} (G : Game Z W A B) (t : ℕ) :
    Game (Z × (History t W × History t W)) (Fin t → W) (Fin t → A) B where
  left z := plant (G.left z.1) z.2.1
  right z := plant (G.right z.1) z.2.2
  validLeft z a := G.validLeft z.1 (a z.2.1.1)
  validRight z b := G.validRight z.1 (b z.2.2.1)
  projectLeft z a := G.projectLeft z.1 (a z.2.1.1)
  projectRight z b := G.projectRight z.1 (b z.2.2.1)

axiom soundness {Z W A B : Type} [Fintype Z] [Fintype W] [DecidableEq W]
    [Nonempty W] [Fintype A] (G : Game Z W A B) (t : ℕ) (ht : 0 < t)
    (s : ℝ) (hG : G.Sound s) : (lift G t).Sound s

axiom fortification {Z W A B : Type}
    [Fintype Z] [Nonempty Z] [Fintype W] [DecidableEq W] [Nonempty W]
    [Fintype A] [Nonempty A]
    (G : Game Z W A B)
    (hl : ∀ f : W → ℝ, (𝔼 z, f (G.left z)) = (𝔼 w, f w))
    (hr : ∀ f : W → ℝ, (𝔼 z, f (G.right z)) = (𝔼 w, f w))
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hG : G.Sound s)
    (t : ℕ) (ht : 0 < t) (r : ℝ) (hr0 : 0 ≤ r) (htr : 1 / (t : ℝ) ≤ r ^ 2) :
    (lift G t).Fortified s (4 * r)

axiom left_uniform {Z W A B : Type} [Fintype Z] [Fintype W] [Nonempty W]
    (G : Game Z W A B)
    (hl : ∀ f : W → ℝ, (𝔼 z, f (G.left z)) = (𝔼 w, f w))
    (t : ℕ) (ht : 0 < t) (f : (Fin t → W) → ℝ) :
    (𝔼 z, f ((lift G t).left z)) = 𝔼 w, f w

axiom right_uniform {Z W A B : Type} [Fintype Z] [Fintype W] [Nonempty W]
    (G : Game Z W A B)
    (hr : ∀ f : W → ℝ, (𝔼 z, f (G.right z)) = (𝔼 w, f w))
    (t : ℕ) (ht : 0 < t) (f : (Fin t → W) → ℝ) :
    (𝔼 z, f ((lift G t).right z)) = 𝔼 w, f w

axiom completeness {Z W A B : Type} (G : Game Z W A B)
    (P Q : W → A) (h : ∀ z, G.Wins P Q z) (t : ℕ) :
    ∀ z, (lift G t).Wins (fun w i ↦ P (w i)) (fun w i ↦ Q (w i)) z

end Lax323828.TupleFortification
