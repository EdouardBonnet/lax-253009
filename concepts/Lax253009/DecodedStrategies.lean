import Lax253009.FiniteProbability
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option

/-!
---
title: Extracting prover strategies from decoded sets
type: theorem
---
A question $u$ for the second prover and a random extension $\omega$
determine the first prover's question. Each first question has a set of
at most $B$ decoded answers. Call a second question common when some
answer is compatible with one of the decoded answers with probability
at least $p$ over extensions.

There are deterministic prover strategies whose success probability is at
least $\Pr[\mathrm{common}]p/(B+1)$. The first strategy depends only on its
own question, even when several extensions produce the same question.
An explicit failure answer handles empty decoding sets. This is the
rounding step in Lemma 5.5, with a harmless extra unit in the denominator.
-/

namespace Lax253009.DecodedStrategies

open FiniteProbability

def Common {U Ω W X Y : Type} [Fintype Ω]
    (question : U → Ω → W) (V : U → Ω → Y → X → Prop)
    (D : W → Finset Y) (p : ℝ) (u : U) : Prop :=
  ∃ x, p ≤ probability (fun ω ↦ ∃ y ∈ D (question u ω), V u ω y x)

def Wins {U Ω W X Y : Type}
    (question : U → Ω → W) (V : U → Ω → Y → X → Prop)
    (P : W → Option Y) (Q : U → Option X) (z : U × Ω) : Prop :=
  ∃ y x, P (question z.1 z.2) = some y ∧ Q z.1 = some x ∧ V z.1 z.2 y x

axiom extract_strategies {U Ω W X Y : Type}
    [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
    [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y]
    (question : U → Ω → W) (V : U → Ω → Y → X → Prop)
    (D : W → Finset Y) (B : ℕ) (hB : ∀ w, (D w).card ≤ B)
    (p : ℝ) (hp : 0 ≤ p) :
    ∃ P : W → Option Y, ∃ Q : U → Option X,
      probability (Common question V D p) * p / (B + 1) ≤ probability (Wins question V P Q)

end Lax253009.DecodedStrategies
