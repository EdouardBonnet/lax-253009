import Lax253009.Graphs
import Lax759944.TuringPolytime
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Randomized promise-gap algorithms for Max Independent Set
type: definition
---
A randomized polynomial-time algorithm distinguishes graphs with independence
number at most $n^{1/q}$ from graphs with independence number at least
$n^{1-1/q}$, with error at most $1/3$ on either promise. The guarantee may
start at a fixed input-size cutoff.

The algorithm is a fixed finite Turing machine, certified polynomial-time
by lax-759944. Its input is a pair of natural-number words: the vertex count
followed by the row-major adjacency matrix, and exactly $c(n+1)^k$ independent
uniform bits. The pair is prefixed by the length of its first word. These
words use the canonical binary encoding of lax-759944. The constants and
the machine are fixed before the input graph is chosen.
-/

namespace Lax253009.IndependentSetGap

open Graphs Lax759944.TuringPolytime

/-- Vertex count followed by the complete row-major adjacency matrix. -/
def graphWord {n : ℕ} (G : Graph n) : List ℕ :=
  n :: List.ofFn fun rank : Fin (n * n) ↦
    let vertex := finProdFinEquiv.symm rank
    if G.adjacent vertex.1 vertex.2 then 1 else 0

/-- A uniform tape of exactly `r` independent bits. -/
abbrev Seed (r : ℕ) := Fin r → Bool

def seedWord {r : ℕ} (seed : Seed r) : List ℕ :=
  (List.ofFn seed).map fun bit ↦ if bit then 1 else 0

def pairWords (left right : List ℕ) : List ℕ :=
  left.length :: left ++ right

/-- One polynomial-time machine with a fixed polynomial random-tape bound. -/
structure Program where
  function : List ℕ → List ℕ
  polytime : TuringPolytime function
  randomnessConstant : ℕ
  randomnessExponent : ℕ
  randomnessConstant_pos : 0 < randomnessConstant

def Program.randomBitCount (program : Program) (n : ℕ) : ℕ :=
  program.randomnessConstant * (n + 1) ^ program.randomnessExponent

abbrev Program.Seed (program : Program) (n : ℕ) :=
  IndependentSetGap.Seed (program.randomBitCount n)

def Program.accepts (program : Program) (n : ℕ)
    (G : Graph n) (seed : program.Seed n) : Bool :=
  decide (program.function (pairWords (graphWord G) (seedWord seed)) = [1])

def Program.seeds (program : Program) (n : ℕ) : Finset (program.Seed n) :=
  Finset.univ

def Program.acceptingSeeds (program : Program) (n : ℕ) (G : Graph n) :
    Finset (program.Seed n) :=
  (program.seeds n).filter fun seed ↦ program.accepts n G seed

/-- A bounded-error polynomial-time solver for the rational Independent Set gap. -/
structure Solver (q : ℕ) where
  program : Program
  cutoff : ℕ
  completeness : ∀ n : ℕ, cutoff ≤ n → ∀ G : Graph n,
    Real.rpow n (1 - (q : ℝ)⁻¹) ≤ (G.simpleGraph.indepNum : ℝ) →
      2 * (program.seeds n).card ≤ 3 * (program.acceptingSeeds n G).card
  soundness : ∀ n : ℕ, cutoff ≤ n → ∀ G : Graph n,
    (G.simpleGraph.indepNum : ℝ) ≤ Real.rpow n ((q : ℝ)⁻¹) →
      3 * (program.acceptingSeeds n G).card ≤ (program.seeds n).card

end Lax253009.IndependentSetGap
