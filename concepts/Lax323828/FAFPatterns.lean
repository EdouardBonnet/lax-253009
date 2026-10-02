import Lax323828.FAFTest
import Lax323828.LongCodePatterns

/-!
---
title: Free bits of the FAF test
type: theorem
---
The accepting transcripts of the FAF test use at most $q+ns$ free bits:
$q$ reference answers, followed by at most $s$ free bits in each of the
$n$ CNA tests. The side-condition queries are determined by the reference
answers. Setting $n=10\ell$ and $q=10\ell s$ gives Lemma 5.4's bound
of $20\ell s$ free bits.

We enumerate a finite superset of accepting transcripts. This allows
repeated sampled tables to be treated independently for the upper bound;
every transcript produced by an actual accepting oracle is included.
-/

namespace Lax323828.FAFPatterns

open scoped Classical

open LongCode LongCodePatterns

/-- The side condition on a larger-table word: validity and agreement with all reference answers. -/
noncomputable def conditionOfAnswers {Ω : Type} {u w q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (ω : Ω) (g : Fin q → Coordinate u) (b : Word q) : Coordinate w :=
  fun y ↦ valid ω y && decide (∀ j, g j (ρ ω y) = b j)

/-- All reference answer strings paired with one permissible partial pattern for each sampled larger table. -/
noncomputable def patterns {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u) (f : Fin n → Fin s → Coordinate w) :
    Finset (Word q × (Fin n → Pattern w)) :=
  Finset.univ.biUnion (fun b : Word q ↦
    (Fintype.piFinset (fun i ↦ sidePatterns (f i) (conditionOfAnswers ρ valid (ω i) g b))).image
      (fun a ↦ (b, a)))

/-- The reference answers and queried larger-table answers supplied by the given tables. -/
noncomputable def transcript {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w) (R : Table u) (A : Ω → Table w)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u) (f : Fin n → Fin s → Coordinate w) :
    Word q × (Fin n → Pattern w) :=
  (fun j ↦ R (g j), fun i ↦ restrict (SideQueried (f i) (FAFTest.condition ρ valid R (ω i) g)) (A (ω i)))

axiom transcript_mem {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w) (R : Table u) (A : Ω → Table w)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u) (f : Fin n → Fin s → Coordinate w)
    (h : FAFTest.Accepts ρ valid R A ω g f) :
    transcript ρ valid R A ω g f ∈ patterns ρ valid ω g f

axiom free_bits {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u) (f : Fin n → Fin s → Coordinate w) :
    (patterns ρ valid ω g f).card ≤ 2 ^ (q + n * s)

end Lax323828.FAFPatterns
