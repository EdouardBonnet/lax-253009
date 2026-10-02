/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Lax323828Proofs.PCPFoundation.Classes.P
import Lax323828Proofs.PCPFoundation.Classes.P.Bridge

/-!
# Division with remainder, in unary

Every index decomposition in an algorithmic constraint graph is a division:
which edge of the original graph, which step of the walk, which copy of the
gadget. This module names the unary quotients and remainders those
constructions read. Each is defined as what it computes, the quotient or
remainder of one length by another written as that many `true`s, and is
polynomial-time by `UnaryFn.div` and `UnaryFn.mod` of
`Lax323828Proofs.PCPFoundation.Classes.P.Unary`. As for `Nat`, dividing by an empty divisor
gives `0` and leaves the whole length as the remainder.

## Main definitions

- `Lax323828Proofs.PCPFoundation.Complexity.divFn`, `Lax323828Proofs.PCPFoundation.Complexity.modFn` — a length divided by the length of a
  fixed divisor
- `Lax323828Proofs.PCPFoundation.Complexity.divFn2`, `Lax323828Proofs.PCPFoundation.Complexity.modFn2` — one length divided by another, both
  read off a pair
- `Lax323828Proofs.PCPFoundation.Complexity.halfFn` — half a length

## Main results

- `Lax323828Proofs.PCPFoundation.Complexity.divFn_mem_FP`, `Lax323828Proofs.PCPFoundation.Complexity.modFn_mem_FP`,
  `Lax323828Proofs.PCPFoundation.Complexity.divFn2_mem_FP`, `Lax323828Proofs.PCPFoundation.Complexity.modFn2_mem_FP`,
  `Lax323828Proofs.PCPFoundation.Complexity.halfFn_mem_FP` — all are polynomial-time
- `Lax323828Proofs.PCPFoundation.Complexity.divFn_eq`, `Lax323828Proofs.PCPFoundation.Complexity.modFn_eq`, `Lax323828Proofs.PCPFoundation.Complexity.divFn2_eq`,
  `Lax323828Proofs.PCPFoundation.Complexity.modFn2_eq`, `Lax323828Proofs.PCPFoundation.Complexity.halfFn_eq` — what they compute
-/

set_option autoImplicit true

namespace Lax323828Proofs.PCPFoundation.Complexity

/-! ### Dividing by a fixed divisor -/

/-- The quotient of a length by the length of a fixed divisor, in unary. -/
def divFn (b s : List Bool) : List Bool := List.replicate (s.length / b.length) true

/-- The remainder of a length by the length of a fixed divisor, in unary. -/
def modFn (b s : List Bool) : List Bool := List.replicate (s.length % b.length) true

theorem divFn_eq {b : List Bool} (s : List Bool) :
    divFn b s = List.replicate (s.length / b.length) true := rfl

theorem modFn_eq {b : List Bool} (s : List Bool) :
    modFn b s = List.replicate (s.length % b.length) true := rfl

theorem divFn_mem_FP (b : List Bool) : divFn b ∈ FP :=
  ((UnaryFn.length id_mem_FP).div (UnaryFn.const b.length)).mem_FP

theorem modFn_mem_FP (b : List Bool) : modFn b ∈ FP :=
  ((UnaryFn.length id_mem_FP).mod (UnaryFn.const b.length)).mem_FP

/-! ### Dividing by a length read from the input -/

/-- The quotient of one length by another, in unary, on `pair b s`. -/
def divFn2 (z : List Bool) : List Bool :=
  List.replicate ((pairSnd z).length / (pairFst z).length) true

/-- The remainder of one length by another, in unary, on `pair b s`. -/
def modFn2 (z : List Bool) : List Bool :=
  List.replicate ((pairSnd z).length % (pairFst z).length) true

theorem divFn2_eq {b : List Bool} (s : List Bool) :
    divFn2 (pair b s) = List.replicate (s.length / b.length) true := by
  rw [divFn2, pairFst_pair, pairSnd_pair]

theorem modFn2_eq {b : List Bool} (s : List Bool) :
    modFn2 (pair b s) = List.replicate (s.length % b.length) true := by
  rw [modFn2, pairFst_pair, pairSnd_pair]

theorem divFn2_mem_FP : divFn2 ∈ FP :=
  ((UnaryFn.length Cobham.sndBlock_mem_FP).div (UnaryFn.length Cobham.fstBlock_mem_FP)).mem_FP

theorem modFn2_mem_FP : modFn2 ∈ FP :=
  ((UnaryFn.length Cobham.sndBlock_mem_FP).mod (UnaryFn.length Cobham.fstBlock_mem_FP)).mem_FP

/-! ### Halving -/

/-- **Halving a length**, in unary. -/
def halfFn (s : List Bool) : List Bool := List.replicate (s.length / 2) true

theorem halfFn_mem_FP : halfFn ∈ FP :=
  ((UnaryFn.length id_mem_FP).div (UnaryFn.const 2)).mem_FP

theorem halfFn_eq (s : List Bool) : halfFn s = List.replicate (s.length / 2) true := rfl

end Lax323828Proofs.PCPFoundation.Complexity
