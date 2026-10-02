/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Lax323828Proofs.PCPFoundation.Classes.PCP.Internal.UnaryDivMod
import Lax323828Proofs.PCPFoundation.Classes.PCP.Internal.PositionsFP
import Lax323828Proofs.PCPFoundation.Classes.P.Range

/-!
# The largest of polynomially many values

An algorithm reading a formula has to know how many variables it mentions, which
is the largest index any literal names. More generally: given a rule that
computes a value for each index, take the largest over a bounded range.

The maximum moved to `Lax323828Proofs.PCPFoundation.Classes.P.Range`, which computes it as a
count and keeps its old names: `maxOver`, `le_maxOver`, `maxOver_le`,
`maxOver_attained`, `maxFn`, `maxFn_mem_FP` and `maxFn_eq`. This module
re-exports it, together with its former imports, so that its importers see the
same names as before.
-/
