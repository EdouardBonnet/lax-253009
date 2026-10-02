/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Lax323828Proofs.PCPFoundation.Classes.PCP.Internal.NatEncode
import Lax323828Proofs.PCPFoundation.Classes.P.Range
import Lax323828Proofs.PCPFoundation.Classes.P.Range.Internal

/-!
# Writing out a list of encoded entries

The list encoder `listEncFn` and the loop behind it moved to
`Lax323828Proofs.PCPFoundation.Classes.P.Range`, where `listEncFn_mem_FP` needs no bound on the
loop's state, and to its internals `Lax323828Proofs.PCPFoundation.Classes.P.Range.Internal`,
which keep `listStep`, `entryCat`, `listStep_iterate`, `listEncFn_eq` and
`bitstringEncode_of_entries` under their old names. This module re-exports both,
together with `Lax323828Proofs.PCPFoundation.Classes.PCP.Internal.NatEncode`, so that its
importers see the same names as before.
-/
