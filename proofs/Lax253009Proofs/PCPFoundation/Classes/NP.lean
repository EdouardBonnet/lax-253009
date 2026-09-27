/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Lax253009Proofs.PCPFoundation.Classes.Time
import Lax253009Proofs.PCPFoundation.Classes.Space

/-!
# NP, coNP, and NPSPACE

This file defines **NP** (nondeterministic polynomial time), **coNP**, and
**NPSPACE** (nondeterministic polynomial space) in terms of the base classes
`NTIME` and `NSPACE`.
-/


set_option autoImplicit true

namespace Lax253009Proofs.PCPFoundation.Complexity

/-- **NP** is the class of languages decidable by a nondeterministic TM in
    polynomial time: `NP = ⋃_k NTIME(n^k)`. -/
def NP : Set Language :=
  ⋃ k : ℕ, NTIME (· ^ k)

/-- **coNP** is the class of languages whose complements are in NP. -/
def coNP : Set Language := complClass NP

/-- **NPSPACE** is the class of languages decidable by a nondeterministic TM
    using polynomial auxiliary space: `NPSPACE = ⋃_k NSPACE(n^k)`. -/
def NPSPACE : Set Language :=
  ⋃ k : ℕ, NSPACE (· ^ k)

end Lax253009Proofs.PCPFoundation.Complexity
