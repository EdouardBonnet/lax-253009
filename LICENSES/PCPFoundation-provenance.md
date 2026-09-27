# Dinur gap-theorem source

The 62 modules under `proofs/Lax253009Proofs/PCPFoundation` are adapted from
[complexitylib](https://github.com/SamuelSchlesinger/complexitylib), commit
`5a1696fdd3bff26a5e7197f3333e8bef50ea146a`. They are the dependency closure of
`Complexitylib.Classes.PCP.Internal.GapTheorem` within that project.

Original copyright notices and authors are retained in each file. These
files are distributed under Apache-2.0; the full license is included as
`complexitylib-Apache-2.0.txt` in this directory.

The complete source of these dependency modules is retained, including
supporting lemmas not yet consumed by the annotated gap theorem. This keeps
the upstream arguments readable and supports the subsequent computational
construction. Lax reports the unused supporting declarations as warnings.

The port targets this submission's Lean 4.33 and pinned mathlib. Changes:

- Relocate imports to `Lax253009Proofs.PCPFoundation` and relocate declarations beneath
  `Lax253009Proofs.PCPFoundation.Complexity`, as required by Lax.
- Remove newer module visibility directives.
- Replace the moved real-number import and renamed conditional lemmas.
- Adapt the nonnegativity argument of the finite product inequality.
- Make two previously implicit Fourier-analysis binders explicit.
- Adjust three elaboration details in finite rotation, rejection-set
  counting, and rational arithmetic proofs.
- Seal the fixed amplifier with `irreducible_def` and its proved defining
  equation, preventing downstream kernel checks from expanding its large
  constant construction.

The original computational PCP implementation is not included in this
port. The imported gap theorem proves the finite construction, completeness,
constant soundness gap, and a polynomial edge bound. Machine running times
require additional proofs.


The computational extension also ports the dependency closure of
`Complexitylib.Classes.PCP.Internal.AlgGapCSP` at the same commit. This adds
Cook–Levin, the exact-3-CNF reduction, Cobham's function algebra and machine
characterization, and the polynomial-time gap-graph algorithms. These internal
machine classes are implementation tools; the submission's headline NP, BPP,
and ZPP definitions remain the registered Lax classes.

The only additional source dependency is
`Cslib/Computability/Circuit/Signature.lean` from
<https://github.com/SamuelSchlesinger/cslib> at
`2a4389ba8d47778cafdd79f522f0b17b623b18b7`, also Apache-2.0. Its copyright
notice is retained. Its two declarations are namespaced under
`Lax253009Proofs.PCPFoundation.Cslib`; its initialization import is replaced
by the required Mathlib finite-index import.

Additional Lean 4.33 adaptations: finite-type imports use `Mathlib.Data.Finite`;
`List.sum_le_card_nsmul` replaces the later renamed length lemma; the positive
literal evaluation proof unfolds explicitly; and a Boolean conditional in
`AlgKilled` uses `Bool.cond_false`. New ported modules explicitly retain the
upstream `autoImplicit` setting. The finite-prefix/suffix extension is moved
under the submission namespace and its uses are qualified. Existing checked
finite-Dinur modules and their kernel-normalization barrier are retained.

The computational extension also includes the twelve modules needed for
`Classes.NP.WitnessConstruction` from the same pinned revision, including
the nondeterministic composition and polynomial witness construction.
Binary-number codec extensions are moved from root `Nat`/`Fin` namespaces
into `Lax253009Proofs.PCPFoundation.BinaryNat` and `BinaryFin`. Direct Aesop
imports are replaced by `Mathlib.Data.Set.Operations`, which exposes those
rules through a permitted dependency.

The original `RegisteredBridge` development proves an explicit simulation
from registered finite-stack machines to the ported model. Its statement
length estimate follows the already registered `TM2Bounds.stepAux_length`
in `lax-434930`, at the dependency revision in `proofs/lakefile.toml`.
The bridge reuses the registered complexity-class definitions. Its explicit
finite-alphabet normalization is now included below, so the simulation
requires no archive theorem assumption.

`RegisteredBridge/Time.lean` and `RegisteredBridge/FiniteAlphabet.lean`
port the corresponding helper modules from
<https://github.com/EdouardBonnet/classical-complexity> at
`0c0840319318215fd7b36a9a822b81ce55cf6941` (Apache-2.0). Namespaces and
imports are adjusted; the final computer-normalization theorem is generalized
from Boolean decisions to arbitrary outputs encoded as Boolean words.
