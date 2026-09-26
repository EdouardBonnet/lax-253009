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
