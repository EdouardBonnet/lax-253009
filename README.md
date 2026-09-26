# Håstad clique inapproximability: preparation status

Local submission: `lax-253009`, Lean `v4.33.0`.
Source: `../hastad.pdf`, Acta Mathematica 182 (1999), 105–142.
Nothing has been submitted or registered remotely.

## Proved components

- `Lax253009.Graphs`: Boolean adjacency matrices, their simple graphs,
  explicit binary encodings, and the clique number.
- `Lax253009.Approximation`: a uniform deterministic polynomial-time
  integer estimator satisfying the paper's approximation guarantee.
- `Lax253009.CliqueCorrespondence`: completeness and soundness of the
  consistency graph, exact equality of its clique number with the optimum
  acceptance count, and the vertex count and bound. Seven proved statements.
- `Lax253009.LongCodeCorrectness`: perfect completeness and Lemma 4.1,
  together with the local counterparts for the side-condition test.
  Four proved statements.
- `Lax253009.LongCodePatterns`: at most `2^s` accepting query patterns,
  both without and with side conditions. Two proved statements.
- `Lax253009.GraphEncoding`: invariance of the clique number under a
  bijective vertex numbering and the exact binary encoding length.
  Two proved statements.
- `Lax253009.SmallSupport`: the decoding-set cardinality bound from
  equation (2), with the squared-mass bound as an explicit hypothesis.
  One proved statement.
- `Lax253009.EncodedReduction`: the numbered consistency graph has the
  expected clique number, and a polynomial-time approximation separates
  any suitably spaced integer acceptance-count gap. Two proved statements.

There are eighteen proof entries. Their proofs do not assume any of the
submission's open statements. Definitions and theorem statements are in
`concepts/`, and their annotated proofs are in `proofs/`.

`Lax253009.CNASoundness` states Theorems 4.2 and 4.17 with their full
quantifier order and uniform finite probabilities. These two statements
remain open. In particular, the decoding set in Theorem 4.17 is chosen
before the side condition. Neither theorem is proved by assuming the other.

Build with `lax build . --replay` from this directory. This checks both
packages, replays the kernel proofs, and checks the archive annotations.

## Agreed theorem scope

Include both statements, for every fixed real ε > 0:

1. **Original Theorem 5.2:** existence of the above approximation implies
   NP = ZPP. Equivalently, under NP ≠ ZPP no such approximation exists.
2. **BPP consequence:** existence of the same approximation implies
   NP ⊆ BPP. Equivalently, under NP ⊈ BPP no such approximation exists.

The algorithm may depend on ε, but must be a single algorithm for all input
sizes. The guarantee is required on nonempty graphs. The algorithm outputs
a number, as in the paper's introduction, rather than a vertex set.

The second statement follows from the first and ZPP ⊆ BPP. The paper's
separate Theorem 5.3 gives the exponent 1/2 − ε under NP ≠ P; it is outside
the agreed scope.

## Existing complexity concepts and the unresolved dependency

An archive refresh on 2026-09-26 found:

| Concept | Submission | State | Environment |
| --- | --- | --- | --- |
| `Lax434930.NondeterministicPolynomialTime.NP` | lax-434930 | registered | v4.33.0 |
| `Lax47.Machine.InNP` | lax-47 | draft | v4.30.0 |
| `Lax47.Machine.InBPP` | lax-47 | draft | v4.30.0 |
| `Lax47.Machine.NPSubsetBPP` | lax-47 | draft | v4.30.0 |

Registered NP source:
`https://github.com/EdouardBonnet/classical-complexity`, commit
`0c0840319318215fd7b36a9a822b81ce55cf6941`, subdirectory `concepts`.

Archived BPP source:
`https://github.com/EdouardBonnet/mis-inapproximability`, commit
`e8e3010e3aae3531db7677c4acb8b0561cc21022`, subdirectory `concepts`.
It also depends on the draft lax-51, on the older environment.

The NP definitions use different input representations: binary strings in
lax-434930 and finite words of natural numbers encoded as binary strings in
lax-47. A port or extraction must address this representation boundary.

The archive requires dependencies to be registered in the same environment;
v4.30.0 is closed to new submissions. Adding lax-47 to this submission's
lakefile would therefore be invalid. No substitute BPP definition has been
introduced here.

The user will supply a separate Lax submission defining BPP and ZPP.
Use those concepts, together with the registered NP above, once the new
submission is available. It must use v4.33.0 and the same binary-language
type as `Lax434930.PolynomialTime.Language`, or provide explicit translations.
It should also expose ZPP ⊆ BPP for the consequence. Local review may use a
draft dependency, but archive submission requires it to be registered.

The concepts lakefile already pins lax-434930; the approximation definition
uses its binary-word type and the same underlying polynomial-time machine
model. The NP theorem and both randomized classes are intentionally deferred
until the forthcoming dependency can be imported. No local NP, BPP, or ZPP
definition is introduced.

Once that dependency is available, add a `CliqueHardness` concept with
the original statement and a `BPPConsequence` concept with the second
statement. Record a proof of the second relative to the original and
the imported ZPP ⊆ BPP statement, so the proof network exposes the exact
dependency. The substantial proof of Theorem 5.2 remains an open obligation.

## Remaining proof development

The dependency chain in the source is:

1. The bounded-occurrence satisfiability gap (Theorem 2.13) and parallel
   repetition (Theorem 2.14), giving the two-prover test (Theorem 3.2).
2. Long-code tests and their soundness analysis, including the version with
   side conditions (Theorem 4.17).
3. The PCP with logarithmic randomness and arbitrarily small amortized
   free-bit complexity (Theorem 5.1).
4. The PCP-to-clique transfer (Theorem 2.8), combined with Theorem 5.1 to
   obtain Theorem 5.2.
5. The implication from NP = ZPP to NP ⊆ BPP.

The finite consistency-graph and elementary long-code components above are
complete. Major remaining work includes the Fourier identities and moment
bounds in Section 4, the probability estimates for Theorems 4.2 and 4.17,
the two-prover and PCP constructions, and the randomized sparsification
and uniform machine implementation needed for the exponent in Theorem 2.8.
The present finite graph construction does not certify its own polynomial
running time or establish that exponent by itself.

The BPP/ZPP dependency only blocks the final complexity-class interfaces;
it does not block any of those independent mathematical developments.
The rational promise-gap interface in `Lax47.Hastad` additionally requires
a randomized gap statement and the graph-complement translation; the
deterministic approximation theorem alone does not discharge that interface.
