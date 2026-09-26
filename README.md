# Håstad clique inapproximability: preparation status

Local submission: `lax-253009`, Lean `v4.33.0`.
Source: `../hastad.pdf`, Acta Mathematica 182 (1999), 105–142.
Nothing has been submitted or registered remotely.

## Current proof status

The submission contains 24 concepts and 53 proof entries. Of the proofs,
49 use only Lean's background axioms; four are conditional deductions with
explicit archive statement dependencies. The full inapproximability theorem
is **not yet proved**.

Two statements have no proof entry:

- `Lax253009.CNASoundness.with_side_conditions` — Theorem 4.17.
- `Lax253009.CliqueHardness.approximation_implies_np_eq_zpp` — Theorem 5.2.

Theorem 4.2 is proved relative to Theorem 4.17, by choosing the constant true
side condition. Theorem 4.17 does not depend on Theorem 4.2. The two
inapproximability formulations and the BPP implication remain conditional
on Theorem 5.2. A proof entry for a consequence does not close its assumptions.

## Proved components

| Component | Result checked in Lean |
| --- | --- |
| `CliqueCorrespondence` | Consistency-graph completeness and soundness, exact clique number, vertex count and bound (7 statements) |
| `LongCodeCorrectness` | Perfect completeness and local decoding, with and without a side condition (4) |
| `LongCodePatterns` | At most `2^s` accepting query patterns for both tests (2) |
| `GraphEncoding`, `EncodedReduction` | Numbering preserves clique number, encoding length, and approximation separates a suitable acceptance-count gap (4) |
| `SmallSupport` | Decoding-set cardinality bound from bounded squared coefficient mass (1) |
| `BooleanFourier` | Orthogonality, inversion, Parseval, sign-valued energy, and bounded-function energy (5) |
| `FourierProjection` | Averaging deletes exactly the coefficients outside the retained coordinates, preserves the bound one, and preserves constant fibers (3) |
| `FourierDecoding` | The actual Fourier decoding set has size at most `2^t`; projection can only shrink it into the satisfying set (2) |
| `FourierIdentities` | Character shift, vanishing even coefficients of odd functions, and the disagreement-indicator identities (4) |
| `ProductMoments` | Balanced mixed-moment cancellation, the exact second-moment identity in equation (7), and reduction of the high-degree bound to correlations (3) |
| `HigherMoments` | Coordinate factorization, singleton cancellation, and the double-cover union-size bound (3) |
| `EvenCovers` | Character moments, the exact even-cover expansion of polynomial moments, and even covers are double covers (3) |
| `FiniteProbability` | Event monotonicity, union bound, and the even-moment tail inequality (3) |
| `SideConditionAveraging` | Averaging over a side-condition fiber preserves each accepted query (1) |
| `OddNormalization` | Repair of arbitrary tables to odd tables, preserving accepted queries and both acceptance tests (4) |

These results do not assume either open theorem. In particular, the
second-moment formula and the even-cover expansion are proved identities;
the subsequent concentration and hypercontractive bounds remain unfinished.
The normalization justifies the odd-table assumption in footnote (4).

## Complexity classes and theorem scope

All three classes are reused without local substitutes:

| Class | Imported definition |
| --- | --- |
| NP | `Lax434930.NondeterministicPolynomialTime.NP` |
| BPP | `Lax666725.RandomizedPolynomialTime.BPP` |
| ZPP | `Lax666725.ZeroError.ZPP` |

They share `Lax434930.PolynomialTime.Language`, the set of binary words.
ZPP uses the bounded-time definition with an explicit failure answer.
The final machine construction must establish this exact definition.

The concepts and proofs pin randomized-complexity at
`31864d7e719d388b3d682a807fa2e56c8f9e0ae6` (`lax-666725`); classical-complexity
is pinned at `0c0840319318215fd7b36a9a822b81ce55cf6941` (`lax-434930`).
On the latest archive refresh, lax-666725 is a draft. Local builds allow
this; archive submission requires its registration.

For every fixed real ε > 0, `CliqueHardness` states that a deterministic
polynomial-time `n^(1−ε)` approximation implies NP = ZPP, and records its
NP ≠ ZPP contrapositive. `BPPConsequence` states the implication NP ⊆ BPP
and its contrapositive under NP ⊈ BPP. The BPP deduction uses the imported
`Lax666725.ZPPSubsetBPP.ZPP_subset_BPP` theorem, with that dependency
recorded in the proof network.

The algorithm may depend on ε but is uniform across all input sizes. It
returns an integer estimate `a(G)` with
`a(G) ≤ ω(G) ≤ n^(1−ε) a(G)` on every nonempty graph. This matches the
paper's numerical-estimation convention. The separate exponent `1/2−ε`
under NP ≠ P in Theorem 5.3 is outside the agreed scope.

## Remaining proof development

The principal remaining tasks are:

1. Concentration of random fibers and balanced-predicate correlations
   (Lemmas 4.3, 4.7, 4.9), the hypercontractive bound, and the weighted
   double-cover estimates (Lemmas 4.13–4.16).
2. Decomposition of the CNA failure event into the three Fourier terms,
   their tail bounds, and the parameter estimates proving Theorem 4.17.
3. The two-prover construction from bounded-occurrence satisfiability and
   parallel repetition, followed by the PCP construction in Theorem 5.1.
4. Randomized sparsification and uniform polynomial-time machine
   implementations for the PCP-to-clique transfer in Theorem 2.8, and
   the final NP = ZPP implication.

The finite graph correspondence does not by itself certify the reduction's
running time or the final approximation exponent. The imported NP and ZPP
use distinct concrete machine representations; their required simulation
and reduction implementations remain part of the final proof obligation.

## Validation

From this directory:

```sh
lax build . --replay
python3 scripts/audit-proof-closure.py
```

The build compiles both packages, replays their kernel proofs, and checks
all concept/proof annotations and axiom hygiene. The audit checks that the
only statement assumptions are the four documented deductions, verifies
the upstream ZPP ⊆ BPP proof closure, and reports the remaining local roots.
The generated build output and Lake artifacts are ignored by Git.
