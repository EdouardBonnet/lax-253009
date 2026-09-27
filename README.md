# Håstad clique inapproximability: preparation status

Local submission: `lax-253009`, Lean `v4.33.0`.
Source: `../hastad.pdf`, Acta Mathematica 182 (1999), 105–142.
Nothing has been submitted or registered remotely.

## Current proof status

The submission contains 63 concepts and 165 proof entries. Of the proofs,
162 use only Lean's background axioms; three are conditional deductions with
explicit archive statement dependencies. The full inapproximability theorem
is **not yet proved**.

One statement has no proof entry:

- `Lax253009.CliqueHardness.approximation_implies_np_eq_zpp` — Theorem 5.2.

Theorems 4.17 and 4.2 are proved with no archive statement assumptions.
Theorem 4.2 follows from the proved Theorem 4.17 by choosing the constant true
side condition. The finite FAF composition, its free-bit count, and the
strategy-extraction argument of Section 5 are also proved. The finite
game-to-clique transfer is proved, including the exact local-view interface,
repetition, sparsification, approximation exponent, polynomial vertex bound,
and sampling from a fixed vector of fair bits. The two
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
| `HigherMoments` | Coordinate factorization, singleton cancellation, the double-cover union-size bound, and extraction of a double subcover (4) |
| `EvenCovers` | Character moments, the exact even-cover expansion of polynomial moments, and even covers are double covers (3) |
| `FiniteProbability` | Event monotonicity, binary and finite union bounds, restriction to a subset, bounded power means, and the even-moment tail inequality (6) |
| `ExponentialBounds` | Exponential Markov, the bounded-variable moment-generating-function estimate, independent bounded sums, and weighted Rademacher tails (6) |
| `BalancedPredicates`, `RandomFibers` | Central-binomial counting and mass, balanced correlation tails, and lower tails for single and arbitrary random fibers (5) |
| `Hypercontractivity` | Fourth moments, multiplication of Fourier degrees, dyadic moments, and a bound for every moment (5) |
| `DoubleCoverBounds`, `SmallUnionDoubleCovers` | Dimension-independent bounds for total double-cover weight and small-union weight, corresponding to Lemmas 4.15 and 4.16 (2) |
| `BalancedCancellation` | Cancellation against characters and arbitrary bounded functions depending on a fixed support (2) |
| `MixedPredicateMoments` | The mixed-predicate estimate used in Lemma 4.12 (1) |
| `HighDegreeSoundness`, `SmallCoefficientSoundness`, `LargeCoefficientSoundness` | Explicit estimates for all three normalized Fourier terms: two moment bounds, their tails, and deterministic cancellation (5) |
| `SideConditionAveraging` | Averaging over a side-condition fiber preserves each accepted query (1) |
| `OddNormalization` | Repair of arbitrary tables to odd tables, preserving accepted queries and both acceptance tests (4) |
| `CNAPointSoundness`, `CNAQuantitativeSoundness` | Decoding-set size, pointwise failure bound from the three Fourier terms, and the actual CNA failure probability with arbitrary side conditions (3) |
| `CNASoundness` | Asymptotic soundness with and without side conditions, including all parameter choices (2) |
| `ManyTableConsistency` | Representative-table counting and random-function agreement bounds underlying Lemmas 5.7 and 5.8 (2) |
| `FAFTest`, `FAFPatterns` | Explicit finite FAF verifier, perfect completeness, quantitative acceptance bound, inclusion of actual transcripts, and the `q + ns` free-bit bound (4) |
| `DecodedStrategies`, `FAFStrategyExtraction` | Globally consistent prover strategies from decoded sets, finite extraction, and uniform extraction using the proved CNA theorem (3) |
| `FAFComposition` | Soundness below `2^(-20*l*l*s)` with `20*l*s` free bits, given an explicit positive two-prover game threshold (2) |
| `BernoulliSampling` | Multiplicative upper tail for independent samples and its simultaneous bound for at most `2^m` events (2) |
| `TestRepetition` | Coherent merged views, exact fixed-proof acceptance probability, accepting-view count, completeness, and soundness after repetition (5) |
| `TestSampling` | Vertex bound, perfect completeness, and simultaneous clique soundness after sampling (3) |
| `SamplingParameters` | Logarithmic repetition count, explicit polynomial size bound, strict approximation gap, and a uniform multiplier (3) |
| `RandomizedReduction` | Repeated sampled graph size, soundness, and a decision rule from the given polynomial-time estimator (3) |
| `FAFLocalTests` | Exact conversion of FAF transcripts into local views, acceptance probability, free bits, completeness, soundness, proof length, and random-choice count (7) |
| `FreshBitSampling` | Modulo bias, explicit fair-bit sampling with error at most `1/12`, resulting `1/3` error, flattening to one bit vector, and repeated-seed bit bound (5) |
| `GapSatisfiability` | Dinur's fixed-alphabet regular gap theorem, with positive gap and polynomial vertex bound (1) |
| `ProjectionGames` | Perfect completeness and soundness at most `1 - gap/2`, allowing partial strategies (2) |
| `ProjectionEncoding` | Binary encoding existence, completeness, and soundness, allowing arbitrary padding (3) |
| `TupleAveraging` | Variance and restriction bounds independent of the alphabet size (2) |
| `TupleSampler` | Planted-coordinate probabilities, exact mean, and squared mean absolute deviation at most `1/t` (3) |
| `FortifiedSquaring` | Two-copy soundness from rectangular restriction bounds (1) |
| `TupleFortification` | Preservation of completeness, soundness and uniform marginals, and rectangular restriction bound `4r` for `1/t ≤ r²` (5) |
| `CenteredProjection` | Symmetrization, reverse square-root bound, complete and uniform transformations, squaring, and regular-CSP interface (10) |
| `Amplification` | Arbitrarily small value with a sequence fixed before the question spaces, preservation of completeness and uniformity, exact cardinalities and polynomial size (7) |
| `GameToClique` | Combined finite construction with parameters fixed before the game question spaces, perfect completeness, `1/3` false-positive probability, and polynomial graph size (1) |

These results do not assume the open clique-hardness theorem. The three Fourier
estimates apply to general finite label spaces and coefficient families and
are now connected to the actual CNA failure event. Their constants are
explicit and nonoptimal. Conditioning independent signs on balance introduces
an extra factor N+1 in concentration, and the moment estimates use larger
constants than the paper. All parameter and asymptotic deductions needed
for CNA soundness are proved. The decoding set is chosen independently of
the side condition; projection shrinks it into the satisfying set. The
normalization separately justifies the odd-table assumption in footnote (4).

The finite FAF argument uses decoded sets of size `2^s`, a slightly weaker
bound than the paper's `2^(s/2)`, and an extra failure slot when extracting
prover strategies. The resulting explicit positive game threshold suffices
for the same free-bit-to-soundness ratio. The strategies depend only on
their respective questions, even when different extensions give the same
first-prover question.

The FAF parameter thresholds are uniform across all finite question spaces.
The local-view construction filters incompatible transcripts before merging,
so repeated queries and repeated table names remain consistent. With proof
length `m`, base soundness `2^(-t)`, and at most `2^f` accepting views, the
sampling construction chooses `k = c * (clog 2 (m+2) + 3)` repetitions and
`(m+2) * 2^(t*k)` samples. The graph has at most
`16^((t+f)*c) * (m+2)^((t+f)*c+1)` vertices. Its low-clique threshold is
`4*(m+2)`, and the approximation gap holds when
`c * (epsilon*t - (1-epsilon)*f) >= 1`.

Sampling `N` elements from `r` choices uses exactly
`N * clog 2 (12*N*r)` fair bits and binary remainder. The finite modulo-bias
proof adds at most `1/12` to the uniform-sampling error of `1/4`. The
`GameToClique` conclusion uses this explicit bit sampler. These finite
constructions and size bounds do not certify a probabilistic Turing
machine's running time.

## PCP foundation and soundness amplification

The finite Dinur gap theorem is ported from 62 complexitylib modules,
with original copyright notices and Apache-2.0 license retained. See
[provenance](LICENSES/PCPFoundation-provenance.md). The regular gap reduction
has a fixed alphabet and degree, a positive constant gap, and a polynomial
vertex bound. It preserves satisfiability. A separate proof converts regular
constraints to a projection game with soundness at most `1 - gap/2` and
perfect completeness, including partial prover strategies. Finite alphabets
can be encoded into arbitrarily padded Boolean words without increasing
soundness.

The soundness-amplification development includes a dimension-independent
variance bound for tuple averages and its restriction estimate, a tuple
sampler with squared mean absolute deviation at most `1/t`, and the
squaring theorem for fortified projection tests. The latter bounds two-copy
soundness by `v*s + |B|*eta`, where `B` is the common projection alphabet.
Tuple fortification is proved, including its `4r` rectangular error when
`1/t ≤ r²`, preservation of soundness and uniform marginals, and perfect
completeness. Centered games retain the projection structure through
fortification and squaring. Iterating gives arbitrary positive target
soundness with a fixed transformation sequence chosen before all question
spaces. Exact cardinality formulas prove polynomial question-space growth
and fixed answer alphabets. No parallel-repetition result is assumed as an axiom.

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
The latest archive refresh confirms that lax-666725 is registered. Its
ZPP ⊆ BPP proof has closed upstream dependencies, as checked by the audit.

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

The registered NP model now connects to the ported Cook–Levin theorem by an
explicit stack-machine simulation. The simulation encodes finite alphabets,
compiles every instruction block, bounds all intermediate configurations,
and handles arbitrary binary-encoded outputs. Finite-alphabet restriction
is proved without changing the running-time polynomial. The resulting
integer-estimator comparison is polynomial-time even for large outputs.
The computational Dinur port supplies a nonempty encoded gap graph for
every registered NP language. The finite small-value game reduction now
applies to those languages with answer alphabets fixed before the language.
Explicit product, tuple, and sum encodings supply polynomial-time numbering
in both directions. The regularized projection-game queries, every fixed
fortification and squaring stage, and binary answer encoding are now proved
polynomial-time. These combine into `computable_small_value`, a uniform
small-value game reduction for each registered NP language.
The reverse multitape-to-stack simulation now proves equality with the
registered deterministic class, including input conversion, output extraction,
cleanup, and a polynomial clock. A finite-coin simulator and an explicit
certificate-pair decoder prove RP ⊆ NP and ZPP ⊆ NP for the registered classes.

## Remaining proof development

The uniform FAF transcript and compatibility queries, logarithmic repetition,
fair-bit sampling, and full adjacency-matrix construction are now proved
polynomial-time. `RegisteredBridge.approximation_random_test` assembles them:
an assumed clique approximation gives every registered NP language a
polynomial-time predicate on the input and an explicitly bounded fair-bit
tape. Members pass on every tape; nonmembers pass with probability at most
1/3. This algorithm theorem has passed the full Lax kernel replay.

The principal remaining tasks are:

1. Compile this fair-bit test into the registered probabilistic model,
   preserving its probability distribution and worst-case polynomial clock.
2. Combine complementary one-sided algorithms into ZPP. RP ⊆ NP and
   ZPP ⊆ NP are proved. The final NP = ZPP implication still needs this
   construction and its probability-preservation proof.

The approximation exponent, polynomial graph-size bound, deterministic
running time, and finite-coin error estimate are proved. The registered
probabilistic-machine implementation and zero-error combination still
belong to the final proof obligation.

## Validation

From this directory:

```sh
lax build . --replay
python3 scripts/audit-proof-closure.py
```

The build compiles both packages, replays their kernel proofs, and checks
all concept/proof annotations and axiom hygiene. The audit checks that the
only statement assumptions are the three documented deductions, verifies
the upstream ZPP ⊆ BPP proof closure, and reports the remaining local roots.
The generated build output and Lake artifacts are ignored by Git.
