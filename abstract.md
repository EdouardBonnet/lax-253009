Håstad proved that, for every fixed $\varepsilon>0$, a polynomial-time
$n^{1-\varepsilon}$-approximation of Max-Clique would imply
$\mathrm{NP}=\mathrm{ZPP}$ [\[1\]](#ref-Hastad1999Clique).
We state this theorem using NP from lax-434930 and ZPP from lax-666725,
and prove its conditional consequence under
$\mathrm{NP}\nsubseteq\mathrm{BPP}$ using the imported ZPP ⊆ BPP inclusion.
**The main inapproximability proof is not yet complete.**

The approximation returns an integer estimate $a(G)$ satisfying
$a(G)\leq\omega(G)\leq n^{1-\varepsilon}a(G)$ on every nonempty graph.
We prove the finite consistency-graph correspondence, vertex bounds, binary
encoding properties, and separation of a suitable acceptance-count gap.

For the complete nonadaptive long-code test, we prove completeness, local
decoding, the free-bit bound, and normalization to odd tables, including
the side-condition extension. We develop finite Boolean Fourier analysis,
prove the small decoding-set bound and its behavior under projection,
and connect projection to accepted side-condition queries. The second-moment
identity, higher-moment cancellation, even-cover expansion, concentration,
hypercontractive bounds, and weighted double-cover estimates are also proved.
These yield explicit bounds for all three normalized Fourier terms, including
the small-coefficient higher-moment and tail estimates. We connect these
bounds to the actual CNA failure event and prove all asymptotic parameter
choices, completing soundness both with and without side conditions
(Theorems 4.17 and 4.2).

For Section 5, we prove the many-table agreement bounds, define the finite
FAF test, count its free bits, and extract globally consistent prover
strategies from its accepting runs. The resulting finite composition has
$20\ell s$ free bits and soundness below $2^{-20\ell^2s}$ given an explicit
sufficiently small two-prover soundness bound.

We connect the FAF verifier exactly to finite local tests, prove repetition
and randomized sparsification, and derive the strict approximation gap and
an explicit polynomial vertex bound. The verifier and sampling parameters
are chosen independently of the game question spaces. Binary interpretation
and modular reduction give a fixed-length fair-bit sampler; its bias changes
the decision error from at most $1/4$ to at most $1/3$. The combined finite
game-to-clique construction preserves perfect completeness.

We port the finite Dinur gap theorem and prove a regular 3-SAT gap reduction
with constant alphabet, degree, and gap and a polynomial vertex bound.
We convert it to a projection game with perfect completeness and soundness
at most one minus half the gap, and prove binary answer encoding and padding.
For soundness amplification we prove dimension-independent tuple-averaging
and sampler bounds and a squaring theorem for fortified projection tests.
We construct the fortified games and iterate squaring to arbitrary positive
target soundness. The sequence is fixed before the question spaces, with
constant answer alphabets, polynomial question-space growth, and perfect
completeness. No parallel-repetition theorem is assumed.

There are 162 proofs with no archive statement assumptions and three explicit
conditional deductions. An explicit simulation connects registered NP
verifiers to the computational Cook–Levin and Dinur constructions. It also
handles arbitrary binary outputs and the clique estimator's comparison.
The reverse simulation proves deterministic model equivalence. Explicit
random-tape verification proves RP ⊆ NP and ZPP ⊆ NP in the registered models.
Uniform polynomial-time implementations of the complete amplification,
FAF and sampled graph constructions, and the final NP = ZPP deduction
remain unfinished.
