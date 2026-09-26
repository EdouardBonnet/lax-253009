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
identity, higher-moment cancellation, even-cover expansion, and finite
moment tail inequality are also proved.

There are 49 proofs with no archive statement assumptions and four explicit
conditional deductions. The concentration and hypercontractive estimates,
full soundness theorem, PCP construction, and computational transfer to
clique inapproximability remain unfinished.
