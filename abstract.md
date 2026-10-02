Håstad proved that, for every fixed $\varepsilon>0$, a deterministic polynomial-time
$n^{1-\varepsilon}$-approximation of Max-Clique would imply
$\mathrm{NP}=\mathrm{ZPP}$ [\[1\]](#ref-Hastad1999Clique).
We formalize this theorem and extend the inapproximability consequence under
$\mathrm{NP}\nsubseteq\mathrm{BPP}$ to bounded-error randomized algorithms,
using NP from [lax-434930](https://laxarchive.org/lax-434930/)
and BPP and ZPP from [lax-666725](https://laxarchive.org/lax-666725/).

**Acknowledgments and reused formalizations.** This submission builds substantially
on Samuel Schlesinger's [complexitylib](https://github.com/SamuelSchlesinger/complexitylib/tree/5a1696fdd3bff26a5e7197f3333e8bef50ea146a).
We gratefully credit Samuel Schlesinger and the upstream contributors, including
Bolton Bailey, credited as the author of the imported Dinur gap-theorem module.
The PCP foundation, Cook--Levin machinery, and supporting computational results
were adapted from that library, not newly formalized for this submission.
The port retains the original copyright and Apache-2.0 notices; its sources and
adaptations are documented in the [provenance record](https://github.com/EdouardBonnet/lax-323828/blob/680d3c797858ac58240148723ea651bd4fcdc9cd/LICENSES/PCPFoundation-provenance.md).
