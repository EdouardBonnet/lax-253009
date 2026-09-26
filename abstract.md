Håstad proved that, for every fixed $\varepsilon>0$, a polynomial-time
$n^{1-\varepsilon}$-approximation of Max-Clique would imply
$\mathrm{NP}=\mathrm{ZPP}$ [\[1\]](#ref-Hastad1999Clique).
In particular, no such approximation exists if
$\mathrm{NP}\nsubseteq\mathrm{BPP}$.

The approximation algorithm returns an integer estimate $a(G)$ satisfying
$a(G)\leq\omega(G)\leq n^{1-\varepsilon}a(G)$, where $n$ is the number of
vertices and $\omega(G)$ is the clique number.

We prove the finite consistency-graph correspondence: its clique number is
the maximum number of random choices on which one proof is accepted. We
bound its number of vertices by the number of accepting local views and
connect the numbered graph to the approximation guarantee.

For Håstad's complete nonadaptive long-code test, we prove perfect
completeness, local decoding, and the bound of $s$ free bits, including
the extension with a side condition. We also prove the counting bound for
the small decoding set obtained from coefficients of bounded total squared
mass. The probabilistic soundness theorems are stated as open obligations;
the full inapproximability theorem is not yet proved.
