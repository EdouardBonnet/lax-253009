Håstad proved that, for every fixed $\varepsilon>0$, a polynomial-time
$n^{1-\varepsilon}$-approximation of Max-Clique would imply
$\mathrm{NP}=\mathrm{ZPP}$ [\[1\]](#ref-Hastad1999Clique).
In particular, no such approximation exists if
$\mathrm{NP}\nsubseteq\mathrm{BPP}$.

The approximation algorithm returns an integer estimate $a(G)$ satisfying
$a(G)\leq\omega(G)\leq n^{1-\varepsilon}a(G)$, where $n$ is the number of
vertices and $\omega(G)$ is the clique number. The present concepts specify
the graph encoding and this polynomial-time approximation guarantee.
