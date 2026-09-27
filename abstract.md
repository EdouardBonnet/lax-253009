Håstad proved that, for every fixed $\varepsilon>0$, a polynomial-time
$n^{1-\varepsilon}$-approximation of Max-Clique would imply
$\mathrm{NP}=\mathrm{ZPP}$ [\[1\]](#ref-Hastad1999Clique).
We prove this theorem using NP from [lax-434930](https://laxarchive.org/lax-434930/)
and ZPP from [lax-666725](https://laxarchive.org/lax-666725/),
and its consequence under $\mathrm{NP}\nsubseteq\mathrm{BPP}$ using the
imported ZPP ⊆ BPP inclusion.

We also state the randomized promise-gap form for Max Independent Set:
for each integer $q\geq3$, a bounded-error polynomial-time algorithm
distinguishing $\alpha(G)\leq n^{1/q}$ from
$\alpha(G)\geq n^{1-1/q}$ on sufficiently large graphs would imply
$\mathrm{NP}\subseteq\mathrm{BPP}$. This additional statement is an
explicit unproven axiom.
