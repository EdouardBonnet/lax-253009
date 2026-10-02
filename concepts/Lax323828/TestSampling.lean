import Lax323828.LocalTests
import Lax323828.EncodedReduction
import Lax323828.BernoulliSampling

/-!
---
title: Random sparsification of a consistency graph
type: theorem
---
Sample $N$ independent random choices of a finite local-test system, with
replacement, and construct its consistency graph. Every sampled choice
keeps its own index, including repeated choices. Perfect completeness is
preserved for every sample, and $A$ accepting views per choice give at most
$NA$ vertices.

If every proof is accepted with probability at most $p$ and $Np\geq m+2$,
where $m$ is the proof length, then with probability at least $3/4$ the
sampled graph has clique number less than $4Np$. The bound holds
simultaneously for every proof, including proofs chosen after sampling.
-/

namespace Lax323828.TestSampling

open LocalTests FiniteProbability ConsistencyGraph

def Passes {r m : ℕ} (C : System r m) (π : Oracle m) (seed : Fin r) : Prop :=
  ∃ a ∈ C.accepting seed, Extends π a

def Complete {r m : ℕ} (C : System r m) : Prop := ∃ π, ∀ seed, Passes C π seed

def Sound {r m : ℕ} (C : System r m) (p : ℝ) : Prop :=
  ∀ π, probability (Passes C π) ≤ p

def sampled {r m N : ℕ} (C : System r m) (z : Fin N → Fin r) : System N m :=
  ⟨fun i ↦ C.accepting (z i)⟩

axiom vertex_bound {r m N : ℕ} (C : System r m) (z : Fin N → Fin r)
    (A : ℕ) (hA : ∀ seed, (C.accepting seed).card ≤ A) :
    Fintype.card (Vertex (sampled C z)) ≤ N * A

axiom perfect_completeness {r m N : ℕ} (C : System r m) (hC : Complete C)
    (z : Fin N → Fin r) :
    (EncodedReduction.output (sampled C z)).cliqueNumber = N

axiom soundness {r m N : ℕ} (hr : 0 < r) (C : System r m) (p : ℝ) (hp : 0 ≤ p)
    (hC : Sound C p) (hN : (m : ℝ) + 2 ≤ N * p) :
    probability (fun z : Fin N → Fin r ↦
      4 * N * p ≤ ((EncodedReduction.output (sampled C z)).cliqueNumber : ℝ)) ≤ 1 / 4

end Lax323828.TestSampling
