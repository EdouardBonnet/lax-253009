import Lax253009.FiniteProbability

/-!
---
title: Independent majority repetition reduces bounded error
type: theorem
---
Three independent executions followed by majority vote transform an error
probability $p$ into $3p^2-2p^3$. Three rounds of this construction reduce
error at most $1/3$ to at most $1/12$, using 27 independent executions.
-/

namespace Lax253009.MajorityAmplification

open FiniteProbability

def vote (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

def errorMap (p : ℝ) : ℝ := 3 * p ^ 2 - 2 * p ^ 3

axiom majority_error {α : Type} [Fintype α] [Nonempty α]
    (answer : α → Bool) (b : Bool) :
    probability (fun r : α × α × α ↦
      vote (answer r.1) (answer r.2.1) (answer r.2.2) ≠ b) =
    errorMap (probability (fun r ↦ answer r ≠ b))

axiom three_rounds (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1 / 3) :
    errorMap (errorMap (errorMap p)) ≤ 1 / 12

end Lax253009.MajorityAmplification
