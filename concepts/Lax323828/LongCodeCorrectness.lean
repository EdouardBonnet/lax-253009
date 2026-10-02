import Lax323828.LongCode

/-!
---
title: Perfect completeness and local decoding of the long-code test
type: theorem
---
Every genuine long code passes the complete nonadaptive test. Conversely,
whenever the test accepts, all its answers agree with evaluation at one
word. This is Lemma 4.1 of Håstad's paper; it concerns a fixed run and does
not assert global closeness of the table to a long code.

A genuine code also passes the extended test whenever its encoded word
satisfies the side condition. Any accepting extended run has a compatible
evaluation point satisfying the condition. The latter is a local statement,
distinct from the probabilistic bound and the fixed small decoding set in
Theorem 4.17.
-/

namespace Lax323828.LongCodeCorrectness

open LongCode

axiom perfect_completeness {w s : ℕ} (x : Word w) (f : Fin s → Coordinate w) :
  Accepts (evaluation x) f

axiom local_decoding {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w)
    (h : Accepts A f) :
  ∃ x : Word w, LooksLike A f x

axiom side_condition_completeness {w s : ℕ} (x : Word w) (f : Fin s → Coordinate w)
    (h : Coordinate w) (hx : h x = true) :
  AcceptsWithCondition (evaluation x) f h

axiom side_condition_decoding {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w)
    (h : Coordinate w) (haccept : AcceptsWithCondition A f h) :
  ∃ x : Word w, h x = true ∧ LooksLike A f x

end Lax323828.LongCodeCorrectness
