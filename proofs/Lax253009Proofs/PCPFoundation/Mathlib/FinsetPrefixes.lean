/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Infix

/-!
# Finsets of prefixes and suffixes

For a finite set `S` of lists, `Finset.prefixes S` is the finite set of all
prefixes of elements of `S`, and `Finset.suffixes S` the finite set of all
suffixes of elements of `S`. The two operations have dual APIs: membership
characterizations (`mem_prefixes`/`mem_suffixes`), self-membership, and
closure under taking further prefixes/suffixes.

This file lives in `Complexitylib/Mathlib/` because it extends a Mathlib
type in its home namespace — the sanctioned exception to the `Lax253009Proofs.PCPFoundation.Complexity`
root-namespace rule. Its contents are candidates for upstreaming to Mathlib.
-/

set_option autoImplicit true

namespace Lax253009Proofs.PCPFoundation.FiniteWords

variable {α : Type*} [DecidableEq α] {S : Finset (List α)}

/-- The finite set of all prefixes of elements of `S`. -/
def prefixes (S : Finset (List α)) : Finset (List α) :=
  S.biUnion fun s => s.inits.toFinset

/-- The finite set of all suffixes of elements of `S`. -/
def suffixes (S : Finset (List α)) : Finset (List α) :=
  S.biUnion fun s => s.tails.toFinset

theorem mem_prefixes {p : List α} : p ∈ prefixes S ↔ ∃ s ∈ S, p <+: s := by
  simp [prefixes, List.mem_inits]

theorem mem_suffixes {w : List α} : w ∈ suffixes S ↔ ∃ s ∈ S, w <:+ s := by
  simp [suffixes, List.mem_tails]

theorem mem_prefixes_self {s : List α} (hs : s ∈ S) : s ∈ prefixes S :=
  mem_prefixes.2 ⟨s, hs, List.prefix_rfl⟩

theorem mem_suffixes_self {s : List α} (hs : s ∈ S) : s ∈ suffixes S :=
  mem_suffixes.2 ⟨s, hs, List.suffix_rfl⟩

theorem nil_mem_prefixes (hS : S.Nonempty) : ([] : List α) ∈ prefixes S :=
  let ⟨s, hs⟩ := hS
  mem_prefixes.2 ⟨s, hs, List.nil_prefix⟩

theorem nil_mem_suffixes (hS : S.Nonempty) : ([] : List α) ∈ suffixes S :=
  let ⟨s, hs⟩ := hS
  mem_suffixes.2 ⟨s, hs, List.nil_suffix⟩

/-- `prefixes S` is downward closed under taking prefixes. -/
theorem mem_prefixes_of_prefix {p q : List α} (hpq : p <+: q) (hq : q ∈ prefixes S) :
    p ∈ prefixes S := by
  obtain ⟨s, hs, hqs⟩ := mem_prefixes.1 hq
  exact mem_prefixes.2 ⟨s, hs, hpq.trans hqs⟩

/-- `suffixes S` is downward closed under taking suffixes. -/
theorem mem_suffixes_of_suffix {w v : List α} (hwv : w <:+ v) (hv : v ∈ suffixes S) :
    w ∈ suffixes S := by
  obtain ⟨s, hs, hvs⟩ := mem_suffixes.1 hv
  exact mem_suffixes.2 ⟨s, hs, hwv.trans hvs⟩

end Lax253009Proofs.PCPFoundation.FiniteWords
