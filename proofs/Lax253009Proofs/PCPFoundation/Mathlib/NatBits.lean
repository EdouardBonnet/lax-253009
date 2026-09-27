/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-!
# Fixed-width binary encodings of natural numbers

Big-endian, fixed-width binary encoding `Lax253009Proofs.PCPFoundation.BinaryNat.toBits` with its exact decoder
`Lax253009Proofs.PCPFoundation.BinaryNat.fromBits`, plus the little-endian views `Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE` and
`Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE` used by local Turing-machine arithmetic. Both conventions
have exact length, truncation, round-trip, and fixed-width injectivity lemmas.
Values wider than the target width are truncated modulo `2 ^ w`.
The final layer packages these bits into a canonical ceiling-logarithmic codec
for `Fin n`, including exact rejection conditions for malformed inputs.

The port keeps these extensions in the submission’s proof namespace.
-/


/-- Encode a natural number as a big-endian binary list of exactly `w` bits.
    Numbers larger than `2^w - 1` are truncated (mod 2^w). -/
def Lax253009Proofs.PCPFoundation.BinaryNat.toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, val => (val / 2 ^ w % 2 == 1) :: Lax253009Proofs.PCPFoundation.BinaryNat.toBits w val

theorem Lax253009Proofs.PCPFoundation.BinaryNat.length_toBits : ∀ (w val : ℕ), (Lax253009Proofs.PCPFoundation.BinaryNat.toBits w val).length = w
  | 0, _ => rfl
  | w + 1, val => by simp [Lax253009Proofs.PCPFoundation.BinaryNat.toBits, Lax253009Proofs.PCPFoundation.BinaryNat.length_toBits w]

/-- Decode a big-endian binary list to a natural number. -/
def Lax253009Proofs.PCPFoundation.BinaryNat.fromBits : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) * 2 ^ rest.length + Lax253009Proofs.PCPFoundation.BinaryNat.fromBits rest

/-- Decoded values are bounded by `2 ^ length`. -/
theorem Lax253009Proofs.PCPFoundation.BinaryNat.fromBits_lt_pow_length : ∀ (l : List Bool), Lax253009Proofs.PCPFoundation.BinaryNat.fromBits l < 2 ^ l.length
  | [] => by simp [Lax253009Proofs.PCPFoundation.BinaryNat.fromBits]
  | b :: rest => by
    have ih := Lax253009Proofs.PCPFoundation.BinaryNat.fromBits_lt_pow_length rest
    simp only [Lax253009Proofs.PCPFoundation.BinaryNat.fromBits, List.length_cons, pow_succ]
    rcases b with _ | _ <;> simp <;> omega

/-- `fromBits ∘ toBits w` reduces any input modulo `2 ^ w`. -/
theorem Lax253009Proofs.PCPFoundation.BinaryNat.fromBits_toBits_mod : ∀ (w val : ℕ),
    Lax253009Proofs.PCPFoundation.BinaryNat.fromBits (Lax253009Proofs.PCPFoundation.BinaryNat.toBits w val) = val % 2 ^ w
  | 0, val => by simp [Lax253009Proofs.PCPFoundation.BinaryNat.toBits, Lax253009Proofs.PCPFoundation.BinaryNat.fromBits, Nat.mod_one]
  | w + 1, val => by
    have ih := Lax253009Proofs.PCPFoundation.BinaryNat.fromBits_toBits_mod w val
    simp only [Lax253009Proofs.PCPFoundation.BinaryNat.toBits, Lax253009Proofs.PCPFoundation.BinaryNat.fromBits, Lax253009Proofs.PCPFoundation.BinaryNat.length_toBits, ih]
    have hbit : (val / 2 ^ w) % 2 = if (val / 2 ^ w % 2 == 1) then 1 else 0 := by
      rcases Nat.mod_two_eq_zero_or_one (val / 2 ^ w) with h | h <;> simp [h]
    have hpow : (2 : ℕ) ^ (w + 1) = 2 ^ w * 2 := by rw [pow_succ]
    have hkey : val % 2 ^ (w + 1) = (val / 2 ^ w) % 2 * 2 ^ w + val % 2 ^ w := by
      rw [hpow, Nat.mod_mul, Nat.mul_comm (2^w) _, Nat.add_comm]
    rw [hkey, ← hbit]

/-- `Lax253009Proofs.PCPFoundation.BinaryNat.fromBits` is a left inverse of `Lax253009Proofs.PCPFoundation.BinaryNat.toBits` on values below `2 ^ w`. -/
theorem Lax253009Proofs.PCPFoundation.BinaryNat.fromBits_toBits {w val : ℕ} (hv : val < 2 ^ w) :
    Lax253009Proofs.PCPFoundation.BinaryNat.fromBits (Lax253009Proofs.PCPFoundation.BinaryNat.toBits w val) = val := by
  rw [Lax253009Proofs.PCPFoundation.BinaryNat.fromBits_toBits_mod, Nat.mod_eq_of_lt hv]

/-- Adding a multiple of `2^w` does not change the low `w` encoded bits. -/
theorem Lax253009Proofs.PCPFoundation.BinaryNat.toBits_add_pow_mul : ∀ (w val c : ℕ),
    Lax253009Proofs.PCPFoundation.BinaryNat.toBits w (val + c * 2 ^ w) = Lax253009Proofs.PCPFoundation.BinaryNat.toBits w val
  | 0, _, _ => rfl
  | w + 1, val, c => by
    have hrw : val + c * 2 ^ (w + 1) = val + c * 2 * 2 ^ w := by
      rw [pow_succ]
      simp [Nat.mul_comm, Nat.mul_assoc]
    have hdiv : (val + c * 2 * 2 ^ w) / 2 ^ w = val / 2 ^ w + c * 2 :=
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos w)
    simp only [hrw, Lax253009Proofs.PCPFoundation.BinaryNat.toBits, hdiv, List.cons.injEq]
    constructor
    · rw [Nat.add_mul_mod_self_right]
    · exact Lax253009Proofs.PCPFoundation.BinaryNat.toBits_add_pow_mul w val (c * 2)

/-- Fixed-width encoding recovers every bit list from its decoded value. -/
theorem Lax253009Proofs.PCPFoundation.BinaryNat.toBits_fromBits : ∀ bits : List Bool,
    Lax253009Proofs.PCPFoundation.BinaryNat.toBits bits.length (Lax253009Proofs.PCPFoundation.BinaryNat.fromBits bits) = bits
  | [] => rfl
  | bit :: rest => by
    have hlt := Lax253009Proofs.PCPFoundation.BinaryNat.fromBits_lt_pow_length rest
    have hval : Lax253009Proofs.PCPFoundation.BinaryNat.fromBits (bit :: rest) =
        Lax253009Proofs.PCPFoundation.BinaryNat.fromBits rest + (if bit then 1 else 0) * 2 ^ rest.length := by
      simp only [Lax253009Proofs.PCPFoundation.BinaryNat.fromBits]
      exact Nat.add_comm _ _
    simp only [List.length_cons, Lax253009Proofs.PCPFoundation.BinaryNat.toBits, List.cons.injEq]
    constructor
    · rw [hval, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt]
      cases bit <;> simp
    · rw [hval, Lax253009Proofs.PCPFoundation.BinaryNat.toBits_add_pow_mul, Lax253009Proofs.PCPFoundation.BinaryNat.toBits_fromBits rest]

/-- Decoding is injective among bit lists of the same width. -/
theorem Lax253009Proofs.PCPFoundation.BinaryNat.fromBits_inj_of_length_eq {first second : List Bool}
    (hlen : first.length = second.length)
    (hvalue : Lax253009Proofs.PCPFoundation.BinaryNat.fromBits first = Lax253009Proofs.PCPFoundation.BinaryNat.fromBits second) : first = second := by
  have hfirst := Lax253009Proofs.PCPFoundation.BinaryNat.toBits_fromBits first
  rw [hvalue, hlen] at hfirst
  rw [← hfirst, Lax253009Proofs.PCPFoundation.BinaryNat.toBits_fromBits second]

/-- Little-endian fixed-width bits, with the least significant bit first. -/
def Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE (width value : ℕ) : List Bool :=
  (Lax253009Proofs.PCPFoundation.BinaryNat.toBits width value).reverse

/-- Decode a little-endian bit list. -/
def Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE (bits : List Bool) : ℕ :=
  Lax253009Proofs.PCPFoundation.BinaryNat.fromBits bits.reverse

/-- Little-endian encoding has exactly the requested width. -/
@[simp] theorem Lax253009Proofs.PCPFoundation.BinaryNat.length_toBitsLE (width value : ℕ) :
    (Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE width value).length = width := by
  simp [Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE, Lax253009Proofs.PCPFoundation.BinaryNat.length_toBits]

/-- Little-endian decoding of a fixed-width encoding truncates modulo `2^width`. -/
theorem Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE_toBitsLE_mod (width value : ℕ) :
    Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE (Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE width value) = value % 2 ^ width := by
  simp [Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE, Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE, Lax253009Proofs.PCPFoundation.BinaryNat.fromBits_toBits_mod]

/-- Little-endian encoding exactly round-trips values that fit the width. -/
theorem Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE_toBitsLE {width value : ℕ} (hvalue : value < 2 ^ width) :
    Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE (Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE width value) = value := by
  rw [Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE_toBitsLE_mod, Nat.mod_eq_of_lt hvalue]

/-- Every little-endian list is recovered at its own fixed width. -/
theorem Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE_fromBitsLE (bits : List Bool) :
    Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE bits.length (Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE bits) = bits := by
  unfold Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE
  rw [show bits.length = bits.reverse.length by simp,
    Lax253009Proofs.PCPFoundation.BinaryNat.toBits_fromBits, List.reverse_reverse]

/-- A little-endian list decodes below `2` raised to its width. -/
theorem Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE_lt_pow_length (bits : List Bool) :
    Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE bits < 2 ^ bits.length := by
  unfold Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE
  simpa using Lax253009Proofs.PCPFoundation.BinaryNat.fromBits_lt_pow_length bits.reverse

/-- Little-endian decoding is injective at a fixed width. -/
theorem Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE_inj_of_length_eq {first second : List Bool}
    (hlen : first.length = second.length)
    (hvalue : Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE first = Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE second) : first = second := by
  have hfirst := Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE_fromBitsLE first
  rw [hvalue, hlen] at hfirst
  rw [← hfirst, Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE_fromBitsLE second]

private theorem Lax253009Proofs.PCPFoundation.BinaryNat.fromBits_append_singleton :
    ∀ (bits : List Bool) (bit : Bool),
      Lax253009Proofs.PCPFoundation.BinaryNat.fromBits (bits ++ [bit]) =
        2 * Lax253009Proofs.PCPFoundation.BinaryNat.fromBits bits + (if bit then 1 else 0)
  | [], bit => by cases bit <;> simp [Lax253009Proofs.PCPFoundation.BinaryNat.fromBits]
  | first :: rest, bit => by
      rw [List.cons_append, Lax253009Proofs.PCPFoundation.BinaryNat.fromBits,
        Lax253009Proofs.PCPFoundation.BinaryNat.fromBits_append_singleton rest bit]
      simp only [List.length_append, List.length_singleton, pow_succ]
      cases first <;> simp [Lax253009Proofs.PCPFoundation.BinaryNat.fromBits]
      omega

/-- Little-endian decoding exposes its least-significant head bit. -/
theorem Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE_cons (bit : Bool) (bits : List Bool) :
    Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE (bit :: bits) =
      (if bit then 1 else 0) + 2 * Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE bits := by
  simp only [Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE, List.reverse_cons]
  rw [Lax253009Proofs.PCPFoundation.BinaryNat.fromBits_append_singleton]
  omega

/-- Decoding the canonical variable-width little-endian bits recovers the
original natural number. -/
theorem Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE_bits : ∀ value : ℕ,
    Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE value.bits = value := by
  intro value
  induction value using Nat.binaryRec' with
  | zero => simp [Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE, Lax253009Proofs.PCPFoundation.BinaryNat.fromBits]
  | bit bit value hvalue ih =>
      rw [Nat.bits_append_bit value bit hvalue,
        Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE_cons, ih]
      cases bit <;> simp [Nat.bit]
      omega

/-- The minimal fixed-width little-endian encoding is exactly the canonical
variable-width bit list. -/
theorem Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE_size (value : ℕ) :
    Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE value.size value = value.bits := by
  calc
    Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE value.size value =
        Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE value.bits.length (Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE value.bits) := by
      congr 1
      · exact (Nat.size_eq_bits_len value).symm
      · exact (Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE_bits value).symm
    _ = value.bits := Lax253009Proofs.PCPFoundation.BinaryNat.toBitsLE_fromBitsLE value.bits

/-- Binary digit width is at most floor-log base two plus one. -/
theorem Lax253009Proofs.PCPFoundation.BinaryNat.size_le_log_two_add_one (value : ℕ) :
    value.size ≤ Nat.log 2 value + 1 := by
  rw [Nat.size_le]
  simpa only [Nat.succ_eq_add_one] using
    Nat.lt_pow_succ_log_self (b := 2) (by omega) value

/-- Every positive natural has binary digit width exactly floor-log base two
plus one. -/
theorem Lax253009Proofs.PCPFoundation.BinaryNat.size_eq_log_two_add_one {value : ℕ} (hvalue : value ≠ 0) :
    value.size = Nat.log 2 value + 1 := by
  apply le_antisymm (Lax253009Proofs.PCPFoundation.BinaryNat.size_le_log_two_add_one value)
  have hlower : Nat.log 2 value < value.size := by
    rw [Nat.lt_size]
    exact Nat.pow_log_le_self 2 hvalue
  omega

/-- Ceiling-logarithmic width sufficient to encode an element of `Fin size`. -/
def Lax253009Proofs.PCPFoundation.BinaryFin.bitWidth (size : ℕ) : ℕ :=
  Nat.clog 2 size

/-- Encode a finite index using the canonical ceiling-logarithmic width. -/
def Lax253009Proofs.PCPFoundation.BinaryFin.toBits {size : ℕ} (index : Fin size) : List Bool :=
  Lax253009Proofs.PCPFoundation.BinaryNat.toBits (Lax253009Proofs.PCPFoundation.BinaryFin.bitWidth size) index

/-- Decode an exactly sized finite-index encoding, rejecting out-of-range
values. -/
def Lax253009Proofs.PCPFoundation.BinaryFin.fromBits? (size : ℕ) (bits : List Bool) : Option (Fin size) :=
  if _hlength : bits.length = Lax253009Proofs.PCPFoundation.BinaryFin.bitWidth size then
    if hvalue : Lax253009Proofs.PCPFoundation.BinaryNat.fromBits bits < size then
      some ⟨Lax253009Proofs.PCPFoundation.BinaryNat.fromBits bits, hvalue⟩
    else
      none
  else
    none

/-- Finite-index encoding has exactly the canonical ceiling-logarithmic
width. -/
@[simp] theorem Lax253009Proofs.PCPFoundation.BinaryFin.length_toBits {size : ℕ} (index : Fin size) :
    (Lax253009Proofs.PCPFoundation.BinaryFin.toBits index).length = Lax253009Proofs.PCPFoundation.BinaryFin.bitWidth size := by
  simp [Lax253009Proofs.PCPFoundation.BinaryFin.toBits, Lax253009Proofs.PCPFoundation.BinaryFin.bitWidth, Lax253009Proofs.PCPFoundation.BinaryNat.length_toBits]

/-- Canonical finite-index encoding round-trips exactly. -/
@[simp] theorem Lax253009Proofs.PCPFoundation.BinaryFin.fromBits?_toBits {size : ℕ} (index : Fin size) :
    Lax253009Proofs.PCPFoundation.BinaryFin.fromBits? size (Lax253009Proofs.PCPFoundation.BinaryFin.toBits index) = some index := by
  have hfits : index.val < 2 ^ Lax253009Proofs.PCPFoundation.BinaryFin.bitWidth size :=
    lt_of_lt_of_le index.isLt
      (Nat.le_pow_clog Nat.one_lt_two size)
  unfold Lax253009Proofs.PCPFoundation.BinaryFin.fromBits?
  rw [Lax253009Proofs.PCPFoundation.BinaryFin.length_toBits, dif_pos rfl]
  simp only [Lax253009Proofs.PCPFoundation.BinaryFin.toBits]
  simp [Lax253009Proofs.PCPFoundation.BinaryNat.fromBits_toBits hfits, index.isLt]

/-- Successful finite-index decoding recovers the exact fixed-width input. -/
theorem Lax253009Proofs.PCPFoundation.BinaryFin.toBits_eq_of_fromBits?_eq_some
    {size : ℕ} {bits : List Bool} {index : Fin size}
    (hdecode : Lax253009Proofs.PCPFoundation.BinaryFin.fromBits? size bits = some index) :
    (Lax253009Proofs.PCPFoundation.BinaryFin.toBits index) = bits := by
  unfold Lax253009Proofs.PCPFoundation.BinaryFin.fromBits? at hdecode
  split at hdecode
  · rename_i hlength
    split at hdecode
    · cases hdecode
      simp only [Lax253009Proofs.PCPFoundation.BinaryFin.toBits]
      rw [← hlength]
      exact Lax253009Proofs.PCPFoundation.BinaryNat.toBits_fromBits bits
    · simp at hdecode
  · simp at hdecode

/-- Finite-index decoding fails exactly on a malformed width or an
out-of-range decoded value. -/
theorem Lax253009Proofs.PCPFoundation.BinaryFin.fromBits?_eq_none_iff (size : ℕ) (bits : List Bool) :
    Lax253009Proofs.PCPFoundation.BinaryFin.fromBits? size bits = none ↔
      bits.length ≠ Lax253009Proofs.PCPFoundation.BinaryFin.bitWidth size ∨ size ≤ Lax253009Proofs.PCPFoundation.BinaryNat.fromBits bits := by
  by_cases hlength : bits.length = Lax253009Proofs.PCPFoundation.BinaryFin.bitWidth size
  · simp [Lax253009Proofs.PCPFoundation.BinaryFin.fromBits?, hlength]
  · simp [Lax253009Proofs.PCPFoundation.BinaryFin.fromBits?, hlength]
