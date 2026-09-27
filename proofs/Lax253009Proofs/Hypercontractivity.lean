import Lax253009.Hypercontractivity
import Lax253009Proofs.FourierIdentities
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Expect

namespace Lax253009Proofs

open Lax253009.BooleanFourier
open scoped BigOperators symmDiff

private noncomputable def poly {ι : Type} (u : Finset ι)
    (c : Finset ι → ℝ) (x : Cube ι) : ℝ :=
  ∑ S ∈ u.powerset, c S * character S x

private noncomputable def energy {ι : Type} (u : Finset ι) (c : Finset ι → ℝ) : ℝ :=
  ∑ S ∈ u.powerset, (3 : ℝ) ^ S.card * c S ^ 2

private theorem energy_nonneg {ι : Type} (u : Finset ι) (c : Finset ι → ℝ) :
    0 ≤ energy u c := Finset.sum_nonneg fun S _ ↦ by positivity

private theorem poly_insert {ι : Type} [DecidableEq ι] (u : Finset ι)
    (i : ι) (hi : i ∉ u) (c : Finset ι → ℝ) (x : Cube ι) :
    poly (insert i u) c x = poly u c x + sign (x i) * poly u (fun S ↦ c (insert i S)) x := by
  unfold poly
  rw [Finset.sum_powerset_insert hi, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  have hSi : i ∉ S := fun h ↦ hi (Finset.mem_powerset.mp hS h)
  rw [character, Finset.prod_insert hSi]
  unfold character
  ring

private theorem energy_insert {ι : Type} [DecidableEq ι] (u : Finset ι)
    (i : ι) (hi : i ∉ u) (c : Finset ι → ℝ) :
    energy (insert i u) c = energy u c + 3 * energy u (fun S ↦ c (insert i S)) := by
  unfold energy
  rw [Finset.sum_powerset_insert hi, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  have hSi : i ∉ S := fun h ↦ hi (Finset.mem_powerset.mp hS h)
  rw [Finset.card_insert_of_notMem hSi, pow_succ]
  ring

private def toggle {ι : Type} [DecidableEq ι] (i : ι) (x : Cube ι) : Cube ι :=
  fun j ↦ if j = i then !(x j) else x j

private theorem toggle_involutive {ι : Type} [DecidableEq ι] (i : ι) :
    Function.Involutive (toggle i) := by
  intro x
  funext j
  by_cases h : j = i <;> simp [toggle, h]

private theorem poly_toggle {ι : Type} [DecidableEq ι] (u : Finset ι)
    (i : ι) (hi : i ∉ u) (c : Finset ι → ℝ) (x : Cube ι) :
    poly u c (toggle i x) = poly u c x := by
  apply Finset.sum_congr rfl
  intro S hS
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := by rintro rfl; exact hi (Finset.mem_powerset.mp hS hj)
  simp [toggle, hji]

private theorem fourth_moment_split {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : Finset ι) (i : ι) (hi : i ∉ u) (c : Finset ι → ℝ) :
    (𝔼 x : Cube ι, poly (insert i u) c x ^ 4) =
      (𝔼 x : Cube ι, poly u c x ^ 4) +
      6 * (𝔼 x : Cube ι, poly u c x ^ 2 * poly u (fun S ↦ c (insert i S)) x ^ 2) +
      (𝔼 x : Cube ι, poly u (fun S ↦ c (insert i S)) x ^ 4) := by
  classical
  let A := poly u c
  let B := poly u (fun S ↦ c (insert i S))
  let P := poly (insert i u) c
  have hp (x : Cube ι) : (P x ^ 4 + P (toggle i x) ^ 4) / 2 =
      A x ^ 4 + 6 * (A x ^ 2 * B x ^ 2) + B x ^ 4 := by
    dsimp [P, A, B]
    rw [poly_insert u i hi, poly_insert u i hi, poly_toggle u i hi, poly_toggle u i hi]
    cases hx : x i <;> simp [toggle, sign, hx] <;> ring
  have havg : (𝔼 x : Cube ι, P (toggle i x) ^ 4) = (𝔼 x : Cube ι, P x ^ 4) :=
    Fintype.expect_equiv ((toggle_involutive i).toPerm _) _ _ (fun _ ↦ rfl)
  calc
    _ = ((𝔼 x : Cube ι, P x ^ 4) + (𝔼 x : Cube ι, P (toggle i x) ^ 4)) / 2 := by
      rw [havg]
      change (𝔼 x, P x ^ 4) = _
      ring
    _ = 𝔼 x : Cube ι, (P x ^ 4 + P (toggle i x) ^ 4) / 2 := by
      rw [← Finset.expect_div, Finset.expect_add_distrib]
    _ = 𝔼 x : Cube ι, (A x ^ 4 + 6 * (A x ^ 2 * B x ^ 2) + B x ^ 4) := by
      exact Finset.expect_congr rfl fun x _ ↦ hp x
    _ = _ := by simp only [Finset.expect_add_distrib, ← Finset.mul_expect]; rfl

private theorem polynomial_fourth_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : Finset ι) (c : Finset ι → ℝ) :
    (𝔼 x : Cube ι, poly u c x ^ 4) ≤ energy u c ^ 2 := by
  classical
  induction u using Finset.induction_on generalizing c with
  | empty => simp [poly, energy, character, ← pow_mul]
  | @insert i u hi ih =>
    let d := fun S ↦ c (insert i S)
    have hA := ih c
    have hB := ih d
    have hA0 : 0 ≤ energy u c := energy_nonneg u c
    have hB0 : 0 ≤ energy u d := energy_nonneg u d
    have hE0 : 0 ≤ (𝔼 x : Cube ι, poly u d x ^ 4) :=
      Finset.expect_nonneg fun x _ ↦ by positivity
    have hCS := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
      (fun x : Cube ι ↦ poly u c x ^ 2) (fun x : Cube ι ↦ poly u d x ^ 2)
    simp only [← pow_mul, Nat.reduceMul] at hCS
    have hprod := mul_le_mul hA hB hE0 (sq_nonneg (energy u c))
    have hcross : (𝔼 x : Cube ι, poly u c x ^ 2 * poly u d x ^ 2) ≤
        energy u c * energy u d := by
      have hc0 : 0 ≤ (𝔼 x : Cube ι, poly u c x ^ 2 * poly u d x ^ 2) :=
        Finset.expect_nonneg fun x _ ↦ by positivity
      have he0 := mul_nonneg hA0 hB0
      nlinarith
    rw [fourth_moment_split u i hi c, energy_insert u i hi c]
    change _ ≤ (energy u c + 3 * energy u d) ^ 2
    nlinarith [sq_nonneg (energy u d)]

/--
---
conclusion: Lax253009.Hypercontractivity.fourth_moment
---
Coordinate induction bounds the fourth moment by the squared Fourier energy
weighted by 3^|S|. Low degree bounds every surviving weight by 3^l.
-/
theorem low_degree_fourth_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (l : ℕ) (hdegree : ∀ S, l < S.card → c S = 0) :
    (𝔼 x : Cube ι, (∑ S, c S * character S x) ^ 4) ≤
      ((3 : ℝ) ^ l * ∑ S, c S ^ 2) ^ 2 := by
  classical
  have hp := polynomial_fourth_moment Finset.univ c
  have hw : energy Finset.univ c ≤ (3 : ℝ) ^ l * ∑ S, c S ^ 2 := by
    simp only [energy, Finset.powerset_univ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro S _
    by_cases hs : S.card ≤ l
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hs) (sq_nonneg _)
    · simp [hdegree S (Nat.lt_of_not_ge hs)]
  apply le_trans (by simpa [poly] using hp)
  exact pow_le_pow_left₀ (energy_nonneg _ _) hw 2

theorem fourier_average_expect {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) : average F = (𝔼 x, F x) := by
  rw [Fintype.expect_eq_sum_div_card]
  simp [average, Cube]

/--
---
conclusion: Lax253009.Hypercontractivity.fourier_fourth_moment
---
Apply the polynomial estimate to the Fourier expansion and use Parseval.
-/
theorem fourier_low_degree_fourth_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (l : ℕ) (hdegree : ∀ S, l < S.card → coefficient F S = 0) :
    (𝔼 x, F x ^ 4) ≤ ((3 : ℝ) ^ l * (𝔼 x, F x ^ 2)) ^ 2 := by
  have h := Lax253009.Hypercontractivity.fourth_moment (coefficient F) l hdegree
  simp_rw [← Lax253009.BooleanFourier.inversion, Lax253009.BooleanFourier.parseval, fourier_average_expect] at h
  exact h

theorem fourier_product_coefficient {ι : Type} [Fintype ι] [DecidableEq ι]
    (F G : Cube ι → ℝ) (U : Finset ι) :
    coefficient (fun x ↦ F x * G x) U =
      ∑ S, coefficient F S * coefficient G (S ∆ U) := by
  classical
  change average (fun x ↦ F x * G x * character U x) = _
  conv_lhs => enter [1, x]; rw [Lax253009.BooleanFourier.inversion F]
  simp only [Finset.sum_mul]
  rw [average_sum]
  apply Finset.sum_congr rfl
  intro S _
  have he (x : Cube ι) : coefficient F S * character S x * G x * character U x =
      coefficient F S * (G x * character (S ∆ U) x) := by rw [← character_mul]; ring
  simp_rw [he, average_mul]
  rfl

/--
---
conclusion: Lax253009.Hypercontractivity.product_degree
---
Fourier coefficients of a product are convolutions over symmetric difference.
A surviving support has cardinality at most the sum of the two degrees.
-/
theorem fourier_product_degree {ι : Type} [Fintype ι] [DecidableEq ι]
    (F G : Cube ι → ℝ) (l k : ℕ)
    (hF : ∀ S, l < S.card → coefficient F S = 0)
    (hG : ∀ S, k < S.card → coefficient G S = 0) :
    ∀ S, l + k < S.card → coefficient (fun x ↦ F x * G x) S = 0 := by
  classical
  intro U hU
  rw [fourier_product_coefficient]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hS : l < S.card
  · rw [hF S hS, zero_mul]
  · have hcard : U.card ≤ S.card + (S ∆ U).card := by
      apply le_trans (Finset.card_le_card (show U ⊆ S ∪ (S ∆ U) from ?_))
        (Finset.card_union_le _ _)
      intro i hi
      simp only [Finset.mem_union, Finset.mem_symmDiff]
      tauto
    rw [hG (S ∆ U) (by omega), mul_zero]

theorem fourier_power_degree {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (l : ℕ) (hF : ∀ S, l < S.card → coefficient F S = 0) (k : ℕ) :
    ∀ S, l * k < S.card → coefficient (fun x ↦ F x ^ k) S = 0 := by
  induction k with
  | zero =>
    intro S hS
    have hne : S ≠ ∅ := by intro he; simp [he] at hS
    simpa [coefficient, character, eq_comm, hne] using Lax253009.BooleanFourier.orthogonality ∅ S
  | succ k ih =>
    simpa only [pow_succ, Nat.mul_succ] using
      Lax253009.Hypercontractivity.product_degree (fun x ↦ F x ^ k) F (l * k) l ih hF

/--
---
conclusion: Lax253009.Hypercontractivity.dyadic_moment
---
Iterate the fourth-moment inequality on powers of F. The degree bound grows
with the power; all resulting constants remain independent of dimension.
-/
theorem fourier_dyadic_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (l k : ℕ) (hdegree : ∀ S, l < S.card → coefficient F S = 0) :
    (𝔼 x, F x ^ (2 ^ (k + 1))) ≤
      (3 : ℝ) ^ (l * k * 2 ^ k) * (𝔼 x, F x ^ 2) ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := Lax253009.Hypercontractivity.fourier_fourth_moment (fun x ↦ F x ^ (2 ^ k)) (l * 2 ^ k)
      (fourier_power_degree F l hdegree (2 ^ k))
    have h4 : 2 ^ k * 4 = 2 ^ (k + 1 + 1) := by ring
    have h2 : 2 ^ k * 2 = 2 ^ (k + 1) := by ring
    simp only [← pow_mul, h4, h2] at h
    have hnonneg : 0 ≤ (𝔼 x, F x ^ (2 ^ (k + 1))) := by
      apply Finset.expect_nonneg
      intro x _
      rw [← h2, pow_mul]
      positivity
    apply h.trans
    calc
      _ ≤ ((3 : ℝ) ^ (l * 2 ^ k) *
          ((3 : ℝ) ^ (l * k * 2 ^ k) * (𝔼 x, F x ^ 2) ^ (2 ^ k))) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (by positivity) hnonneg)
          (mul_le_mul_of_nonneg_left ih (by positivity)) 2
      _ = _ := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← mul_assoc, ← pow_add]
        congr 1
        congr 1
        ring

/--
---
conclusion: Lax253009.Hypercontractivity.bounded_moment
---
Compare an arbitrary power with one plus a larger even power, then apply
dyadic hypercontractivity and the supplied second-moment bound.
-/
theorem fourier_bounded_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (l m : ℕ) (V : ℝ)
    (hdegree : ∀ S, l < S.card → coefficient F S = 0)
    (hvariance : (𝔼 x, F x ^ 2) ≤ V) :
    (𝔼 x, F x ^ m) ≤ 1 + (3 : ℝ) ^ (l * m * 2 ^ m) * V ^ (2 ^ m) := by
  have hq : m ≤ 2 ^ (m + 1) := by have h := (m + 1).lt_two_pow_self; omega
  have habs (x : ℝ) : |x| ^ (2 ^ (m + 1)) = x ^ (2 ^ (m + 1)) := by
    rw [pow_succ, pow_mul, pow_mul, ← abs_pow, sq_abs]
  have hpoint (x : ℝ) : x ^ m ≤ 1 + x ^ (2 ^ (m + 1)) := by
    calc
      x ^ m ≤ |x| ^ m := (le_abs_self _).trans_eq (abs_pow _ _)
      _ ≤ 1 + |x| ^ (2 ^ (m + 1)) := by
        by_cases hx : |x| ≤ 1
        · have h : |x| ^ m ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
          linarith [pow_nonneg (abs_nonneg x) (2 ^ (m + 1))]
        · have h := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hx)) hq
          linarith
      _ = _ := by rw [habs]
  have hE0 : 0 ≤ (𝔼 x, F x ^ 2) := Finset.expect_nonneg fun _ _ ↦ sq_nonneg _
  calc
    _ ≤ 𝔼 x, (1 + F x ^ (2 ^ (m + 1))) := Finset.expect_le_expect fun x _ ↦ hpoint _
    _ = 1 + (𝔼 x, F x ^ (2 ^ (m + 1))) := by
      rw [Finset.expect_add_distrib, Fintype.expect_const]
    _ ≤ 1 + (3 : ℝ) ^ (l * m * 2 ^ m) * (𝔼 x, F x ^ 2) ^ (2 ^ m) :=
      add_le_add (le_refl 1) (Lax253009.Hypercontractivity.dyadic_moment F l m hdegree)
    _ ≤ _ := add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hE0 hvariance (2 ^ m))
      (show 0 ≤ (3 : ℝ) ^ (l * m * 2 ^ m) by positivity))

theorem average_finset_sum {ι α : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset α) (F : α → Cube ι → ℝ) :
    average (fun x ↦ ∑ a ∈ s, F a x) = ∑ a ∈ s, average (F a) := by
  classical
  simp only [average, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem fourier_sum_degree {ι α : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset α) (F : α → Cube ι → ℝ) (l : ℕ)
    (h : ∀ a ∈ s, ∀ S, l < S.card → coefficient (F a) S = 0) :
    ∀ S, l < S.card → coefficient (fun x ↦ ∑ a ∈ s, F a x) S = 0 := by
  intro S hS
  simp only [coefficient, Finset.sum_mul]
  rw [average_finset_sum]
  exact Finset.sum_eq_zero fun a ha ↦ h a ha S hS

theorem fourier_character_degree {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (l : ℕ) (hcard : S.card ≤ l) :
    ∀ U, l < U.card → coefficient (character S) U = 0 := by
  intro U hU
  have hne : S ≠ U := by rintro rfl; omega
  exact (Lax253009.BooleanFourier.orthogonality S U).trans (if_neg hne)

theorem fourier_const_degree {ι : Type} [Fintype ι] [DecidableEq ι] (c : ℝ) :
    ∀ S : Finset ι, 0 < S.card → coefficient (fun _ ↦ c) S = 0 := by
  intro S hS
  have h := fourier_character_degree (∅ : Finset ι) 0 (by simp) S hS
  have hc : coefficient (fun _ : Cube ι ↦ c) S =
      c * coefficient (character ∅) S := by
    simp only [coefficient, character, Finset.prod_empty, one_mul]
    exact average_mul c _
  rw [hc, h, mul_zero]

theorem fourier_finset_product_degree {ι α : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset α) (F : α → Cube ι → ℝ) (d : α → ℕ)
    (h : ∀ a ∈ s, ∀ S, d a < S.card → coefficient (F a) S = 0) :
    ∀ S, (∑ a ∈ s, d a) < S.card → coefficient (fun x ↦ ∏ a ∈ s, F a x) S = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using fourier_const_degree (ι := ι) 1
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, Finset.prod_insert ha]
    exact Lax253009.Hypercontractivity.product_degree (F a) (fun x ↦ ∏ b ∈ s, F b x) (d a) (∑ b ∈ s, d b)
      (h a (Finset.mem_insert_self _ _)) (ih (fun b hb ↦ h b (Finset.mem_insert_of_mem hb)))

end Lax253009Proofs
