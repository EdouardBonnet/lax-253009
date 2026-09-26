import Lax253009.DoubleCoverBounds
import Lax253009Proofs.Hypercontractivity
import Lax253009Proofs.HigherMoments

namespace Lax253009Proofs

open Lax253009.BooleanFourier Lax253009.HigherMoments Lax253009.DoubleCoverBounds
open Lax253009.ProductMoments
open scoped BigOperators

private def colored (z : Bool × Bool) : ℝ :=
  sign z.1 + sign z.2 + sign z.1 * sign z.2

private theorem colored_moment (n : ℕ) :
    (𝔼 z : Bool × Bool, colored z ^ n) = ((3 : ℝ) ^ n + 3 * (-1 : ℝ) ^ n) / 4 := by
  rw [Fintype.expect_eq_sum_div_card]
  norm_num [Fintype.sum_prod_type, colored, sign]
  ring

private theorem colored_mean : (𝔼 z, colored z) = 0 := by
  simpa using colored_moment 1

private theorem colored_second : (𝔼 z, colored z ^ 2) = 3 := by
  norm_num [colored_moment]

private theorem colored_moment_ge_one (n : ℕ) (hn : 2 ≤ n) :
    1 ≤ (𝔼 z, colored z ^ n) := by
  rw [colored_moment]
  have h3 : (9 : ℝ) ≤ 3 ^ n := by
    calc
      (9 : ℝ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h1 : (-1 : ℝ) ≤ (-1 : ℝ) ^ n := (abs_le.mp (by simp : |(-1 : ℝ) ^ n| ≤ 1)).1
  linarith

private theorem colored_moment_nonneg (n : ℕ) : 0 ≤ (𝔼 z, colored z ^ n) := by
  rcases n with _ | (_ | n)
  · norm_num [colored_moment]
  · simpa using colored_mean.ge
  · exact (by norm_num : (0 : ℝ) ≤ 1).trans (colored_moment_ge_one _ (by omega))

private noncomputable def coloredPoly {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (f : ι → Bool × Bool) : ℝ :=
  ∑ S, c S * ∏ i ∈ S, colored (f i)

private def pairedEquiv (ι : Type) : Cube (ι × Bool) ≃ (ι → Bool × Bool) where
  toFun x i := (x (i, false), x (i, true))
  invFun f p := if p.2 then (f p.1).2 else (f p.1).1
  left_inv x := by funext ⟨i, b⟩; cases b <;> rfl
  right_inv f := by funext i; rfl

private noncomputable def lifted {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (x : Cube (ι × Bool)) : ℝ := coloredPoly c (pairedEquiv ι x)

private theorem lifted_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (m : ℕ) :
    (𝔼 x, lifted c x ^ m) = (𝔼 f, coloredPoly c f ^ m) :=
  Fintype.expect_equiv (pairedEquiv ι) _ _ (fun _ ↦ rfl)

private theorem colored_coordinate_degree {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) :
    ∀ S, 2 < S.card → coefficient (fun x : Cube (ι × Bool) ↦ colored (pairedEquiv ι x i)) S = 0 := by
  intro S hS
  have h1 := fourier_character_degree {(i, false)} 2 (by simp) S hS
  have h2 := fourier_character_degree {(i, true)} 2 (by simp) S hS
  have h3 := fourier_character_degree {(i, false), (i, true)} 2 (by simp) S hS
  have he (x : Cube (ι × Bool)) : colored (pairedEquiv ι x i) =
      character {(i, false)} x + character {(i, true)} x + character {(i, false), (i, true)} x := by
    simp [colored, pairedEquiv, character]
  simp only [coefficient, he, add_mul, average, Finset.sum_add_distrib, add_div] at *
  linarith

private theorem lifted_degree {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (l : ℕ) (hdegree : ∀ S, l < S.card → c S = 0) :
    ∀ U, 2 * l < U.card → coefficient (lifted c) U = 0 := by
  apply fourier_sum_degree Finset.univ _ (2 * l)
  intro S _ U hU
  by_cases hS : l < S.card
  · simp only [hdegree S hS, zero_mul, coefficient, average, Finset.sum_const_zero, zero_div]
  · have hp := fourier_finset_product_degree S
      (fun i x ↦ colored (pairedEquiv ι x i)) (fun _ ↦ 2)
      (fun i _ ↦ colored_coordinate_degree i) U
    simp only [Finset.sum_const, smul_eq_mul] at hp
    have hcard : S.card * 2 < U.card := by omega
    have hz := hp hcard
    change average (fun x ↦ (c S * ∏ i ∈ S, colored (pairedEquiv ι x i)) * character U x) = 0
    simp only [mul_assoc, average_mul]
    exact mul_eq_zero_of_right _ hz

private theorem colored_energy {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) :
    (𝔼 f, coloredPoly c f ^ 2) = ∑ S, c S ^ 2 * (3 : ℝ) ^ S.card := by
  classical
  have h := balanced_second_moment (ι := ι) Finset.univ c {colored}
    (by intro B hB; simpa using (Finset.mem_singleton.mp hB ▸ colored_mean))
  simpa only [weightedSum, Finset.sum_singleton, coloredPoly, ← pow_two, colored_second] using h

private theorem lifted_variance_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (l : ℕ) (hdegree : ∀ S, l < S.card → c S = 0)
    (henergy : ∑ S, c S ^ 2 ≤ 1) : (𝔼 x, lifted c x ^ 2) ≤ (3 : ℝ) ^ l := by
  rw [lifted_moment, colored_energy]
  calc
    _ ≤ ∑ S, c S ^ 2 * (3 : ℝ) ^ l := by
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : S.card ≤ l
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hS) (sq_nonneg _)
      · simp [hdegree S (by omega)]
    _ = (∑ S, c S ^ 2) * (3 : ℝ) ^ l := (Finset.sum_mul ..).symm
    _ ≤ 1 * (3 : ℝ) ^ l := mul_le_mul_of_nonneg_right henergy (by positivity)
    _ = _ := one_mul _

private theorem colored_moment_expansion {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (m : ℕ) :
    (𝔼 f, coloredPoly c f ^ m) =
      ∑ S : Fin m → Finset ι, (∏ j, c (S j)) *
        ∏ i, (𝔼 z, colored z ^ (Finset.univ.filter fun j ↦ i ∈ S j).card) := by
  classical
  unfold coloredPoly
  simp_rw [Fintype.sum_pow, Finset.prod_mul_distrib, Finset.expect_sum_comm, ← Finset.mul_expect]
  apply Finset.sum_congr rfl
  intro S _
  rw [higher_moment_factorization S (fun _ ↦ colored)]
  simp only [Finset.prod_const]

private theorem double_cover_le_colored_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (m : ℕ) (hc : ∀ S, 0 ≤ c S) :
    weight c m ≤ (𝔼 f, coloredPoly c f ^ m) := by
  classical
  rw [colored_moment_expansion]
  unfold weight
  apply Finset.sum_le_sum
  intro S _
  have hcprod : 0 ≤ ∏ j, c (S j) := Finset.prod_nonneg fun j _ ↦ hc _
  have hmprod : 0 ≤ ∏ i, (𝔼 z, colored z ^ (Finset.univ.filter fun j ↦ i ∈ S j).card) :=
    Finset.prod_nonneg fun i _ ↦ colored_moment_nonneg _
  split_ifs with hS
  · have hi (i : ι) : 1 ≤ (𝔼 z, colored z ^ (Finset.univ.filter fun j ↦ i ∈ S j).card) := by
      by_cases hmem : i ∈ Finset.univ.biUnion S
      · exact colored_moment_ge_one _ (hS i hmem)
      · have hz : (Finset.univ.filter fun j ↦ i ∈ S j) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro j hj
          exact hmem (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩)
        simp [hz]
    have hprod : 1 ≤ ∏ i, (𝔼 z, colored z ^ (Finset.univ.filter fun j ↦ i ∈ S j).card) :=
      Finset.one_le_prod fun i _ ↦ hi i
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod hcprod
  · exact mul_nonneg hcprod hmprod

/--
---
conclusion: Lax253009.DoubleCoverBounds.bound
---
The centered two-bit variable has all double-cover moments at least one.
Its lifted polynomial has degree at most 2l and second moment at most 3^l.
Apply the dimension-independent bounded-moment estimate.
-/
theorem double_cover_weight_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (l m : ℕ) (hc : ∀ S, 0 ≤ c S)
    (hdegree : ∀ S, l < S.card → c S = 0) (henergy : ∑ S, c S ^ 2 ≤ 1) :
    weight c m ≤ 1 + (3 : ℝ) ^ (l * (2 * m + 1) * 2 ^ m) := by
  calc
    _ ≤ (𝔼 f, coloredPoly c f ^ m) := double_cover_le_colored_moment c m hc
    _ = (𝔼 x, lifted c x ^ m) := (lifted_moment c m).symm
    _ ≤ 1 + (3 : ℝ) ^ (2 * l * m * 2 ^ m) * ((3 : ℝ) ^ l) ^ (2 ^ m) :=
      fourier_bounded_moment (lifted c) (2 * l) m ((3 : ℝ) ^ l)
        (lifted_degree c l hdegree) (lifted_variance_bound c l hdegree henergy)
    _ = _ := by
      rw [← pow_mul, ← pow_add]
      congr 2
      ring

end Lax253009Proofs
