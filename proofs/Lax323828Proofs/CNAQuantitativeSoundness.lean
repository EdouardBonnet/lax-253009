import Lax323828.CNAQuantitativeSoundness
import Lax323828Proofs.CNAPointSoundness
import Lax323828Proofs.RandomFibers
import Lax323828Proofs.LongCode
import Lax323828Proofs.SideConditionAveraging

namespace Lax323828Proofs

open Lax323828.FiniteProbability Lax323828.RandomFibers
open Lax323828.BooleanFourier Lax323828.LongCode Lax323828.CNASoundness
open Lax323828.CNAPointSoundness Lax323828.CNAQuantitativeSoundness
open Lax323828.FourierProjection Lax323828.SideConditionAveraging
open scoped BigOperators Classical

theorem random_fiber_counting {ι κ : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (Bad : (ι → κ) → Prop) (G : (ι → κ) → ι → Prop) (p : ℝ)
    (hfiber : ∀ f, Bad f → ∃ z, ∀ y, f y = z → G f y)
    (hpoint : ∀ y, probability (fun f ↦ G f y) ≤ p) :
    probability Bad ≤ (Fintype.card κ : ℝ) *
      Real.exp (-(Fintype.card ι : ℝ) / (8 * (Fintype.card κ : ℝ) ^ 2)) +
      2 * Fintype.card κ * p := by
  let small := fun f : ι → κ ↦ ∃ z,
    (fiber f z).card < (Fintype.card ι : ℝ) / (2 * Fintype.card κ)
  let T := (Fintype.card ι : ℝ) / (2 * Fintype.card κ)
  have hI : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hK : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hT : 0 < T := by positivity
  have hcount (f : ι → κ) (hf : Bad f ∧ ¬ small f) :
      T ≤ (Finset.univ.filter (G f)).card := by
    obtain ⟨z, hz⟩ := hfiber f hf.1
    have hc : (fiber f z).card ≤ (Finset.univ.filter (G f)).card :=
      Finset.card_le_card fun y hy ↦ Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hz y (Finset.mem_filter.mp hy).2⟩
    exact (le_of_not_gt (fun hh ↦ hf.2 ⟨z, hh⟩)).trans (by exact_mod_cast hc)
  have hgood : probability (fun f ↦ Bad f ∧ ¬ small f) ≤ 2 * Fintype.card κ * p := by
    calc
      _ ≤ (∑ y, probability (fun f : ι → κ ↦ y ∈ Finset.univ.filter (G f))) / T :=
        finite_probability_counting _ _ T hT hcount
      _ = (∑ y, probability (fun f : ι → κ ↦ G f y)) / T := by simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      _ ≤ (∑ _y : ι, p) / T := div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun y _ ↦ hpoint y) hT.le
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, T]; field_simp
  calc
    _ ≤ probability (fun f ↦ small f ∨ (Bad f ∧ ¬ small f)) := by
      apply Lax323828.FiniteProbability.monotone
      intro f hf
      by_cases hs : small f
      · exact Or.inl hs
      · exact Or.inr ⟨hf, hs⟩
    _ ≤ probability small + probability (fun f ↦ Bad f ∧ ¬ small f) := Lax323828.FiniteProbability.union_bound _ _
    _ ≤ _ := add_le_add (Lax323828.RandomFibers.any_small_fiber Fintype.card_pos) hgood

private theorem looks_like_same_label {w s : ℕ} (A : Table w)
    (f : Word w → Word s) (x y : Word w)
    (hx : LooksLike A (fun i v ↦ f v i) x) (hy : f y = f x) :
    LooksLike A (fun i v ↦ f v i) y := by
  refine ⟨fun i ↦ (hx.1 i).trans ((congrFun hy i).symm), fun B ↦ ?_⟩
  change A (fun v ↦ B (f v)) = B (f y)
  rw [hy]
  exact hx.2 B

/--
---
conclusion: Lax323828.CNAQuantitativeSoundness.quantitative_soundness
---
Transpose the random query matrix into independent labels. Project onto
the satisfying words, preserving accepted answers and shrinking the decoding
set into the original decoding set intersected with those words. Every bad
accepting run then supplies a whole fiber of bad evaluation points.
-/
theorem cna_quantitative_soundness (w s l m r : ℕ) (hs : 0 < s)
    (hl : 0 < l) (hlN : l < 2 ^ s)
    (τ q : ℝ) (hτ : 0 < τ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hr : 2 * r ≤ m) (hm : Even m)
    (hlarge : (l : ℝ) / ((2 : ℝ) ^ s - l) / τ ≤ 1 / 3)
    (A : Table w) (h : Coordinate w) :
    probability (BadWithCondition (s := s) A (decoding (fun g ↦ sign (A g)) l τ) h) ≤
      totalBound l m r s w τ q := by
  let F₀ : Cube (Word w) → ℝ := fun g ↦ sign (A g)
  let F := project F₀ (satisfying h)
  let D := decoding F₀ l τ
  let E : (Fin s → Coordinate w) ≃ (Word w → Word s) := Equiv.piComm (fun _ _ ↦ Bool)
  let Bad := fun f : Word w → Word s ↦ BadWithCondition A D h (E.symm f)
  let n := 2 ^ (s - 1)
  have hn : 0 < n := by positivity
  have hcard (a : ℕ) : Fintype.card (Word a) = 2 ^ a := by simp [Word]
  have hN : Fintype.card (Word s) = 2 * n := by
    rw [hcard, show s = (s - 1) + 1 by omega, pow_succ]
    exact Nat.mul_comm _ _
  have hF₀ (g : Cube (Word w)) : |F₀ g| ≤ 1 := by
    dsimp only [F₀]
    cases A g <;> norm_num [sign]
  have hF (g : Cube (Word w)) : |F g| ≤ 1 := Lax323828.FourierProjection.bounded_project F₀ hF₀ _ g
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hD : decoding F l τ ⊆ D ∩ satisfying h :=
    Lax323828.FourierDecoding.projected_decoding_subset F₀ _ l (τ ^ 2 / l) (div_pos (sq_pos_of_pos hτ) hlr)
  let G := fun (f : Word w → Word s) (y : Word w) ↦
    Matches F n f y ∧ Avoids (decoding F l τ) f y
  have hfiber (f : Word w → Word s) (hf : Bad f) :
      ∃ z, ∀ y, f y = z → G f y := by
    obtain ⟨x, hx⟩ := Lax323828.LongCodeCorrectness.local_decoding A (E.symm f) hf.1.1
    refine ⟨f x, fun y hy ↦ ?_⟩
    have hylook := looks_like_same_label A f x y hx hy
    refine ⟨fun B ↦ ?_, fun x' hx' heq ↦ ?_⟩
    · have hp := Lax323828.SideConditionAveraging.query_preserved A (E.symm f) h hf.1
        (compose (E.symm f) B.val) (Or.inr ⟨B.val, rfl⟩)
      exact hp.trans (congrArg sign (hylook.2 B.val))
    · obtain ⟨hxD, hxU⟩ := Finset.mem_inter.mp (hD hx')
      exact hf.2 ⟨x', hxD, (Finset.mem_filter.mp hxU).2,
        looks_like_same_label A f y x' hylook heq⟩
  have hpoint (y : Word w) : probability (fun f : Word w → Word s ↦ G f y) ≤
      pointBound l m r (2 ^ s) τ q := by
    have he := Lax323828.CNAPointSoundness.point_soundness F hF n hn hN l m r hl
      (by simpa only [hcard] using hlN) τ q hτ hq hq1 hr hm
      (by simpa only [hcard, Nat.cast_pow, Nat.cast_ofNat] using hlarge) y
    simpa only [hcard] using he
  have hb := random_fiber_counting Bad G _ hfiber hpoint
  have he : probability (BadWithCondition (s := s) A D h) = probability Bad :=
    finite_probability_equiv E _ _ (fun f ↦ by simp only [Bad, Equiv.symm_apply_apply])
  rw [he]
  simpa only [hcard, Nat.cast_pow, Nat.cast_ofNat, totalBound] using hb

end Lax323828Proofs
