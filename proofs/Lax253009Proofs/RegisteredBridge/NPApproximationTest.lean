import Lax253009Proofs.RegisteredBridge.ComputableSmallValue
import Lax253009Proofs.RegisteredBridge.ComputableProjectionEncoding
import Lax253009Proofs.RegisteredBridge.ComputableFAF
import Lax253009Proofs.RegisteredBridge.SampledGraphDecision
import Lax253009Proofs.GameToClique

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

namespace Lax253009Proofs.RegisteredBridge

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding ComputableNumbering
open ComputableAmplification Lax253009 CenteredProjection FAFLocalTests TestSampling FiniteProbability
open FAFDataAlgorithms FAFPartAlgorithms
open scoped Classical

/-- A clique approximation supplies, for every registered NP language, a
uniform polynomial-time test of an input and a fair random tape. Members
pass for every tape and nonmembers pass with probability at most one third.
The remaining model conversion must implement this test by a registered
probabilistic procedure. -/
theorem approximation_random_test (F : FinBase) (hd : 1 < F.deg)
    (ε : ℝ) (hε : 0 < ε) (happrox : Approximation.Approximable ε) :
    ∀ L ∈ Lax434930.NondeterministicPolynomialTime.NP,
      ∃ b : Word → ℕ, UnaryFn b ∧ ∃ D : Word → Prop, FPPred D ∧
        (∀ x ∈ L, ∀ coins : Fin (b x) → Bool, D (pair x (List.ofFn coins))) ∧
        (∀ x ∉ L, probability (fun coins : Fin (b x) → Bool ↦ D (pair x (List.ofFn coins))) ≤ 1 / 3) := by
  let θ := min ε 1
  have hθ : 0 < θ := lt_min hε zero_lt_one
  obtain ⟨estimate, ⟨M⟩, hestimate⟩ := SampledGraphDecision.approximation_decision θ hθ
    (min_le_right _ _) (approximation_weaken (min_le_left _ _) happrox)
  obtain ⟨l, hl⟩ := exists_nat_gt (1 / θ)
  have hlpos : 0 < l := by exact_mod_cast (div_pos zero_lt_one hθ).trans hl
  have hlθ : 1 < (l : ℝ) * θ := (div_lt_iff₀ hθ).mp hl
  obtain ⟨s₀, hs₀⟩ := faf_local_soundness l hlpos
  let s := max s₀ 1
  have hspos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  obtain ⟨w₀, hw₀⟩ := hs₀ s (le_max_left _ _)
  have hmargin : 0 < (20 * l * l * s : ℕ) * θ - (20 * l * s : ℕ) * (1 - θ) := by
    push_cast
    have hp : 0 < (20 : ℝ) * l * s := by positivity
    have hm : 0 < (l : ℝ) * θ - (1 - θ) := by linarith
    nlinarith [mul_pos hp hm]
  obtain ⟨c, hc, hcmargin⟩ := sampling_choose_multiplier θ (20 * l * s) (20 * l * l * s) hmargin
  let δ := FAFComposition.gameThreshold l s / 2
  have hδ : 0 < δ := half_pos (faf_game_threshold_pos l s)
  have hδlt : δ < FAFComposition.gameThreshold l s := half_lt_self (faf_game_threshold_pos l s)
  obtain ⟨S, hS⟩ := computable_small_value F hd δ hδ
  let X := S.centers DinurAlpha
  let Y := S.questions (DinurAlpha × DinurAlpha)
  let u := Fintype.card X
  let w := max w₀ (Fintype.card Y)
  obtain ⟨ix⟩ := projection_encoding_exists (A := X) u le_rfl
  obtain ⟨iy⟩ := projection_encoding_exists (A := Y) w (le_max_right _ _)
  intro L hL
  obtain ⟨U, O, W, hU, hO, hW, hpos, G, hG, hyes, hno⟩ := hS L hL
  let H := ComputableProjectionEncoding.encoded ix iy G
  have hH := ComputableProjectionEncoding.algorithms ix iy
    (center_code_injective S code code_injective) G hG
  let pu := fin U hU
  let po := fin O hO
  let pw := fin W hW
  let pr := seedNumbering (unary U) (unary O) pu po u w (10 * l) s (10 * l * s)
  let pi := indexNumbering pu pw u w
  obtain ⟨C, E, hE, hCyes, hCno⟩ := computable_faf (10 * l) s (10 * l * s) pu po pw H hH
  let f := 10 * l * s + 10 * l * s
  have hf : f = 20 * l * s := by dsimp [f]; ring
  have hcm : 1 ≤ (c : ℝ) * ((20 * l * l * s : ℕ) * θ - (f : ℝ) * (1 - θ)) := by
    simpa only [hf] using hcmargin
  have hr : ∀ x, 0 < pr.size x := by
    intro x
    letI : Nonempty (Fin (U x)) := Fin.pos_iff_nonempty.mp (hpos x).1
    letI : Nonempty (Fin (O x)) := Fin.pos_iff_nonempty.mp (hpos x).2.1
    exact Fin.pos_iff_nonempty.mpr ⟨pr.equiv x (Classical.arbitrary _)⟩
  let b := fun x ↦ SampledGraphDecision.coinCount (pr.size x) (pi.size x) (20 * l * l * s) c
  let D := fun z ↦ SamplingParameters.threshold (pi.size (pairFst z)) <
    estimate (ComputableSampledGraph.graph E hr (20 * l * l * s) c (pairFst z) (pairSnd z)).encode
  have hD (x coins : Word) : D (pair x coins) ↔
      SamplingParameters.threshold (pi.size x) <
        estimate (ComputableSampledGraph.graph E hr (20 * l * l * s) c x coins).encode := by
    change SamplingParameters.threshold (pi.size (pairFst (pair x coins))) <
      estimate (ComputableSampledGraph.graph E hr (20 * l * l * s) c
        (pairFst (pair x coins)) (pairSnd (pair x coins))).encode ↔ _
    rw [pairFst_pair, pairSnd_pair]
  refine ⟨b, SampledGraphDecision.coinCount_poly pr.size_poly pi.size_poly _ _, D,
    SampledGraphDecision.decision_mem_FP E hr hE pr.size_poly pi.size_poly _ _ M, ?_, ?_⟩
  · intro x hx coins
    have hcomplete : Complete (C x) := by
      apply hCyes
      obtain ⟨P, Q, hpq⟩ := hyes x hx
      obtain ⟨hv, hp⟩ := projection_encoding_complete ix iy (G x).question (G x).valid (G x).project
        P Q (fun v ω ↦ (hpq v ω).1) (fun v ω ↦ (hpq v ω).2)
      exact faf_local_perfect_completeness _ _ _ (fun a ↦ iy (P a)) (fun a ↦ ix (Q a)) hv hp
    have hh := (hestimate f (20 * l * l * s) c hc hcm E hr x).1
      hcomplete (List.ofFn coins)
    exact (hD x (List.ofFn coins)).mpr hh
  · intro x hx
    have hsound : Sound (C x) ((1 / 2 : ℝ) ^ (20 * l * l * s)) := by
      apply hCno
      letI : Nonempty (Fin (U x)) := Fin.pos_iff_nonempty.mp (hpos x).1
      letI : Nonempty (Fin (O x)) := Fin.pos_iff_nonempty.mp (hpos x).2.1
      apply hw₀ w (le_max_left _ _) u (H x).question (H x).project (H x).valid
      intro P Q
      exact (projection_encoding_sound ix iy (G x).question (G x).valid (G x).project δ
        (hno x hx) P Q).trans_lt hδlt
    have hh := (hestimate f (20 * l * l * s) c hc hcm E hr x).2 hsound
    apply le_trans (finite_probability_mono _ _ ?_) hh
    intro coins hcoin
    exact (hD x (List.ofFn coins)).mp hcoin

end Lax253009Proofs.RegisteredBridge
