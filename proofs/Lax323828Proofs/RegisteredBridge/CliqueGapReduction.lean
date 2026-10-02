import Lax323828Proofs.RegisteredBridge.ComputableSmallValue
import Lax323828Proofs.RegisteredBridge.ComputableProjectionEncoding
import Lax323828Proofs.RegisteredBridge.ComputableFAF
import Lax323828Proofs.RegisteredBridge.SampledGraphDecision
import Lax323828Proofs.GameToClique

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

namespace Lax323828Proofs.RegisteredBridge

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding ComputableNumbering
open ComputableAmplification Lax323828 CenteredProjection FAFLocalTests TestSampling FiniteProbability
open FAFDataAlgorithms FAFPartAlgorithms
open scoped Classical

/-- The computational PCP reduction exposes a uniform gap in clique number.
It is independent of any algorithm used to estimate that number. -/
structure CliqueGapReduction (ε : ℝ) (L : Language) where
  bits : Word → ℕ
  bits_poly : UnaryFn bits
  size : Word → ℕ
  nonempty : ∀ x, 0 < size x
  threshold : Word → ℕ
  threshold_poly : UnaryFn threshold
  graph : ∀ x, Word → Graphs.Graph (size x)
  graph_poly : (fun z ↦ (graph (pairFst z) (pairSnd z)).encode) ∈ FP
  complete : ∀ x ∈ L, ∀ coins,
    Real.rpow (size x : ℝ) (1 - ε) * (threshold x : ℝ) <
      (graph x coins).cliqueNumber
  sound : ∀ x ∉ L,
    probability (fun coins : Fin (bits x) → Bool ↦
      threshold x ≤ (graph x (List.ofFn coins)).cliqueNumber) ≤ 1 / 3

theorem clique_gap_reduction (F : FinBase) (hd : 1 < F.deg)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ L ∈ Lax434930.NondeterministicPolynomialTime.NP,
      Nonempty (CliqueGapReduction ε L) := by
  obtain ⟨l, hl⟩ := exists_nat_gt (1 / ε)
  have hlpos : 0 < l := by exact_mod_cast (div_pos zero_lt_one hε).trans hl
  have hlε : 1 < (l : ℝ) * ε := (div_lt_iff₀ hε).mp hl
  obtain ⟨s₀, hs₀⟩ := Lax323828.FAFLocalTests.soundness l hlpos
  let s := max s₀ 1
  have hspos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  obtain ⟨w₀, hw₀⟩ := hs₀ s (le_max_left _ _)
  have hmargin : 0 < (20 * l * l * s : ℕ) * ε - (20 * l * s : ℕ) * (1 - ε) := by
    push_cast
    have hp : 0 < (20 : ℝ) * l * s := by positivity
    have hm : 0 < (l : ℝ) * ε - (1 - ε) := by linarith
    nlinarith [mul_pos hp hm]
  obtain ⟨c, hc, hcmargin⟩ := Lax323828.SamplingParameters.choose_multiplier ε (20 * l * s) (20 * l * l * s) hmargin
  let δ := FAFComposition.gameThreshold l s / 2
  have hδ : 0 < δ := half_pos (Lax323828.FAFComposition.threshold_positive l s)
  have hδlt : δ < FAFComposition.gameThreshold l s := half_lt_self (Lax323828.FAFComposition.threshold_positive l s)
  obtain ⟨S, hS⟩ := computable_small_value F hd δ hδ
  let X := S.centers DinurAlpha
  let Y := S.questions (DinurAlpha × DinurAlpha)
  let u := Fintype.card X
  let w := max w₀ (Fintype.card Y)
  obtain ⟨ix⟩ := Lax323828.ProjectionEncoding.encoding_exists (A := X) u le_rfl
  obtain ⟨iy⟩ := Lax323828.ProjectionEncoding.encoding_exists (A := Y) w (le_max_right _ _)
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
  have hcm : 1 ≤ (c : ℝ) * ((20 * l * l * s : ℕ) * ε - (f : ℝ) * (1 - ε)) := by
    simpa only [hf] using hcmargin
  have hr : ∀ x, 0 < pr.size x := by
    intro x
    let : Nonempty (Fin (U x)) := Fin.pos_iff_nonempty.mp (hpos x).1
    let : Nonempty (Fin (O x)) := Fin.pos_iff_nonempty.mp (hpos x).2.1
    exact Fin.pos_iff_nonempty.mpr ⟨pr.equiv x (Classical.arbitrary _)⟩
  refine ⟨{
    bits := fun x ↦ SampledGraphDecision.coinCount (pr.size x) (pi.size x) (20 * l * l * s) c
    bits_poly := SampledGraphDecision.coinCount_poly pr.size_poly pi.size_poly _ _
    size := fun x ↦ ComputableSampledGraph.size f (20 * l * l * s) c (pi.size x)
    nonempty := fun x ↦ ComputableSampledGraph.size_pos _ _ _ _
    threshold := fun x ↦ SamplingParameters.threshold (pi.size x)
    threshold_poly := (UnaryFn.const 4).mul (pi.size_poly.add (UnaryFn.const 2))
    graph := ComputableSampledGraph.graph E hr (20 * l * l * s) c
    graph_poly := ComputableSampledGraph.encode_mem_FP E hr hE pr.size_poly pi.size_poly _ _
    complete := ?_
    sound := ?_ }⟩
  · intro x hx coins
    have hcomplete : Complete (C x) := by
      apply hCyes
      obtain ⟨P, Q, hpq⟩ := hyes x hx
      obtain ⟨hv, hp⟩ := Lax323828.ProjectionEncoding.completeness ix iy (G x).question (G x).valid (G x).project
        P Q (fun v ω ↦ (hpq v ω).1) (fun v ω ↦ (hpq v ω).2)
      exact Lax323828.FAFLocalTests.perfect_completeness _ _ _ (fun a ↦ iy (P a)) (fun a ↦ ix (Q a)) hv hp
    have hlarge := SampledGraphDecision.perfect E hr (20 * l * l * s) c x coins hcomplete
    have hgap := Lax323828.SamplingParameters.approximation_gap ε hε hε1 f
      (20 * l * l * s) c hcm (pi.size x)
    rw [← ComputableSampledGraph.size_eq] at hgap
    exact hgap.trans_le (by exact_mod_cast hlarge)
  · intro x hx
    have hsound : Sound (C x) ((1 / 2 : ℝ) ^ (20 * l * l * s)) := by
      apply hCno
      let : Nonempty (Fin (U x)) := Fin.pos_iff_nonempty.mp (hpos x).1
      let : Nonempty (Fin (O x)) := Fin.pos_iff_nonempty.mp (hpos x).2.1
      apply hw₀ w (le_max_left _ _) u (H x).question (H x).project (H x).valid
      intro P Q
      exact (Lax323828.ProjectionEncoding.soundness ix iy (G x).question (G x).valid (G x).project δ
        (hno x hx) P Q).trans_lt hδlt
    exact SampledGraphDecision.sound E hr (20 * l * l * s) c hc x hsound

end Lax323828Proofs.RegisteredBridge
