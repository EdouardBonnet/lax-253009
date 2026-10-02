import Lax323828Proofs.RegisteredBridge.MultitapeCleanup
import Lax323828Proofs.RegisteredBridge.TM2InputOutput
import Lax323828Proofs.PCPFoundation.Classes.P.Defs
import Lax323828Proofs.PCPFoundation.Asymptotics.PolyBound

set_option backward.isDefEq.respectTransparency false

namespace Lax323828Proofs.RegisteredBridge.MultitapeMachine

open PCPFoundation.Complexity Turing StackTapeMachine MultitapeCore Time

variable {n : ℕ}

theorem initial_size (x : List Bool) (i : Index n) :
    (initialTapes x i).left.length + (initialTapes x i).right.length ≤ x.length := by
  cases i with
  | inl b => cases b <;> simp [initialTapes, StackTape.init]
  | inr i => simp [initialTapes, StackTape.init]

theorem decider_run (M : TM n) {L : Language} {T : ℕ → ℕ}
    (hM : M.DecidesInTime L T) (f : List Bool → Bool) (hf : ∀ x, f x = true ↔ x ∈ L)
    (x : List Bool) :
    Within (machine M).step (8 * (x.length + T x.length + 1))
      (initList (machine M) x) (haltList (machine M) [f x]) := by
  obtain ⟨c, m, hm, hr, hhalt, hy, hn⟩ := hM x
  obtain ⟨s, t, b, he, hsize, hrun⟩ := MultitapeCore.run M Label.simulate
    (.goto fun _ ↦ Label.rewindOutput) (program M) rfl hr
      (initialCache M) (fun _ ↦ []) (initialTapes x) false (initial_cfg M x)
  have hb : ∀ i, (t i).left.length + (t i).right.length ≤ x.length + m := by
    intro i
    exact (hsize i).trans (Nat.add_le_add_right (initial_size x i) m)
  have hh : s.state = M.qhalt := (congrArg Cfg.state he).trans hhalt
  obtain ⟨u, hu, hc, hs, hrewind⟩ := rewind_run M s t b
  have hbit : decide ((u output).toTape.cells 1 = Γ.one) = f x := by
    classical
    have ho : (u output).toTape.cells 1 = c.output.cells 1 :=
      (congrFun hc 1).trans (congrArg (fun d ↦ d.output.cells 1) he)
    rw [ho]
    by_cases hx : x ∈ L
    · simp [hy hx, (hf x).mpr hx]
    · have hf' : f x = false := Bool.eq_false_iff.mpr (fun h ↦ hx ((hf x).mp h))
      simp [hn hx, hf']
  let s' : Cache M.Q n := {s with verdict := decide ((u output).toTape.cells 1 = Γ.one)}
  have hclean := clear_run M s' u false (x.length + m) (by
    intro i
    have h := hs i
    have h' := hb i
    omega)
  have hprefix := ((init_run M x).trans hrun).trans
    (.one (simulate_halted M s t b hh))
  have hprefix' := (hprefix.trans hrewind).trans (.one (read_verdict M s u hu))
  have hwhole := (Within.trans
    (show Within (machine M).step _ _ _ from ⟨_, le_rfl, hprefix'⟩) hclean)
  have hresult : s'.verdict = f x := hbit
  rw [hresult] at hwhole
  apply hwhole.mono
  have h := hb output
  omega

theorem decider_polytime (M : TM n) {L : Language} {T : ℕ → ℕ} {d : ℕ}
    (hM : M.DecidesInTime L T) (hT : T =O (· ^ d))
    (f : List Bool → Bool) (hf : ∀ x, f x = true ↔ x ∈ L) :
    Nonempty (TM2ComputableInPolyTime id Computability.encodeBool f) := by
  obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hT
  refine ⟨{
    tm := machine M
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.C 8 * (Polynomial.X + p + 1)
    outputsFun := ?_
  }⟩
  intro x
  have h := (decider_run M hM f hf x).mono (show 8 * (x.length + T x.length + 1) ≤
      (Polynomial.C 8 * (Polynomial.X + p + 1)).eval x.length by
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    exact Nat.mul_le_mul_left 8 (Nat.add_le_add_right (Nat.add_le_add_left (hp _) _) _))
  simpa only [TM2OutputsInTime, Equiv.refl, List.map_id, id_eq,
    Computability.encodeBool, List.pure_def, Option.map_some] using h.evals

end Lax323828Proofs.RegisteredBridge.MultitapeMachine

namespace Lax323828Proofs.RegisteredBridge

open PCPFoundation.Complexity

theorem P_subset_registered_P : P ⊆ Lax434930.PolynomialTime.P := by
  classical
  intro L hL
  obtain ⟨d, hL⟩ := Set.mem_iUnion.mp hL
  obtain ⟨n, M, T, hM, hT⟩ := hL
  let f : List Bool → Bool := fun x ↦ decide (x ∈ L)
  have hf : ∀ x, f x = true ↔ x ∈ L := fun _ ↦ decide_eq_true_iff
  exact ⟨f, hf, MultitapeMachine.decider_polytime M hM hT f hf⟩

theorem registered_P_eq_P : Lax434930.PolynomialTime.P = P :=
  Set.Subset.antisymm registered_P_subset P_subset_registered_P

end Lax323828Proofs.RegisteredBridge
