import Lax323828Proofs.RegisteredBridge.MultitapeMachine

set_option backward.isDefEq.respectTransparency false

namespace Lax323828Proofs.RegisteredBridge.MultitapeMachine

open PCPFoundation.Complexity Turing StackTapeMachine MultitapeCore Time


variable {n : ℕ}

theorem clear_live (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape) (b : Bool)
    (h : allDirty t = true) :
    (machine M).step (config (some Label.clear) s (fun _ ↦ []) t b) =
      some (config (some Label.clear) s (fun _ ↦ []) (fun i ↦ thin (t i)) true) := by
  change some (TM2.stepAux (program M .clear) (registers s t b) (tapeStacks (fun _ ↦ []) t)) = _
  unfold program
  simp only [TM2.stepAux, registers]
  erw [clear_all_step (fun _ ↦ []) s t false]
  simp [registers, h, TM2.stepAux, config]

theorem clear_done (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape) (b : Bool)
    (h : allDirty t = false) :
    (machine M).step (config (some Label.clear) s (fun _ ↦ []) t b) =
      some (haltList (machine M) [s.verdict]) := by
  have he := (all_dirty_eq_false t).mp h
  change some (TM2.stepAux (program M .clear) (registers s t b) (tapeStacks (fun _ ↦ []) t)) = _
  unfold program
  simp only [TM2.stepAux, registers]
  erw [clear_all_step (fun _ ↦ []) s t false]
  simp only [registers, h, Bool.false_or, Bool.cond_false, TM2.stepAux]
  congr 1
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl c => cases c <;> simp [haltList, machine, tapeStacks]
    | inr p =>
      obtain ⟨i, c⟩ := p
      cases c <;> simp [haltList, machine, tapeStacks, thin, (he i).1, (he i).2]

theorem clear_run (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape) (b : Bool)
    (B : ℕ) (hB : ∀ i, (t i).left.length ≤ B ∧ (t i).right.length ≤ B) :
    Within (machine M).step (B + 1)
      (config (some Label.clear) s (fun _ ↦ []) t b)
      (haltList (machine M) [s.verdict]) := by
  induction B generalizing t b with
  | zero =>
    apply Within.one
    apply clear_done
    rw [all_dirty_eq_false]
    intro i
    simpa only [Nat.le_zero, List.length_eq_zero_iff] using hB i
  | succ B ih =>
    cases hd : allDirty t
    · exact (Within.one (clear_done M s t b hd)).mono (by omega)
    · have hs := Within.one (clear_live M s t b hd)
      have ht := ih (fun i ↦ thin (t i)) true (by
        intro i
        have hi := hB i
        simp only [thin, List.length_tail]
        omega)
      simpa only [Nat.add_comm 1] using hs.trans ht

theorem simulate_halted (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape) (b : Bool)
    (h : s.state = M.qhalt) :
    (machine M).step (config (some Label.simulate) s (fun _ ↦ []) t b) =
      some (config (some Label.rewindOutput) s (fun _ ↦ []) t b) := by
  change some (TM2.stepAux (body M Label.simulate (.goto fun _ ↦ Label.rewindOutput))
    (registers s t b) (tapeStacks (fun _ ↦ []) t)) = _
  rw [body_halted M _ _ _ _ _ _ h]
  rfl

theorem rewind_nil (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape) (b : Bool)
    (h : (t output).left = []) :
    (machine M).step (config (some Label.rewindOutput) s (fun _ ↦ []) t b) =
      some (config (some Label.readVerdict) s (fun _ ↦ []) t false) := by
  simp [FinTM2.step, machine, program, config, TM2.step, TM2.stepAux,
    registers, tapeStacks, h]

theorem rewind_cons (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape) (b : Bool)
    (h : (t output).left ≠ []) :
    (machine M).step (config (some Label.rewindOutput) s (fun _ ↦ []) t b) =
      some (config (some Label.rewindOutput) s (fun _ ↦ [])
        (Function.update t output (t output).moveLeft) true) := by
  have hd : (t output).left.head?.isSome = true := by simpa using h
  change some (TM2.stepAux (program M .rewindOutput) (registers s t b)
    (tapeStacks (fun _ ↦ []) t)) = _
  simp only [program, TM2.stepAux, registers, tapeStacks, hd, Bool.cond_true]
  erw [left_step (fun _ ↦ []) s t true output (.goto fun _ ↦ Label.rewindOutput)]
  simp only [hd, TM2.stepAux, config]

theorem move_left_size (u : StackTape) :
    u.moveLeft.left.length + u.moveLeft.right.length = u.left.length + u.right.length := by
  cases u with
  | mk l c r => cases l <;> simp [StackTape.moveLeft] <;> omega

theorem rewind_run (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape) (b : Bool) :
    ∃ u, (u output).left = [] ∧ (u output).toTape.cells = (t output).toTape.cells ∧
      (∀ i, (u i).left.length + (u i).right.length =
        (t i).left.length + (t i).right.length) ∧
      Run (machine M).step ((t output).left.length + 1)
        (config (some Label.rewindOutput) s (fun _ ↦ []) t b)
        (config (some Label.readVerdict) s (fun _ ↦ []) u false) := by
  suffices ∀ m (t : Index n → StackTape) (b : Bool), (t output).left.length = m →
      ∃ u, (u output).left = [] ∧ (u output).toTape.cells = (t output).toTape.cells ∧
        (∀ i, (u i).left.length + (u i).right.length =
          (t i).left.length + (t i).right.length) ∧
        Run (machine M).step (m + 1)
          (config (some Label.rewindOutput) s (fun _ ↦ []) t b)
          (config (some Label.readVerdict) s (fun _ ↦ []) u false) from
    this _ t b rfl
  intro m
  induction m with
  | zero =>
    intro t b h
    have he : (t output).left = [] := List.length_eq_zero_iff.mp h
    exact ⟨t, he, rfl, fun _ ↦ rfl, .one (rewind_nil M s t b he)⟩
  | succ m ih =>
    intro t b h
    have hn : (t output).left ≠ [] := by intro he; simp [he] at h
    let t' := Function.update t output (t output).moveLeft
    have hlen : (t' output).left.length = m := by
      simp only [t', Function.update_self]
      cases he : (t output).left with
      | nil => exact False.elim (hn he)
      | cons a l => simp [StackTape.moveLeft, he] at h ⊢; omega
    obtain ⟨u, hu, hc, hs, hr⟩ := ih t' true hlen
    refine ⟨u, hu, ?_, ?_, .cons (rewind_cons M s t b hn) hr⟩
    · rw [hc]
      change (t output).moveLeft.toTape.cells = (t output).toTape.cells
      rw [StackTape.toTape_move_left]
      rfl
    · intro i
      rw [hs]
      by_cases hi : i = output
      · subst i; simp only [t', Function.update_self, move_left_size]
      · simp only [t', Function.update_of_ne hi]

theorem read_verdict (M : TM n) (s : Cache M.Q n) (t : Index n → StackTape)
    (h : (t output).left = []) :
    (machine M).step (config (some Label.readVerdict) s (fun _ ↦ []) t false) =
      some (config (some Label.clear)
        {s with verdict := decide ((t output).toTape.cells 1 = Γ.one)}
        (fun _ ↦ []) t false) := by
  have he : (t output).toTape.cells 1 = (t output).right.head?.getD Γ.blank := by
    simp only [StackTape.toTape, StackTape.contents, h, List.reverse_nil, List.nil_append,
      List.getElem?_cons_succ]
    cases (t output).right <;> rfl
  simp [FinTM2.step, machine, program, config, TM2.step, TM2.stepAux,
    registers, tapeStacks, he]

end Lax323828Proofs.RegisteredBridge.MultitapeMachine
