import Lax253009Proofs.RegisteredBridge.ComputableEncodings
import Lax253009.Amplification

set_option backward.isDefEq.respectTransparency false

namespace Lax253009Proofs.RegisteredBridge.ComputableAmplification

open PCPFoundation.Complexity FiniteEncoding ComputableEncoding
open Lax253009.CenteredProjection
open Lax253009.Amplification

variable {U Ω W : Family} {X Y : Type}

structure Algorithms (eu : Encoding U) (eo : Encoding Ω) (ew : Encoding W)
    (ex : X → Word) (ey : Y → Word) (G : ∀ z, System (U z) (Ω z) (W z) X Y) : Prop where
  question : Realizes (prod eu eo) ew (fun z p ↦ (G z).question p.1 p.2)
  valid : Realizes (prod (prod eu eo) (fun _ ↦ ey)) (finite Bool)
    (fun z p ↦ (G z).valid p.1.1 p.1.2 p.2)
  project : Realizes (prod (prod eu eo) (fun _ ↦ ey)) (fun _ ↦ ex)
    (fun z p ↦ (G z).project p.1.1 p.1.2 p.2)

theorem zip_left {A B C D : Family} (a : Encoding A) (b : Encoding B)
    (c : Encoding C) (d : Encoding D) :
    Realizes (prod (prod a b) (prod c d)) (prod a c) (fun _ p ↦ (p.1.1, p.2.1)) :=
  pair_maps (comp (fst _ _) (fst _ _)) (comp (snd _ _) (fst _ _))

theorem zip_right {A B C D : Family} (a : Encoding A) (b : Encoding B)
    (c : Encoding C) (d : Encoding D) :
    Realizes (prod (prod a b) (prod c d)) (prod b d) (fun _ p ↦ (p.1.2, p.2.2)) :=
  pair_maps (comp (fst _ _) (snd _ _)) (comp (snd _ _) (snd _ _))

theorem tensor (eu : Encoding U) (eo : Encoding Ω) (ew : Encoding W)
    (ex : X → Word) (ey : Y → Word) (G : ∀ z, System (U z) (Ω z) (W z) X Y)
    (h : Algorithms eu eo ew ex ey G) :
    Algorithms (prod eu eu) (prod eo eo) (prod ew ew)
      (fun x ↦ pair (ex x.1) (ex x.2)) (fun y ↦ pair (ey y.1) (ey y.2))
      (fun z ↦ (G z).tensor) := by
  let eargs := prod (prod (prod eu eu) (prod eo eo)) (prod (fun _ ↦ ey) (fun _ ↦ ey))
  have hl : Realizes eargs (prod (prod eu eo) (fun _ ↦ ey))
      (fun _ p ↦ ((p.1.1.1, p.1.2.1), p.2.1)) :=
    pair_maps (comp (fst _ _) (zip_left _ _ _ _)) (comp (snd _ _) (fst _ _))
  have hr : Realizes eargs (prod (prod eu eo) (fun _ ↦ ey))
      (fun _ p ↦ ((p.1.1.2, p.1.2.2), p.2.2)) :=
    pair_maps (comp (fst _ _) (zip_right _ _ _ _)) (comp (snd _ _) (snd _ _))
  refine ⟨pair_maps (comp (zip_left _ _ _ _) h.question)
    (comp (zip_right _ _ _ _) h.question), ?_, pair_maps (comp hl h.project) (comp hr h.project)⟩
  have hand := fixed_map (fun p : Bool × Bool ↦ pair (code p.1) (code p.2))
    (fun p q hp ↦ Prod.ext (code_injective (pair_inj hp).1) (code_injective (pair_inj hp).2))
    code (fun p ↦ p.1 && p.2)
  exact comp (pair_maps (comp hl h.valid) (comp hr h.valid)) hand

theorem fortify (eu : Encoding U) (eo : Encoding Ω) (ew : Encoding W)
    (ex : X → Word) (ey : Y → Word) (G : ∀ z, System (U z) (Ω z) (W z) X Y)
    (h : Algorithms eu eo ew ex ey G) (t : ℕ) :
    Algorithms eu (prod eo (prod (finite (Fin t)) (tuple ew t))) (tuple ew t)
      ex (fun y ↦ Cobham.encodeVec (fun i ↦ ey (y i))) (fun z ↦ (G z).fortify t) := by
  let eh := prod (finite (Fin t)) (tuple ew t)
  let eω := prod eo eh
  let ebase := prod eu eω
  have hh : Realizes ebase eh (fun _ p ↦ p.2.2) :=
    comp (snd eu eω) (snd eo eh)
  have hi : Realizes ebase (finite (Fin t)) (fun _ p ↦ p.2.2.1) :=
    comp hh (fst (finite (Fin t)) (tuple ew t))
  have hhistory : Realizes ebase (tuple ew t) (fun _ p ↦ p.2.2.2) :=
    comp hh (snd (finite (Fin t)) (tuple ew t))
  have hbase : Realizes ebase (prod eu eo) (fun _ p ↦ (p.1, p.2.1)) :=
    pair_maps (fst eu eω) (comp (snd eu eω) (fst eo eh))
  have hquestion : Realizes ebase ew (fun z p ↦ (G z).question p.1 p.2.1) := comp hbase h.question
  have hplanted : Realizes ebase (tuple ew t)
      (fun z p j ↦ if j = p.2.2.1 then (G z).question p.1 p.2.1 else p.2.2.2 j) := by
    apply tuple_maps
    intro j
    apply finite_dispatch (f := fun i z p ↦
      if j = i then (G z).question p.1 p.2.1 else p.2.2.2 j) hi
    intro i
    by_cases hij : j = i
    · simpa only [hij, if_true] using hquestion
    · simpa only [hij, if_false] using comp hhistory (tuple_entry ew j)
  let eargs := prod ebase (tuple (fun _ ↦ ey) t)
  have hy : Realizes eargs (tuple (fun _ ↦ ey) t) (fun _ p ↦ p.2) := snd _ _
  have houter : Realizes eargs ebase (fun _ p ↦ p.1) := fst ebase (tuple (fun _ ↦ ey) t)
  have hi' := comp houter hi
  have hselected : Realizes eargs (fun _ ↦ ey) (fun _ p ↦ p.2 p.1.2.2.1) :=
    finite_tuple_entry hy hi'
  have hargs : Realizes eargs (prod (prod eu eo) (fun _ ↦ ey))
      (fun _ p ↦ ((p.1.1, p.1.2.1), p.2 p.1.2.2.1)) :=
    pair_maps (comp houter hbase) hselected
  refine ⟨?_, comp hargs h.valid, comp hargs h.project⟩
  apply of_pointwise hplanted
  intro z p
  funext j
  simp only [System.fortify, Lax253009.TupleFortification.plant, Function.update_apply]

def centerCode {A : Type} (S : Scheme) (e : A → Word) : S.centers A → Word :=
  match S with
  | .base => e
  | .step _ S => fun p ↦ pair (centerCode S e p.1) (centerCode S e p.2)

def questionCode {A : Type} (S : Scheme) (e : A → Word) : S.questions A → Word :=
  match S with
  | .base => e
  | .step _ S => fun p ↦
      pair (Cobham.encodeVec (fun i ↦ questionCode S e (p.1 i)))
        (Cobham.encodeVec (fun i ↦ questionCode S e (p.2 i)))

noncomputable def extensionCode {A B : Type} (S : Scheme) (a : A → Word) (b : B → Word) :
    S.extensions A B → Word := match S with
  | .base => a
  | .step _ S => fun p ↦
      pair (pair (extensionCode S a b p.1.1)
        (pair (code p.1.2.1) (Cobham.encodeVec (fun i ↦ questionCode S b (p.1.2.2 i)))))
      (pair (extensionCode S a b p.2.1)
        (pair (code p.2.2.1) (Cobham.encodeVec (fun i ↦ questionCode S b (p.2.2.2 i)))))

theorem transform (eu : Encoding U) (eo : Encoding Ω) (ew : Encoding W)
    (ex : X → Word) (ey : Y → Word) (G : ∀ z, System (U z) (Ω z) (W z) X Y)
    (h : Algorithms eu eo ew ex ey G) (S : Scheme) :
    Algorithms (fun z ↦ centerCode S (eu z)) (fun z ↦ extensionCode S (eo z) (ew z))
      (fun z ↦ questionCode S (ew z)) (centerCode S ex) (questionCode S ey)
      (fun z ↦ S.transform (G z)) := by
  induction S with
  | base => exact h
  | step t S ih =>
    exact tensor _ _ _ _ _ _ (fortify _ _ _ _ _ _ ih t)

theorem center_code_injective {A : Type} (S : Scheme) (e : A → Word)
    (he : Function.Injective e) : Function.Injective (centerCode S e) := by
  induction S with
  | base => exact he
  | step t S ih =>
    intro x y h
    obtain ⟨h₁, h₂⟩ := pair_inj h
    exact Prod.ext (ih h₁) (ih h₂)

theorem question_code_injective {A : Type} (S : Scheme) (e : A → Word)
    (he : Function.Injective e) : Function.Injective (questionCode S e) := by
  induction S with
  | base => exact he
  | step t S ih =>
    intro x y h
    obtain ⟨h₁, h₂⟩ := pair_inj h
    apply Prod.ext
    · funext i
      apply ih
      simpa only [entry_encodeVec] using congrArg (entry i.val) h₁
    · funext i
      apply ih
      simpa only [entry_encodeVec] using congrArg (entry i.val) h₂

end Lax253009Proofs.RegisteredBridge.ComputableAmplification
