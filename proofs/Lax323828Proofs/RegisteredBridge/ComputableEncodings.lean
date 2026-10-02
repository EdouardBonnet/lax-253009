import Lax323828Proofs.RegisteredBridge.FiniteWordEncoding
import Lax323828Proofs.RegisteredBridge.TM2InputOutput

set_option backward.isDefEq.respectTransparency false

namespace Lax323828Proofs.RegisteredBridge.ComputableEncoding

open PCPFoundation.Complexity FiniteEncoding

abbrev Word := List Bool
abbrev Family := Word → Type
abbrev Encoding (A : Family) := ∀ z, A z → Word

def prod {A B : Family} (a : Encoding A) (b : Encoding B) : Encoding (fun z ↦ A z × B z) :=
  fun z p ↦ pair (a z p.1) (b z p.2)

def tuple {A : Family} (a : Encoding A) (n : ℕ) : Encoding (fun z ↦ Fin n → A z) :=
  fun z v ↦ Cobham.encodeVec (fun i ↦ a z (v i))

noncomputable def finite (A : Type) [Fintype A] : Encoding (fun _ ↦ A) := fun _ ↦ code

/-- A single polynomial-time algorithm acts correctly on every encoded input
in a family; the original word is retained as the uniform parameter. -/
def Realizes {A B : Family} (a : Encoding A) (b : Encoding B)
    (f : ∀ z, A z → B z) : Prop :=
  ∃ F : Word → Word, F ∈ FP ∧ ∀ z v, F (pair z (a z v)) = b z (f z v)

variable {A B C D : Family} {a : Encoding A} {b : Encoding B} {c : Encoding C} {d : Encoding D}

theorem identity (a : Encoding A) : Realizes a a (fun _ v ↦ v) :=
  ⟨pairSnd, pairSnd_mem_FP, fun _ _ ↦ pairSnd_pair _ _⟩

theorem comp {f : ∀ z, A z → B z} {g : ∀ z, B z → C z}
    (hf : Realizes a b f) (hg : Realizes b c g) :
    Realizes a c (fun z v ↦ g z (f z v)) := by
  obtain ⟨F, hF, hFc⟩ := hf
  obtain ⟨G, hG, hGc⟩ := hg
  refine ⟨fun z ↦ G (pair (pairFst z) (F z)),
    mem_FP_comp (mem_FP_pair pairFst_mem_FP hF) hG, ?_⟩
  intro z v
  dsimp only
  rw [pairFst_pair, hFc, hGc]

theorem fst (a : Encoding A) (b : Encoding B) :
    Realizes (prod a b) a (fun _ v ↦ v.1) :=
  ⟨pairFst ∘ pairSnd, mem_FP_comp pairSnd_mem_FP pairFst_mem_FP,
    fun _ _ ↦ by simp [prod]⟩

theorem snd (a : Encoding A) (b : Encoding B) :
    Realizes (prod a b) b (fun _ v ↦ v.2) :=
  ⟨pairSnd ∘ pairSnd, mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP,
    fun _ _ ↦ by simp [prod]⟩

theorem pair_maps {f : ∀ z, A z → B z} {g : ∀ z, A z → C z}
    (hf : Realizes a b f) (hg : Realizes a c g) :
    Realizes a (prod b c) (fun z v ↦ (f z v, g z v)) := by
  obtain ⟨F, hF, hFc⟩ := hf
  obtain ⟨G, hG, hGc⟩ := hg
  exact ⟨fun z ↦ pair (F z) (G z), mem_FP_pair hF hG,
    fun z v ↦ by simp only [prod, hFc, hGc]⟩

theorem tuple_maps {n : ℕ} {f : ∀ z, A z → Fin n → B z}
    (hf : ∀ i, Realizes a b (fun z v ↦ f z v i)) :
    Realizes a (tuple b n) f := by
  classical
  choose F hF hFc using hf
  refine ⟨fun z ↦ Cobham.encodeVec (fun i ↦ F i z), encodeVec_mem_FP F hF, ?_⟩
  intro z v
  change Cobham.encodeVec (fun i ↦ F i (pair z (a z v))) =
    Cobham.encodeVec (fun i ↦ b z (f z v i))
  congr 1
  funext i
  exact hFc i z v

theorem tuple_entry {n : ℕ} (a : Encoding A) (i : Fin n) :
    Realizes (tuple a n) a (fun _ v ↦ v i) := by
  refine ⟨entry i.val ∘ pairSnd, mem_FP_comp pairSnd_mem_FP (entry_mem_FP i.val), ?_⟩
  intro z v
  simp only [Function.comp_apply, pairSnd_pair, tuple, entry_encodeVec]

theorem of_pointwise {f g : ∀ z, A z → B z} (hf : Realizes a b f)
    (h : ∀ z v, f z v = g z v) : Realizes a b g := by
  obtain ⟨F, hF, hc⟩ := hf
  exact ⟨F, hF, fun z v ↦ (hc z v).trans (congrArg (b z) (h z v))⟩

theorem finite_map {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y) :
    Realizes (finite X) (finite Y) (fun _ ↦ f) := by
  classical
  let read : Word → Word := fun w ↦
    match decode (A := X) w with | none => [] | some x => code (f x)
  refine ⟨fun z ↦ read ((pairSnd z).take (Fintype.card X)),
    bounded_read_mem_FP pairSnd_mem_FP (Fintype.card X) read, ?_⟩
  intro z x
  change read ((pairSnd (pair z (code x))).take (Fintype.card X)) = code (f x)
  rw [pairSnd_pair, List.take_of_length_le (by rw [code_length])]
  simp only [read, decode_code]

theorem finite_constant {X : Type} [Fintype X] (a : Encoding A) (x : X) :
    Realizes a (finite X) (fun _ _ ↦ x) :=
  ⟨fun _ ↦ code x, constFn_mem_FP _, fun _ _ ↦ rfl⟩

theorem finite_dispatch {X : Type} [Fintype X] {key : ∀ z, A z → X}
    (hk : Realizes a (finite X) key) {f : X → ∀ z, A z → B z}
    (hf : ∀ x, Realizes a b (f x)) :
    Realizes a b (fun z v ↦ f (key z v) z v) := by
  classical
  obtain ⟨K, hK, hKc⟩ := hk
  choose F hF hFc using hf
  let read : Word → Option X := decode
  let out : Option X → Word → Word := fun x ↦ match x with | none => fun _ ↦ [] | some x => F x
  refine ⟨fun z ↦ out (read ((K z).take (Fintype.card X))) z,
    bounded_dispatch_mem_FP (take_mem_FP hK (Fintype.card X))
      (fun z ↦ List.length_take_le _ _) read out (fun x ↦ ?_), ?_⟩
  · cases x with
    | none => exact constFn_mem_FP []
    | some x => exact hF x
  · intro z v
    simp only [hKc, finite, ← code_length (key z v), List.take_length, read, decode_code,
      out, hFc]

theorem finite_tuple_entry {n : ℕ} {f : ∀ z, A z → Fin n → B z}
    {index : ∀ z, A z → Fin n}
    (hf : Realizes a (tuple b n) f) (hi : Realizes a (finite (Fin n)) index) :
    Realizes a b (fun z v ↦ f z v (index z v)) :=
  finite_dispatch hi (fun i ↦ comp hf (tuple_entry b i))

theorem prod_injective (ha : ∀ z, Function.Injective (a z))
    (hb : ∀ z, Function.Injective (b z)) : ∀ z, Function.Injective (prod a b z) := by
  intro z x y h
  obtain ⟨h₁, h₂⟩ := pair_inj h
  exact Prod.ext (ha z h₁) (hb z h₂)

theorem tuple_injective (ha : ∀ z, Function.Injective (a z)) (n : ℕ) :
    ∀ z, Function.Injective (tuple a n z) := by
  intro z v w h
  funext i
  apply ha z
  have hh := congrArg (entry i.val) h
  simpa only [tuple, entry_encodeVec] using hh

/-- Every map on a fixed finite encoded alphabet has a polynomial-time
realizer. The bound depends on the alphabet, never on the input word. -/
theorem fixed_map {X Y : Type} [Fintype X] (ex : X → Word)
    (hx : Function.Injective ex) (ey : Y → Word) (f : X → Y) :
    Realizes (fun _ ↦ ex) (fun _ ↦ ey) (fun _ ↦ f) := by
  classical
  let width := Finset.univ.sup (fun x : X ↦ (ex x).length)
  let read : Word → Word := fun w ↦ if h : ∃ x, ex x = w then ey (f h.choose) else []
  refine ⟨fun z ↦ read ((pairSnd z).take width), bounded_read_mem_FP pairSnd_mem_FP width read, ?_⟩
  intro z x
  change read ((pairSnd (pair z (ex x))).take width) = ey (f x)
  have hlen : (ex x).length ≤ width := Finset.le_sup (f := fun x : X ↦ (ex x).length) (Finset.mem_univ x)
  rw [pairSnd_pair, List.take_of_length_le hlen]
  have h : ∃ y, ex y = ex x := ⟨x, rfl⟩
  simp only [read, dif_pos h]
  rw [hx h.choose_spec]

end Lax323828Proofs.RegisteredBridge.ComputableEncoding
