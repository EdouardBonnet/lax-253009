import Lax323828Proofs.PCPFoundation.Models.TuringMachine
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace Lax323828Proofs.RegisteredBridge

open PCPFoundation.Complexity

/-- A finite two-stack presentation of a one-sided tape; omitted cells are blank. -/
structure StackTape where
  left : List Γ
  current : Γ
  right : List Γ

namespace StackTape

def contents (t : StackTape) : List Γ := t.left.reverse ++ t.current :: t.right

def toTape (t : StackTape) : Tape where
  head := t.left.length
  cells i := (t.contents[i]?).getD Γ.blank

def write (t : StackTape) (a : Γ) : StackTape :=
  if t.left = [] then t else {t with current := a}

def moveRight (t : StackTape) : StackTape :=
  ⟨t.current :: t.left, t.right.head?.getD Γ.blank, t.right.tail⟩

def moveLeft (t : StackTape) : StackTape :=
  match t.left with
  | [] => t
  | a :: l => ⟨l, a, t.current :: t.right⟩

def move (t : StackTape) : Dir3 → StackTape
  | .left => t.moveLeft
  | .right => t.moveRight
  | .stay => t

@[simp] theorem read_toTape (t : StackTape) : t.toTape.read = t.current := by
  simp [Tape.read, toTape, contents, List.getElem?_append_right]

theorem getD_append_blank (l : List Γ) (i : ℕ) :
    ((l ++ [Γ.blank])[i]?).getD Γ.blank = (l[i]?).getD Γ.blank := by
  induction l generalizing i with
  | nil => cases i <;> simp
  | cons a l ih => cases i with
    | zero => simp
    | succ i => simpa using ih i

theorem contents_move_right (t : StackTape) (i : ℕ) :
    ((t.moveRight.contents)[i]?).getD Γ.blank = (t.contents[i]?).getD Γ.blank := by
  cases t with
  | mk l c r =>
    cases r with
    | nil =>
      simpa [contents, moveRight, List.reverse_cons, List.append_assoc] using
        getD_append_blank (l.reverse ++ [c]) i
    | cons a r => simp [contents, moveRight, List.reverse_cons, List.append_assoc]

theorem toTape_move_right (t : StackTape) : t.moveRight.toTape = t.toTape.move .right := by
  apply Tape.ext
  · simp [toTape, moveRight, Tape.move]
  · funext i
    exact contents_move_right t i

theorem contents_move_left (t : StackTape) : t.moveLeft.contents = t.contents := by
  cases t with
  | mk l c r =>
    cases l <;> simp [contents, moveLeft, List.reverse_cons, List.append_assoc]

theorem toTape_move_left (t : StackTape) : t.moveLeft.toTape = t.toTape.move .left := by
  apply Tape.ext
  · cases t with
    | mk l c r => cases l <;> simp [toTape, moveLeft, Tape.move]
  · funext i
    simp only [toTape, Tape.move, contents_move_left]

theorem toTape_move (t : StackTape) (d : Dir3) : (t.move d).toTape = t.toTape.move d := by
  cases d
  · exact toTape_move_left t
  · exact toTape_move_right t
  · rfl

theorem contents_replace (t : StackTape) (a : Γ) :
    ({t with current := a} : StackTape).contents = t.contents.set t.left.length a := by
  simp [contents, List.set_append, List.length_reverse]

theorem toTape_write (t : StackTape) (a : Γ) : (t.write a).toTape = t.toTape.write a := by
  by_cases hl : t.left = []
  · simp [write, hl, toTape, Tape.write]
  · have hn : t.left.length ≠ 0 := by simpa using hl
    have hn' : t.toTape.head ≠ 0 := hn
    rw [write, if_neg hl, Tape.write, if_neg hn']
    apply Tape.ext
    · rfl
    · funext i
      change ((({t with current := a} : StackTape).contents)[i]?).getD Γ.blank =
        Function.update (fun j ↦ (t.contents[j]?).getD Γ.blank) t.left.length a i
      rw [contents_replace]
      by_cases hi : i = t.left.length
      · subst i
        rw [List.getElem?_set_self (by simp [contents]), Function.update_self]
        rfl
      · rw [List.getElem?_set_ne (Ne.symm hi), Function.update_of_ne hi]

def init (w : List Γ) : StackTape := ⟨[], Γ.start, w⟩

theorem toTape_init (w : List Γ) : (init w).toTape = Tape.init w := by
  apply Tape.ext
  · rfl
  · funext i
    cases i <;> simp [init, toTape, contents, Tape.init]

/-- The represented finite tape grows by at most one cell per head move. -/
theorem length_move_le (t : StackTape) (d : Dir3) :
    (t.move d).left.length + (t.move d).right.length ≤ t.left.length + t.right.length + 1 := by
  cases t with
  | mk l c r =>
    cases d
    · cases l <;> simp [move, moveLeft] <;> omega
    · cases r <;> simp [move, moveRight] <;> omega
    · simp [move]

end StackTape
end Lax323828Proofs.RegisteredBridge
