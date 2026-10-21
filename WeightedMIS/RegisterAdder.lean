module

public import WeightedMIS.RegisterMachine
public import WeightedMIS.PointerArithmeticEval
public import WeightedMIS.EfficientSearchCodeBounds

/-!
# Closed register code for binary addition

The input registers contain the two word pointers and a carry bit. The code
loads their actual tags, calls the same finite procedure on the tails, branches
on the three Boolean inputs, and allocates the sum cell. Its return values are
the result pointer and carry bit. Register transfers are included in the trace.
-/

@[expose] public section

namespace WeightedMIS.RegisterAdder

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

variable {p : ℕ}

def sumLeaf (a b carry : Bool) : Command p :=
  .allocate 9 (.bit (.flag (Bits.fullAdd a b carry).1) (.register 7))
    (.ret [.register 9, .flag (Bits.fullAdd a b carry).2])

def carryBranch (a b : Bool) : Command p :=
  .branch (.register 8) (sumLeaf a b true) (sumLeaf a b false)

def secondBranch (a : Bool) : Command p :=
  .branch (.register 6) (carryBranch a true) (carryBranch a false)

def afterCall : Command p :=
  .branch (.register 4) (secondBranch true) (secondBranch false)

def nilBitCases (nilCase bitCase : Command p) : Cases (Command p) :=
  ⟨nilCase, bitCase, .fail, .fail, .fail, .fail⟩

/-- Finite syntax for the recursive addition procedure. -/
def adderBody (self : Fin p) : Command p :=
  .load (.register 0) 3 15 4 (nilBitCases
    (.load (.register 1) 5 15 6 (nilBitCases (.ret [.null, .register 2]) .fail))
    (.load (.register 1) 5 15 6 (nilBitCases .fail
      (.call self [.register 3, .register 5, .register 2] [7, 8] afterCall))))

/-- The allocation/return leaf has a fixed thirteen-event implementation. -/
theorem sumLeaf_exec (code : Code p) (h : Heap) (regs : Registers)
    (a b carry : Bool) (tail : Ptr) (ht : regs 7 = .pointer tail) :
    ∃ out, Exec code h regs (sumLeaf a b carry) out ∧
      out.value = [.pointer h.length, .flag (Bits.fullAdd a b carry).2] ∧
      out.heap = h ++ [.bit (Bits.fullAdd a b carry).1 tail] ∧
      out.trace.length = 13 := by
  refine ⟨_, Exec.allocate (c := .bit (Bits.fullAdd a b carry).1 tail) ?_
    (Exec.ret _ _ _), ?_, rfl, ?_⟩
  · simp [CellExpr.eval, Atom.eval, ht, Value.asFlag, Value.asPointer]
  · simp [withEvents, values, Atom.eval, Function.update_apply]
  · simp [withEvents, sumLeaf, CellExpr.args, values, moves, Atom.eval, Value.moves, ht]

/-- Three Boolean branches implement the full adder without arithmetic opcodes. -/
theorem afterCall_exec (code : Code p) (h : Heap) (regs : Registers)
    (a b carry : Bool) (tail : Ptr)
    (ha : regs 4 = .flag a) (hb : regs 6 = .flag b)
    (hc : regs 8 = .flag carry) (ht : regs 7 = .pointer tail) :
    ∃ out, Exec code h regs afterCall out ∧
      out.value = [.pointer h.length, .flag (Bits.fullAdd a b carry).2] ∧
      out.heap = h ++ [.bit (Bits.fullAdd a b carry).1 tail] ∧
      out.trace.length = 22 := by
  obtain ⟨leaf, hleaf, hv, hh, hl⟩ := sumLeaf_exec code h regs a b carry tail ht
  have h3 : Exec code h regs (carryBranch a b)
      (withEvents (.control :: (Value.flag carry).moves) leaf) := by
    apply Exec.branch (b := carry) (by simpa [Atom.eval] using hc)
    cases carry <;> exact hleaf
  have h2 : Exec code h regs (secondBranch a)
      (withEvents (.control :: (Value.flag b).moves)
        (withEvents (.control :: (Value.flag carry).moves) leaf)) := by
    apply Exec.branch (b := b) (by simpa [Atom.eval] using hb)
    cases b <;> exact h3
  have h1 : Exec code h regs afterCall
      (withEvents (.control :: (Value.flag a).moves)
        (withEvents (.control :: (Value.flag b).moves)
          (withEvents (.control :: (Value.flag carry).moves) leaf))) := by
    apply Exec.branch (b := a) (by simpa [Atom.eval] using ha)
    cases a <;> exact h2
  exact ⟨_, h1, hv, hh, by simp [withEvents, Value.moves, hl]⟩

theorem afterCall_within (code : Code p) (h : Heap) (regs : Registers)
    (a b carry : Bool) (tail : Ptr)
    (ha : regs 4 = .flag a) (hb : regs 6 = .flag b)
    (hc : regs 8 = .flag carry) (ht : regs 7 = .pointer tail) :
    Within code h regs afterCall [.pointer h.length, .flag (Bits.fullAdd a b carry).2]
      (h ++ [.bit (Bits.fullAdd a b carry).1 tail]) 22 := by
  obtain ⟨⟨value, heap, events⟩, he, hv, hh, hl⟩ := afterCall_exec code h regs a b carry tail ha hb hc ht
  dsimp only at hv hh hl
  subst value heap
  exact ⟨events, he, hl.le⟩

/-- The fixed register body implements every data-directed ripple-carry run.
The factor includes all decoded fields, arguments, returns, and register moves. -/
theorem compiled (code : Code p) (self : Fin p) (body : code self = adderBody self)
    {h : Heap} {ap bp : Ptr} {carry : Bool} {r : Run (Ptr × Bool)}
    (he : AddEval h ap bp carry r) :
    Within code h (initialRegisters [.pointer ap, .pointer bp, .flag carry]) (code self)
      [.pointer r.value.1, .flag r.value.2] r.heap (10 * r.trace.length) := by
  induction he with
  | @nil ap bp carry left right =>
    rw [body]
    let regs := initialRegisters [Value.pointer ap, .pointer bp, .flag carry]
    let first := loadRegisters regs 3 15 4 Cell.nil
    let second := loadRegisters first 5 15 6 Cell.nil
    have last := Within.ret code h second [.null, .register 2]
    have last' : Within code h second (.ret [.null, .register 2])
        [.pointer 0, .flag carry] h 5 := by
      simpa [second, first, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval] using last
    have loadB := Within.load (address := .register 1) (first := 5) (second := 15) (bit := 6)
      (branches := nilBitCases (.ret [.null, .register 2]) .fail)
      (by simp [Atom.eval, first, regs, loadRegisters, decoded, initialRegisters]) right last'
    have loadA := Within.load (address := .register 0) (first := 3) (second := 15) (bit := 4)
      (branches := nilBitCases
        (.load (.register 1) 5 15 6 (nilBitCases (.ret [.null, .register 2]) .fail))
        (.load (.register 1) 5 15 6 (nilBitCases .fail
          (.call self [.register 3, .register 5, .register 2] [7, 8] afterCall))))
      (by simp [Atom.eval, regs, initialRegisters]) left loadB
    exact loadA.mono (by simp [readTwoBefore, Program.load])
  | @bit ap bp atail btail a b carry r left right child ih =>
    rw [body]
    let regs := initialRegisters [Value.pointer ap, .pointer bp, .flag carry]
    let first := loadRegisters regs 3 15 4 (.bit a atail)
    let second := loadRegisters first 5 15 6 (.bit b btail)
    let returned := [Value.pointer r.value.1, .flag r.value.2]
    let ready := bindResults second [7, 8] returned
    have hargs : values second [.register 3, .register 5, .register 2] =
        [Value.pointer atail, .pointer btail, .flag carry] := by
      simp [second, first, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    have ha : ready 4 = .flag a := by
      simp [ready, returned, second, first, regs, bindResults, loadRegisters, decoded]
    have hb : ready 6 = .flag b := by
      simp [ready, returned, second, first, regs, bindResults, loadRegisters, decoded]
    have hc : ready 8 = .flag r.value.2 := by simp [ready, returned, bindResults]
    have ht : ready 7 = .pointer r.value.1 := by simp [ready, returned, bindResults]
    have last := afterCall_within code r.heap ready a b r.value.2 r.value.1 ha hb hc ht
    have call := Within.call (procedure := self) (arguments := [.register 3, .register 5, .register 2])
      (results := [7, 8]) (regs := second) (returned := returned)
      (by simpa only [hargs] using ih) last
    have loadB := Within.load (address := .register 1) (first := 5) (second := 15) (bit := 6)
      (branches := nilBitCases .fail
        (.call self [.register 3, .register 5, .register 2] [7, 8] afterCall))
      (by simp [Atom.eval, first, regs, loadRegisters, decoded, initialRegisters]) right call
    have loadA := Within.load (address := .register 0) (first := 3) (second := 15) (bit := 4)
      (branches := nilBitCases
        (.load (.register 1) 5 15 6 (nilBitCases (.ret [.null, .register 2]) .fail))
        (.load (.register 1) 5 15 6 (nilBitCases .fail
          (.call self [.register 3, .register 5, .register 2] [7, 8] afterCall))))
      (by simp [Atom.eval, regs, initialRegisters]) left loadB
    apply loadA.mono
    simp only [withEvents, adderAfter, readTwoBefore, Program.load, Program.allocate,
      List.length_append, List.length_cons, List.length_nil, List.length_replicate]
    omega

end WeightedMIS.RegisterAdder
