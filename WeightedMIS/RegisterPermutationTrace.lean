module

public import WeightedMIS.FiniteCycleEnumeration
public import WeightedMIS.CompiledTrie
public import WeightedMIS.EfficientSearchCodeBounds
public import WeightedMIS.RegisterMachineFrames
public import WeightedMIS.PointerRepresentations

/-!
# A finite register program tracing a stored permutation

Every successor is an actual pointer field in the supplied finite graph.
Fuel is the shape of a supplied list. The checked result is precisely the
mathematical iterate list, with one constant-size load/call/allocation round
per visited position; no permutation evaluation is a machine instruction.
-/

@[expose] public section

namespace WeightedMIS.RegisterPermutationTrace

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.CompiledTrie
open WeightedMIS.FiniteCycleEnumeration

variable {p : ℕ}

/-- A successor graph stored as payload/successor pairs. Its payload is an
allocated immutable value; the second field names the actual next record. -/
def SuccessorsAt {α : Type*} (next : α → α) (pointer : α → Ptr) (h : Heap) : Prop :=
  ∀ x, ∃ payload, h[pointer x]? = some (.pair payload (pointer (next x)))

theorem SuccessorsAt.mono {α : Type*} {next : α → α} {pointer : α → Ptr}
    {h h' : Heap} (ext : Extends h h') (hs : SuccessorsAt next pointer h) :
    SuccessorsAt next pointer h' := by
  intro x
  obtain ⟨payload, cell⟩ := hs x
  exact ⟨payload, ext.lookup cell⟩

/-- Arguments 0=fuel list, 1=current record, 2=output tail. -/
def traceBody (self : Fin p) : Command p :=
  .load (.register 0) 3 4 5 {
    failCases with
    nil := .ret [.register 2]
    cons := .load (.register 1) 6 7 8 {
      failCases with
      pair := .call self [.register 4, .register 7, .register 2] [9]
        (.allocate 10 (.cons (.register 1) (.register 9)) (.ret [.register 10]))
    }
  }

/-- The finite recursive procedure emits exactly the supplied graph's actual
iterate trace, retaining the existing tail by sharing. -/
theorem compiled {α : Type*} (code : Code p) (self : Fin p)
    (hcode : code self = traceBody self) (next : α → α) (pointer : α → Ptr)
    {h : Heap} (hh : Valid h) (graph : SuccessorsAt next pointer h)
    {fuel tail : Ptr} {fuelItems tailItems : List Ptr}
    (fuelAt : ListAt h fuel fuelItems) (tailAt : ListAt h tail tailItems) (x : α) :
    ∃ out final, Within code h (initialRegisters [.pointer fuel, .pointer (pointer x), .pointer tail])
      (code self) [.pointer out] final (38 * fuelItems.length + 13) ∧
      Valid final ∧ Extends h final ∧
      ListAt final out ((trace next fuelItems.length x).map pointer ++ tailItems) := by
  induction fuelAt generalizing x with
  | @nil fuel cell =>
    let regs := initialRegisters [Value.pointer fuel, .pointer (pointer x), .pointer tail]
    let loaded := loadRegisters regs 3 4 5 .nil
    have last : Within code h loaded (.ret [.register 2]) [.pointer tail] h 3 := by
      simpa [values, Atom.eval, loaded, regs, loadRegisters, decoded, initialRegisters] using
        Within.ret code h loaded [.register 2]
    have run := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 5)
      (branches := {failCases with
        nil := .ret [.register 2]
        cons := .load (.register 1) 6 7 8 {
          failCases with
          pair := .call self [.register 4, .register 7, .register 2] [9]
            (.allocate 10 (.cons (.register 1) (.register 9)) (.ret [.register 10]))
        }})
      (by simp [Atom.eval, regs, initialRegisters]) cell last
    refine ⟨tail, h, ?_, hh, Extends.refl h, ?_⟩
    · simpa [hcode, traceBody] using run
    · simpa [trace] using tailAt
  | @cons fuel item fuelTail items cell rest ih =>
    obtain ⟨payload, nodeCell⟩ := graph x
    obtain ⟨midPtr, mid, child, valid, ext, result⟩ := ih (next x)
    have allocated : pointer x < mid.length :=
      lt_of_lt_of_le (List.getElem?_eq_some_iff.mp nodeCell |>.1) ext.length_le
    obtain ⟨safe, consAt⟩ := allocate_cons valid allocated result
    let final := mid ++ [.cons (pointer x) midPtr]
    let regs := initialRegisters [Value.pointer fuel, .pointer (pointer x), .pointer tail]
    let loaded := loadRegisters regs 3 4 5 (.cons item fuelTail)
    let node := loadRegisters loaded 6 7 8 (.pair payload (pointer (next x)))
    let returned := bindResults node [9] [Value.pointer midPtr]
    have last : Within code final (Function.update returned 10 (.pointer mid.length))
        (.ret [.register 10]) [.pointer mid.length] final 3 := by
      simpa [values, Atom.eval] using
        Within.ret code final (Function.update returned 10 (.pointer mid.length)) [.register 10]
    have allocation := Within.allocate (dst := 10)
      (expr := .cons (.register 1) (.register 9)) (c := .cons (pointer x) midPtr)
      (by simp [CellExpr.eval, Atom.eval, returned, node, loaded, regs, bindResults,
        loadRegisters, decoded, initialRegisters, Value.asPointer]) last
    have call := Within.call (procedure := self) (regs := node)
      (arguments := [.register 4, .register 7, .register 2]) (results := [9])
      (by simpa [values, Atom.eval, node, loaded, regs, loadRegisters, decoded, initialRegisters]
        using child) allocation
    have nodeLoad := Within.load (address := .register 1) (first := 6) (second := 7) (bit := 8)
      (branches := {failCases with
        pair := .call self [.register 4, .register 7, .register 2] [9]
          (.allocate 10 (.cons (.register 1) (.register 9)) (.ret [.register 10]))})
      (by simp [Atom.eval, loaded, regs, loadRegisters, decoded, initialRegisters]) nodeCell call
    have fuelLoad := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 5)
      (branches := {failCases with
        nil := .ret [.register 2]
        cons := .load (.register 1) 6 7 8 {
          failCases with
          pair := .call self [.register 4, .register 7, .register 2] [9]
            (.allocate 10 (.cons (.register 1) (.register 9)) (.ret [.register 10]))
        }})
      (by simp [Atom.eval, regs, initialRegisters]) cell nodeLoad
    refine ⟨mid.length, final, ?_, safe.2.1, ext.trans safe.1, ?_⟩
    · rw [hcode]
      exact fuelLoad.mono (by simp [CellExpr.args, List.length_cons, Nat.mul_add]; omega)
    · simpa [trace, Program.allocate] using consAt

/-- A concrete one-procedure program traces any supplied successor table. -/
def program : Code 1 := fun _ => traceBody 0

end WeightedMIS.RegisterPermutationTrace
