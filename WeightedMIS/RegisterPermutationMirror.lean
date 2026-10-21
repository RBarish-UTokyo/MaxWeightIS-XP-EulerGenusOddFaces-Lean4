module

public import WeightedMIS.RegisterPermutationTrace
public import WeightedMIS.CompiledTrie
public import WeightedMIS.EfficientSearchCodeBounds
public import WeightedMIS.RegisterMachineFrames
public import WeightedMIS.PointerRepresentations

/-!
# Finite tracing of the reverse boundary representatives

A stored flag has an information record containing its immutable key and its
opposite endpoint flag. This routine follows the actual successor pointers
and emits the opposite flags. Together with ordinary tracing it forms the
complete boundary-equivalence block used by deterministic face enumeration.
-/

@[expose] public section

namespace WeightedMIS.RegisterPermutationMirror

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.CompiledTrie
open WeightedMIS.FiniteCycleEnumeration

variable {p : ℕ}

/-- A successor graph stored as payload/successor pairs. Its payload is an
allocated immutable value; the second field names the actual next record. -/
def FlagLinksAt {α : Type*} (next mirror : α → α) (pointer : α → Ptr) (h : Heap) : Prop :=
  ∀ x, ∃ info key, h[pointer x]? = some (.pair info (pointer (next x))) ∧
    h[info]? = some (.pair key (pointer (mirror x)))

theorem FlagLinksAt.mono {α : Type*} {next mirror : α → α} {pointer : α → Ptr}
    {h h' : Heap} (ext : Extends h h') (hs : FlagLinksAt next mirror pointer h) :
    FlagLinksAt next mirror pointer h' := by
  intro x
  obtain ⟨info, key, cell, link⟩ := hs x
  exact ⟨info, key, ext.lookup cell, ext.lookup link⟩

theorem FlagLinksAt.successors {α : Type*} {next mirror : α → α} {pointer : α → Ptr}
    {h : Heap} (hs : FlagLinksAt next mirror pointer h) :
    RegisterPermutationTrace.SuccessorsAt next pointer h := by
  intro x
  obtain ⟨info, key, cell, _⟩ := hs x
  exact ⟨info, cell⟩

/-- Arguments 0=fuel list, 1=current record, 2=output tail. -/
def traceBody (self : Fin p) : Command p :=
  .load (.register 0) 3 4 5 {
    failCases with
    nil := .ret [.register 2]
    cons := .load (.register 1) 6 7 8 {
      failCases with
      pair := .load (.register 6) 11 12 13 {
        failCases with
        pair := .call self [.register 4, .register 7, .register 2] [9]
          (.allocate 10 (.cons (.register 12) (.register 9)) (.ret [.register 10]))
      }
    }
  }

/-- The finite recursive procedure emits exactly the supplied graph's actual
iterate trace, retaining the existing tail by sharing. -/
theorem compiled {α : Type*} (code : Code p) (self : Fin p)
    (hcode : code self = traceBody self) (next mirror : α → α) (pointer : α → Ptr)
    {h : Heap} (hh : Valid h) (graph : FlagLinksAt next mirror pointer h)
    {fuel tail : Ptr} {fuelItems tailItems : List Ptr}
    (fuelAt : ListAt h fuel fuelItems) (tailAt : ListAt h tail tailItems) (x : α) :
    ∃ out final, Within code h (initialRegisters [.pointer fuel, .pointer (pointer x), .pointer tail])
      (code self) [.pointer out] final (48 * fuelItems.length + 13) ∧
      Valid final ∧ Extends h final ∧
      ListAt final out ((trace next fuelItems.length x).map (pointer ∘ mirror) ++ tailItems) := by
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
          pair := .load (.register 6) 11 12 13 {
            failCases with
            pair := .call self [.register 4, .register 7, .register 2] [9]
              (.allocate 10 (.cons (.register 12) (.register 9)) (.ret [.register 10]))
          }
        }})
      (by simp [Atom.eval, regs, initialRegisters]) cell last
    refine ⟨tail, h, ?_, hh, Extends.refl h, ?_⟩
    · simpa [hcode, traceBody] using run
    · simpa [trace] using tailAt
  | @cons fuel item fuelTail items cell rest ih =>
    obtain ⟨payload, key, nodeCell, infoCell⟩ := graph x
    obtain ⟨midPtr, mid, child, valid, ext, result⟩ := ih (next x)
    have allocated : pointer (mirror x) < mid.length :=
      lt_of_lt_of_le (hh.2 payload _ infoCell _ (by simp [Cell.references])) ext.length_le
    obtain ⟨safe, consAt⟩ := allocate_cons valid allocated result
    let final := mid ++ [.cons (pointer (mirror x)) midPtr]
    let regs := initialRegisters [Value.pointer fuel, .pointer (pointer x), .pointer tail]
    let loaded := loadRegisters regs 3 4 5 (.cons item fuelTail)
    let node := loadRegisters loaded 6 7 8 (.pair payload (pointer (next x)))
    let info := loadRegisters node 11 12 13 (.pair key (pointer (mirror x)))
    let returned := bindResults info [9] [Value.pointer midPtr]
    have last : Within code final (Function.update returned 10 (.pointer mid.length))
        (.ret [.register 10]) [.pointer mid.length] final 3 := by
      simpa [values, Atom.eval] using
        Within.ret code final (Function.update returned 10 (.pointer mid.length)) [.register 10]
    have allocation := Within.allocate (dst := 10)
      (expr := .cons (.register 12) (.register 9)) (c := .cons (pointer (mirror x)) midPtr)
      (by simp [CellExpr.eval, Atom.eval, returned, info, node, loaded, regs, bindResults,
        loadRegisters, decoded, initialRegisters, Value.asPointer]) last
    have call := Within.call (procedure := self) (regs := info)
      (arguments := [.register 4, .register 7, .register 2]) (results := [9])
      (by simpa [values, Atom.eval, info, node, loaded, regs, loadRegisters, decoded, initialRegisters]
        using child) allocation
    have infoLoad := Within.load (address := .register 6) (first := 11) (second := 12) (bit := 13)
      (branches := {failCases with
        pair := .call self [.register 4, .register 7, .register 2] [9]
          (.allocate 10 (.cons (.register 12) (.register 9)) (.ret [.register 10]))})
      (by simp [Atom.eval, node, loadRegisters, decoded]) infoCell call
    have nodeLoad := Within.load (address := .register 1) (first := 6) (second := 7) (bit := 8)
      (branches := {failCases with
        pair := .load (.register 6) 11 12 13 {
          failCases with
          pair := .call self [.register 4, .register 7, .register 2] [9]
            (.allocate 10 (.cons (.register 12) (.register 9)) (.ret [.register 10]))
        }})
      (by simp [Atom.eval, loaded, regs, loadRegisters, decoded, initialRegisters]) nodeCell infoLoad
    have fuelLoad := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 5)
      (branches := {failCases with
        nil := .ret [.register 2]
        cons := .load (.register 1) 6 7 8 {
          failCases with
          pair := .load (.register 6) 11 12 13 {
            failCases with
            pair := .call self [.register 4, .register 7, .register 2] [9]
              (.allocate 10 (.cons (.register 12) (.register 9)) (.ret [.register 10]))
          }
        }})
      (by simp [Atom.eval, regs, initialRegisters]) cell nodeLoad
    refine ⟨mid.length, final, ?_, safe.2.1, ext.trans safe.1, ?_⟩
    · rw [hcode]
      exact fuelLoad.mono (by simp [CellExpr.args, List.length_cons, Nat.mul_add]; omega)
    · simpa [trace, Program.allocate] using consAt

/-- A concrete one-procedure program traces any supplied successor table. -/
def program : Code 1 := fun _ => traceBody 0

end WeightedMIS.RegisterPermutationMirror
