module

public import WeightedMIS.EfficientSearchPointerData
public import WeightedMIS.EfficientSearchCodeBounds
public import WeightedMIS.RegisterMachineFrames

/-!
# Reading edge labels from the computed predecessor chain

The finite procedure follows the actual list and record tags. It returns a
list of the allocated edge-label pointers, in the order of the reverse path.
Each predecessor requires four loads and one list allocation. The execution
bound includes all register transfers and procedure calls.
-/

@[expose] public section

namespace WeightedMIS.RegisterPathLabels

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.EfficientSearch.Pointer

variable {p : ℕ}

def pairCases (next : Command p) : Cases (Command p) :=
  ⟨.fail, .fail, .fail, .fail, .fail, next⟩

def afterLabel (self : Fin p) : Command p :=
  .call self [.register 2] [7]
    (.allocate 8 (.cons (.register 6) (.register 7)) (.ret [.register 8]))

def readLabel (self : Fin p) : Command p :=
  .load (.register 5) 3 6 15 (pairCases (afterLabel self))

def readArc (self : Fin p) : Command p :=
  .load (.register 4) 3 5 15 (pairCases (readLabel self))

def readRaw (self : Fin p) : Command p :=
  .load (.register 1) 3 4 15 (pairCases (readArc self))

def labelsBody (self : Fin p) : Command p :=
  .load (.register 0) 1 2 15
    ⟨.ret [.null], .fail, readRaw self, .fail, .fail, .fail⟩

theorem compiled_aux (code : Code p) (self : Fin p)
    (body : code self = labelsBody self)
    {h : Heap} (hh : Valid h) {pp : Ptr} {pointers : List Ptr} (hl : ListAt h pp pointers)
    {vbits cbits : ℕ} {path : Trace Ptr vbits cbits}
    (hr : List.Forall₂ (RawArcAt h) pointers path) :
    ∃ out final, Within code h (initialRegisters [.pointer pp]) (code self)
      [.pointer out] final (54 * path.length + 13) ∧
      Extends h final ∧ ListAt final out (path.map (fun a => a.2.label)) := by
  induction hl generalizing path with
  | @nil pp cell =>
    cases hr
    refine ⟨0, h, ?_, Extends.refl h, ?_⟩
    · rw [body]
      have last := Within.ret code h
        (loadRegisters (initialRegisters [.pointer pp]) 1 2 15 .nil) [.null]
      exact Within.load (address := .register 0) (first := 1) (second := 2) (bit := 15)
        (branches := ⟨.ret [.null], .fail, readRaw self, .fail, .fail, .fail⟩)
        (by simp [Atom.eval, initialRegisters]) cell last
    · exact .nil hh.1
  | @cons pp ap tail pointers cell rest ih =>
    cases hr with
    | @cons _ edge _ path arc arcs =>
      obtain ⟨source, ep, rawCell, sourceAt, edgeAt⟩ := arc
      obtain ⟨target, weightLabel, weight, edgeCell, weightCell, targetAt, weightAt, labelAt⟩ := edgeAt
      obtain ⟨out, final, child, extension, resultAt⟩ := ih arcs
      let r0 := initialRegisters [Value.pointer pp]
      let r1 := loadRegisters r0 1 2 15 (.cons ap tail)
      let r2 := loadRegisters r1 3 4 15 (.pair source ep)
      let r3 := loadRegisters r2 3 5 15 (.pair target weightLabel)
      let r4 := loadRegisters r3 3 6 15 (.pair weight edge.2.label)
      let r5 := bindResults r4 [7] [Value.pointer out]
      have last : Within code (final ++ [.cons edge.2.label out])
          (Function.update r5 8 (.pointer final.length)) (.ret [.register 8])
          [.pointer final.length] (final ++ [.cons edge.2.label out]) 3 := by
        simpa [values, Atom.eval] using Within.ret code
          (final ++ [.cons edge.2.label out])
          (Function.update r5 8 (.pointer final.length)) [.register 8]
      have alloc := Within.allocate (dst := 8)
        (expr := .cons (.register 6) (.register 7))
        (by simp [CellExpr.eval, Atom.eval, r5, r4, bindResults, loadRegisters,
          decoded, Value.asPointer]) last
      have call := Within.call (procedure := self) (arguments := [.register 2])
        (results := [7]) (regs := r4) (returned := [.pointer out])
        (by simpa [values, Atom.eval, r4, r3, r2, r1, loadRegisters, decoded] using child) alloc
      have l4 := Within.load (address := .register 5) (first := 3) (second := 6) (bit := 15)
        (branches := pairCases (afterLabel self))
        (by simp [Atom.eval, r3, loadRegisters, decoded]) weightCell call
      have l3 := Within.load (address := .register 4) (first := 3) (second := 5) (bit := 15)
        (branches := pairCases (readLabel self))
        (by simp [Atom.eval, r2, loadRegisters, decoded]) edgeCell l4
      have l2 := Within.load (address := .register 1) (first := 3) (second := 4) (bit := 15)
        (branches := pairCases (readArc self))
        (by simp [Atom.eval, r1, loadRegisters, decoded]) rawCell l3
      have l1 := Within.load (address := .register 0) (first := 1) (second := 2) (bit := 15)
        (branches := ⟨.ret [.null], .fail, readRaw self, .fail, .fail, .fail⟩)
        (by simp [Atom.eval, r0, initialRegisters]) cell l2
      refine ⟨final.length, final ++ [.cons edge.2.label out], ?_,
        extension.trans ⟨_, rfl⟩, ?_⟩
      · rw [body]
        exact l1.mono (by simp [CellExpr.args]; omega)
      · exact .cons (by simp) (resultAt.mono ⟨_, rfl⟩)

/-- The output list is read from the actual computed predecessor records. -/
theorem compiled (code : Code p) (self : Fin p)
    (body : code self = labelsBody self)
    {h : Heap} (hh : Valid h) {pp : Ptr} {vbits cbits : ℕ}
    {path : Trace Ptr vbits cbits} (hp : TraceAt h pp path) :
    ∃ out final, Within code h (initialRegisters [.pointer pp]) (code self)
      [.pointer out] final (54 * path.length + 13) ∧
      Extends h final ∧ ListAt final out (path.map (fun a => a.2.label)) := by
  obtain ⟨pointers, hl, hr⟩ := hp
  exact compiled_aux code self body hh hl hr

end WeightedMIS.RegisterPathLabels
