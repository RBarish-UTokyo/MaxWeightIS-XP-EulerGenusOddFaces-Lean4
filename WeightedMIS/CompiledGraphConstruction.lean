module

public import WeightedMIS.RadixConstruction
public import WeightedMIS.CompiledInsert
public import WeightedMIS.EfficientSearchPointerEvaluation
public import WeightedMIS.RegisterMachineFrames

/-!
# Finite register construction of the sparse graph table

The procedure consumes an explicit list of source/arc records. It recursively
builds the tail table and inserts the current arc with the compiled radix
inserter. Its instruction count is linear in the number of entries times the
binary vertex-key width; no dense table of vertex pairs is constructed.
-/

@[expose] public section

namespace WeightedMIS.CompiledGraphConstruction

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.CompiledTrie

variable {p : ℕ}

def afterRecord (self insert : Fin p) : Command p :=
  .call self [.register 3, .register 1] [6]
    (.call insert [.register 4, .register 5, .register 6] [7] (.ret [.register 7]))

def graphBody (self insert : Fin p) : Command p :=
  .load (.register 0) 2 3 15 {
    failCases with
    nil := .ret [.register 1]
    cons := .load (.register 2) 4 5 15 {failCases with pair := afterRecord self insert}
  }

theorem compiled_aux (code : Code p) (self insert : Fin p)
    (body : code self = graphBody self insert) (inserter : code insert = insertBody insert)
    {h : Heap} (hh : Valid h) {pp : Ptr} {pointers : List Ptr} (hl : ListAt h pp pointers)
    {vbits cbits : ℕ} {entries : List (RawArc Ptr vbits cbits)}
    (hr : List.Forall₂ (RawArcAt h) pointers entries)
    {gp : Ptr} {graph : Graph Ptr vbits cbits} (hg : GraphAt h gp graph) :
    ∃ out final, Within code h (initialRegisters [.pointer pp, .pointer gp]) (code self)
      [.pointer out] final ((80 * vbits + 135) * entries.length + 13) ∧
      Valid final ∧ Extends h final ∧ GraphAt final out (Radix.insertEntries entries graph) := by
  induction hl generalizing entries with
  | @nil pp cell =>
    cases hr
    refine ⟨gp, h, ?_, hh, Extends.refl h, hg⟩
    rw [body]
    have last : Within code h
        (loadRegisters (initialRegisters [.pointer pp, .pointer gp]) 2 3 15 .nil)
        (.ret [.register 1]) [.pointer gp] h 3 := by
      simpa [values, Atom.eval, loadRegisters, decoded, initialRegisters] using
        Within.ret code h
          (loadRegisters (initialRegisters [.pointer pp, .pointer gp]) 2 3 15 .nil) [.register 1]
    exact Within.load (address := .register 0) (first := 2) (second := 3) (bit := 15)
      (branches := ⟨.ret [.register 1], .fail,
        .load (.register 2) 4 5 15 {failCases with pair := afterRecord self insert},
        .fail, .fail, .fail⟩)
      (by simp [Atom.eval, initialRegisters]) cell last
  | @cons pp ap tail pointers cell rest ih =>
    cases hr with
    | @cons _ entry _ entries arc arcs =>
      obtain ⟨source, ep, rawCell, sourceAt, edgeAt⟩ := arc
      obtain ⟨midPtr, mid, child, midValid, extension, midGraph⟩ := ih arcs
      have hk := sourceAt.mono extension
      have ha := edgeAt.mono extension
      obtain ⟨safe, out, value, resultGraph, cost⟩ := insert_tree_refines
        (R := ArcAt) (fun he _ _ hv => hv.mono he) midValid hk ha ha.allocated midGraph
      have eval := insert_tree_eval (ap := ep) midValid hk midGraph
      let r0 := initialRegisters [Value.pointer pp, .pointer gp]
      let r1 := loadRegisters r0 2 3 15 (.cons ap tail)
      let r2 := loadRegisters r1 4 5 15 (.pair source ep)
      let r3 := bindResults r2 [6] [Value.pointer midPtr]
      let r4 := bindResults r3 [7] [Value.pointer out]
      let result := insertPointer vbits source ep midPtr mid
      obtain ⟨compiledOut, compiledValue, compiledInsert⟩ := compile_insert inserter eval
        (initialRegisters [Value.pointer source, .pointer ep, .pointer midPtr])
        (by simp [initialRegisters]) (by simp [initialRegisters]) (by simp [initialRegisters])
      have heq : compiledOut = out := Option.some.inj (compiledValue.symm.trans value)
      subst compiledOut
      have hargs : values r3 [.register 4, .register 5, .register 6] =
          [Value.pointer source, .pointer ep, .pointer midPtr] := by
        simp [values, Atom.eval, r3, r2, bindResults, loadRegisters, decoded]
      have compiledInsert' : Within code mid
          (initialRegisters (values r3 [.register 4, .register 5, .register 6]))
          (code insert) [.pointer out] result.heap (80 * vbits + 100) := by
        rw [hargs, inserter]
        apply compiledInsert.mono
        rw [cost, Radix.insert_steps]
        omega
      have last : Within code result.heap r4 (.ret [.register 7])
          [.pointer out] result.heap 3 := by
        simpa [values, Atom.eval, r4, bindResults] using
          Within.ret code result.heap r4 [.register 7]
      have insertCall := Within.call (procedure := insert)
        (arguments := [.register 4, .register 5, .register 6]) (results := [7])
        (regs := r3) compiledInsert' last
      have selfCall := Within.call (procedure := self)
        (arguments := [.register 3, .register 1]) (results := [6]) (regs := r2)
        (by simpa [values, Atom.eval, r2, r1, r0, loadRegisters, decoded,
          initialRegisters] using child) insertCall
      have recordLoad := Within.load (address := .register 2)
        (first := 4) (second := 5) (bit := 15)
        (branches := {failCases with pair := afterRecord self insert})
        (by simp [Atom.eval, r1, loadRegisters, decoded]) rawCell selfCall
      have listLoad := Within.load (address := .register 0)
        (first := 2) (second := 3) (bit := 15)
        (branches := ⟨.ret [.register 1], .fail,
          .load (.register 2) 4 5 15 {failCases with pair := afterRecord self insert},
          .fail, .fail, .fail⟩)
        (by simp [Atom.eval, r0, initialRegisters]) cell recordLoad
      refine ⟨out, result.heap, ?_, safe.2.1, extension.trans safe.1, resultGraph⟩
      rw [body]
      exact listLoad.mono (by simp [List.length_cons, Nat.mul_add]; omega)

theorem compiled (code : Code p) (self insert : Fin p)
    (body : code self = graphBody self insert) (inserter : code insert = insertBody insert)
    {h : Heap} (hh : Valid h) {pp : Ptr} {vbits cbits : ℕ}
    {entries : List (RawArc Ptr vbits cbits)} (hp : TraceAt h pp entries) :
    ∃ out final, Within code h (initialRegisters [.pointer pp, .pointer 0]) (code self)
      [.pointer out] final ((80 * vbits + 135) * entries.length + 13) ∧
      Valid final ∧ Extends h final ∧ GraphAt final out (Radix.fromEntries entries) := by
  obtain ⟨pointers, hl, hr⟩ := hp
  exact compiled_aux code self insert body inserter hh hl hr
    ⟨.empty, .empty hh.1, .empty⟩

end WeightedMIS.CompiledGraphConstruction
