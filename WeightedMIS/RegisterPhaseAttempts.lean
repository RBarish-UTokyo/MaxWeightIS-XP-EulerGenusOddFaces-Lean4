module

public import WeightedMIS.CompiledTrie
public import WeightedMIS.EfficientSearchCodeBounds
public import WeightedMIS.ExpandedWords
public import WeightedMIS.MaxFlowScaling

/-!
# Finite construction of the capacity-scaling attempt list

The phase compiler consumes an actual linked list whose length is the phase
fuel `2 * N^2 + 1`, where `N` is the number of vertices. This module builds that
list from the represented vertex list without arithmetic instructions.

* The inner procedure, inputs `[innerList, source, accumulator]`, prepends two
  cons cells holding the source word pointer for every element of the inner list.
* The outer procedure, inputs `[outerList, nodesList, source, accumulator]`, calls
  the inner procedure on the full node list once for every element of the outer list.
* The entry procedure, inputs `[nodesList, source]`, allocates the singleton
  list `[source]` and calls the outer procedure with the node list as both lists.

All entries of the result share the supplied source word pointer. The exact
output is `List.replicate (2 * N^2 + 1) source`, with an explicit quadratic
event bound.
-/

@[expose] public section

namespace WeightedMIS.RegisterPhaseAttempts

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords

structure Procedures (p : ℕ) where
  inner : Fin p
  outer : Fin p
  entry : Fin p

variable {p : ℕ}

/-- Inputs: inner list, source word, accumulator. -/
def innerBody (self : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.register 2]
    cons := .allocate 5 (.cons (.register 1) (.register 2))
      (.allocate 6 (.cons (.register 1) (.register 5))
        (.call self [.register 4, .register 1, .register 6] [7] (.ret [.register 7]))) }

/-- Inputs: outer list, node list, source word, accumulator. -/
def outerBody (self inner : Fin p) : Command p :=
  .load (.register 0) 4 5 15 { CompiledTrie.failCases with
    nil := .ret [.register 3]
    cons := .call inner [.register 1, .register 2, .register 3] [6]
      (.call self [.register 5, .register 1, .register 2, .register 6] [7] (.ret [.register 7])) }

/-- Inputs: node list, source word. Output: the attempt list. -/
def entryBody (outer : Fin p) : Command p :=
  .allocate 2 (.cons (.register 1) .null)
    (.call outer [.register 0, .register 0, .register 1, .register 2] [3] (.ret [.register 3]))

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  code d.inner = innerBody d.inner ∧
  code d.outer = outerBody d.outer d.inner ∧
  code d.entry = entryBody d.outer

def innerBudget (length : ℕ) : ℕ := 36 * length + 13

def outerBudget (nodes length : ℕ) : ℕ := (36 * nodes + 42) * length + 13

def budget (nodes : ℕ) : ℕ := 80 * (nodes + 1) ^ 2

theorem replicate_two_succ {α : Type*} (m : ℕ) (s : α) (acc : List α) :
    List.replicate (2 * m) s ++ s :: s :: acc = List.replicate (2 * (m + 1)) s ++ acc := by
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, List.replicate_succ', List.replicate_succ']
  simp [List.append_assoc]

theorem replicate_block {α : Type*} (block m : ℕ) (s : α) (acc : List α) :
    List.replicate (block * m) s ++ (List.replicate block s ++ acc) =
      List.replicate (block * (m + 1)) s ++ acc := by
  rw [Nat.mul_succ, List.replicate_add, List.append_assoc]

theorem inner_compiled (code : Code p) (self : Fin p) (hself : code self = innerBody self)
    {k n : ℕ} {h : Heap} (hh : Valid h) {lp sp ap : Ptr} {xs : List (Bits k)}
    {source : Bits n} {acc : List (Bits n)}
    (hl : WordsAt h lp xs) (hs : BitsAt h sp source) (ha : WordsAt h ap acc) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q (List.replicate (2 * xs.length) source ++ acc) ∧
      Within code h (initialRegisters [.pointer lp, .pointer sp, .pointer ap])
        (code self) [.pointer q] out (innerBudget xs.length) := by
  induction xs generalizing h lp ap acc with
  | nil =>
    have cell := WordsAt.nil_iff.mp hl
    refine ⟨h, ap, .refl h, hh, by simpa using ha, ?_⟩
    rw [hself]
    unfold innerBody
    apply Within.load (budget := 3) (pointer := lp) (c := .nil)
    · simp [Atom.eval, initialRegisters]
    · exact cell
    · simpa [values, Atom.eval, loadRegisters, decoded, initialRegisters, Cases.select] using
        Within.ret code h
          (loadRegisters (initialRegisters [.pointer lp, .pointer sp, .pointer ap]) 3 4 15 .nil)
          [.register 2]
  | cons x xs ih =>
    obtain ⟨xp, tp, cell, _, htail⟩ := WordsAt.cons_iff.mp hl
    have a1 := allocate_word_cons hh hs ha
    have e1 : Extends h (h ++ [Cell.cons sp ap]) := a1.1.1
    have v1 : Valid (h ++ [Cell.cons sp ap]) := a1.1.2.1
    have a2 := allocate_word_cons v1 (hs.mono e1) a1.2
    have e2 : Extends (h ++ [Cell.cons sp ap])
        (h ++ [Cell.cons sp ap] ++ [Cell.cons sp h.length]) := a2.1.1
    have v2 : Valid (h ++ [Cell.cons sp ap] ++ [Cell.cons sp h.length]) := a2.1.2.1
    obtain ⟨out, q, he, hv, hw, child⟩ :=
      ih v2 (htail.mono (e1.trans e2)) (hs.mono (e1.trans e2)) a2.2
    refine ⟨out, q, e1.trans (e2.trans he), hv, ?_, ?_⟩
    · simpa only [List.length_cons, replicate_two_succ] using hw
    · let regs := initialRegisters [Value.pointer lp, .pointer sp, .pointer ap]
      let r1 := loadRegisters regs 3 4 15 (.cons xp tp)
      let r2 := Function.update r1 5 (.pointer h.length)
      let r3 := Function.update r2 6 (.pointer (h ++ [Cell.cons sp ap]).length)
      let r4 := bindResults r3 [7] [.pointer q]
      have ret : Within code out r4 (.ret [.register 7]) [.pointer q] out 3 := by
        simpa [values, Atom.eval, r4, bindResults] using Within.ret code out r4 [.register 7]
      have args : values r3 [.register 4, .register 1, .register 6] =
          [.pointer tp, .pointer sp, .pointer (h ++ [Cell.cons sp ap]).length] := by
        simp [values, Atom.eval, r3, r2, r1, regs, loadRegisters, decoded, initialRegisters]
      have call := Within.call (procedure := self) (regs := r3)
        (arguments := [.register 4, .register 1, .register 6]) (results := [7])
        (by simpa only [args] using child) ret
      have alloc2 := Within.allocate (h := h ++ [Cell.cons sp ap]) (regs := r2) (dst := 6)
        (expr := .cons (.register 1) (.register 5)) (c := .cons sp h.length)
        (by simp [CellExpr.eval, Atom.eval, r2, r1, regs, loadRegisters, decoded,
          initialRegisters, Value.asPointer]) call
      have alloc1 := Within.allocate (h := h) (regs := r1) (dst := 5)
        (expr := .cons (.register 1) (.register 2)) (c := .cons sp ap)
        (by simp [CellExpr.eval, Atom.eval, r1, regs, loadRegisters, decoded,
          initialRegisters, Value.asPointer]) alloc2
      have loaded := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
        (branches := { CompiledTrie.failCases with
          nil := .ret [.register 2]
          cons := .allocate 5 (.cons (.register 1) (.register 2))
            (.allocate 6 (.cons (.register 1) (.register 5))
              (.call self [.register 4, .register 1, .register 6] [7] (.ret [.register 7]))) })
        (by simp [Atom.eval, regs, initialRegisters]) cell alloc1
      simpa only [hself, innerBody] using
        loaded.mono (b := innerBudget (x :: xs).length)
          (by simp only [innerBudget, CellExpr.args, List.length_cons, List.length_nil]; omega)

theorem outer_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {k n : ℕ} {h : Heap} (hh : Valid h) {op np sp ap : Ptr} {outer nodes : List (Bits k)}
    {source : Bits n} {acc : List (Bits n)}
    (ho : WordsAt h op outer) (hn : WordsAt h np nodes) (hs : BitsAt h sp source)
    (ha : WordsAt h ap acc) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q (List.replicate (2 * nodes.length * outer.length) source ++ acc) ∧
      Within code h (initialRegisters [.pointer op, .pointer np, .pointer sp, .pointer ap])
        (code d.outer) [.pointer q] out (outerBudget nodes.length outer.length) := by
  obtain ⟨hinner, houter, _⟩ := hm
  induction outer generalizing h op ap acc with
  | nil =>
    have cell := WordsAt.nil_iff.mp ho
    refine ⟨h, ap, .refl h, hh, by simpa using ha, ?_⟩
    rw [houter]
    unfold outerBody
    apply Within.load (budget := 3) (pointer := op) (c := .nil)
    · simp [Atom.eval, initialRegisters]
    · exact cell
    · simpa [values, Atom.eval, loadRegisters, decoded, initialRegisters, Cases.select] using
        Within.ret code h
          (loadRegisters (initialRegisters [.pointer op, .pointer np, .pointer sp, .pointer ap])
            4 5 15 .nil) [.register 3]
  | cons x xs ih =>
    obtain ⟨xp, tp, cell, _, htail⟩ := WordsAt.cons_iff.mp ho
    obtain ⟨mid, q1, he1, hv1, hw1, innerRun⟩ := inner_compiled code d.inner hinner hh hn hs ha
    obtain ⟨out, q, he2, hv2, hw2, child⟩ :=
      ih hv1 (htail.mono he1) (hn.mono he1) (hs.mono he1) hw1
    refine ⟨out, q, he1.trans he2, hv2, ?_, ?_⟩
    · simpa only [List.length_cons, replicate_block] using hw2
    · let regs := initialRegisters [Value.pointer op, .pointer np, .pointer sp, .pointer ap]
      let r1 := loadRegisters regs 4 5 15 (.cons xp tp)
      let r2 := bindResults r1 [6] [.pointer q1]
      let r3 := bindResults r2 [7] [.pointer q]
      have ret : Within code out r3 (.ret [.register 7]) [.pointer q] out 3 := by
        simpa [values, Atom.eval, r3, bindResults] using Within.ret code out r3 [.register 7]
      have argsR : values r2 [.register 5, .register 1, .register 2, .register 6] =
          [.pointer tp, .pointer np, .pointer sp, .pointer q1] := by
        simp [values, Atom.eval, r2, r1, regs, bindResults, loadRegisters, decoded,
          initialRegisters]
      have recurse := Within.call (procedure := d.outer) (regs := r2)
        (arguments := [.register 5, .register 1, .register 2, .register 6]) (results := [7])
        (by simpa only [argsR] using child) ret
      have argsI : values r1 [.register 1, .register 2, .register 3] =
          [.pointer np, .pointer sp, .pointer ap] := by
        simp [values, Atom.eval, r1, regs, loadRegisters, decoded, initialRegisters]
      have icall := Within.call (procedure := d.inner) (regs := r1)
        (arguments := [.register 1, .register 2, .register 3]) (results := [6])
        (by simpa only [argsI] using innerRun) recurse
      have loaded := Within.load (address := .register 0) (first := 4) (second := 5) (bit := 15)
        (branches := { CompiledTrie.failCases with
          nil := .ret [.register 3]
          cons := .call d.inner [.register 1, .register 2, .register 3] [6]
            (.call d.outer [.register 5, .register 1, .register 2, .register 6] [7]
              (.ret [.register 7])) })
        (by simp [Atom.eval, regs, initialRegisters]) cell icall
      simpa only [houter, outerBody] using
        loaded.mono (b := outerBudget nodes.length (x :: xs).length)
          (by simp only [outerBudget, innerBudget, List.length_cons, List.length_nil, Nat.mul_add,
            Nat.mul_one]; omega)

theorem entry_budget_le (N : ℕ) : 20 + outerBudget N N ≤ budget N := by
  simp only [outerBudget, budget]
  nlinarith

/-- The constructed attempt list has exactly the phase-fuel length. -/
theorem attempts_length {α : Type*} (N : ℕ) (s : α) :
    (List.replicate (2 * N ^ 2 + 1) s).length = 2 * N ^ 2 + 1 := List.length_replicate

theorem attempts_length_phaseFuel {α β : Type*} (V : Type*) [Fintype V] (nodes : List β)
    (hN : nodes.length = Fintype.card V) (s : α) :
    (List.replicate (2 * nodes.length ^ 2 + 1) s).length = MaxFlowScaling.phaseFuel V := by
  simp [MaxFlowScaling.phaseFuel, hN]

/-- The entry procedure builds `2 * N^2 + 1` copies of the source word pointer. -/
theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {k n : ℕ} {h : Heap} (hh : Valid h) {np sp : Ptr} {nodes : List (Bits k)}
    {source : Bits n} (hn : WordsAt h np nodes) (hs : BitsAt h sp source) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q (List.replicate (2 * nodes.length ^ 2 + 1) source) ∧
      Within code h (initialRegisters [.pointer np, .pointer sp])
        (code d.entry) [.pointer q] out (budget nodes.length) := by
  have hentry := hm.2.2
  have a1 := allocate_word_cons hh hs (WordsAt.nil hh.1 : WordsAt h 0 ([] : List (Bits n)))
  have e1 : Extends h (h ++ [Cell.cons sp 0]) := a1.1.1
  have v1 : Valid (h ++ [Cell.cons sp 0]) := a1.1.2.1
  obtain ⟨out, q, he, hv, hw, outerRun⟩ :=
    outer_compiled code d hm v1 (hn.mono e1) (hn.mono e1) (hs.mono e1) a1.2
  refine ⟨out, q, e1.trans he, hv, ?_, ?_⟩
  · have hlen : 2 * nodes.length * nodes.length = 2 * nodes.length ^ 2 := by ring
    rw [hlen, ← List.replicate_succ'] at hw
    exact hw
  · let regs := initialRegisters [Value.pointer np, .pointer sp]
    let r1 := Function.update regs 2 (.pointer h.length)
    let r2 := bindResults r1 [3] [.pointer q]
    have ret : Within code out r2 (.ret [.register 3]) [.pointer q] out 3 := by
      simpa [values, Atom.eval, r2, bindResults] using Within.ret code out r2 [.register 3]
    have args : values r1 [.register 0, .register 0, .register 1, .register 2] =
        [.pointer np, .pointer np, .pointer sp, .pointer h.length] := by
      simp [values, Atom.eval, r1, regs, initialRegisters]
    have call := Within.call (procedure := d.outer) (regs := r1)
      (arguments := [.register 0, .register 0, .register 1, .register 2]) (results := [3])
      (by simpa only [args] using outerRun) ret
    have alloc := Within.allocate (h := h) (regs := regs) (dst := 2)
      (expr := .cons (.register 1) .null) (c := .cons sp 0)
      (by simp [CellExpr.eval, Atom.eval, regs, initialRegisters, Value.asPointer]) call
    have hb := entry_budget_le nodes.length
    simpa only [hentry, entryBody] using
      alloc.mono (b := budget nodes.length)
        (by simp only [CellExpr.args, List.length_cons, List.length_nil]; omega)

end WeightedMIS.RegisterPhaseAttempts
