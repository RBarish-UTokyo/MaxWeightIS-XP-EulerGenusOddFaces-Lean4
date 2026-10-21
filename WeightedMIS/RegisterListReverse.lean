module

public import WeightedMIS.RegisterListCommon

/-!
# Reversing a linked list onto an accumulator

The command body traverses actual cons cells and allocates one new `cons`
cell per item onto the accumulator, sharing the item addresses. Item values
are never copied and the accumulator is never traversed. The theorem refines
`List.reverse` followed by append.
-/

@[expose] public section

namespace WeightedMIS.RegisterListReverse

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer

variable {p : ℕ}

/-- Arguments 0=list, 1=accumulator; the result is the reversed list on the accumulator. -/
def body (self : Fin p) : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    nil := .ret [.register 1]
    cons := .allocate 4 (.cons (.register 2) (.register 1))
      (.call self [.register 3, .register 4] [5] (.ret [.register 5])) }

theorem compiled {α : Type*} (code : Code p) (self : Fin p) (hself : code self = body self)
    (R : Heap → Ptr → α → Prop)
    (mono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, R h ptr x → R h' ptr x)
    {h : Heap} (hh : Valid h) {list acc : Ptr} {xs ys : List α}
    (hl : ListRep R h list xs) (ha : ListRep R h acc ys) :
    ∃ out q, Extends h out ∧ Valid out ∧ ListRep R out q (xs.reverse ++ ys) ∧
      Within code h (initialRegisters [.pointer list, .pointer acc])
        (code self) [.pointer q] out (26 * xs.length + 13) := by
  induction xs generalizing h list acc ys with
  | nil =>
    obtain ⟨pointers, hlist, hrel⟩ := hl
    cases hrel
    cases hlist with
    | nil cell =>
      refine ⟨h, acc, .refl h, hh, by simpa using ha, ?_⟩
      rw [hself]
      unfold body
      apply Within.load (budget := 3) (pointer := list) (c := .nil)
      · simp [Atom.eval, initialRegisters]
      · exact cell
      · simpa [values, Atom.eval, loadRegisters, decoded, initialRegisters, Cases.select] using
          Within.ret code h
            (loadRegisters (initialRegisters [.pointer list, .pointer acc]) 2 3 15 .nil)
            [.register 1]
  | cons x xs ih =>
    obtain ⟨pointers, hlist, hrel⟩ := hl
    cases hrel with
    | @cons xp _ ps _ hx hxs =>
    cases hlist with
    | @cons _ _ rest _ cell hrest =>
    obtain ⟨hext, hv, hrep⟩ := RegisterListCommon.allocate_consRep mono hh hx
      (RegisterListCommon.ListAt.head_allocated hh cell) ha
    obtain ⟨out, q, heout, ho, hq, hc⟩ := ih hv
      (ListRep.mono hext (mono hext) ⟨ps, hrest, hxs⟩) hrep
    refine ⟨out, q, hext.trans heout, ho, by simpa using hq, ?_⟩
    let regs := initialRegisters [Value.pointer list, .pointer acc]
    let rs := loadRegisters regs 2 3 15 (.cons xp rest)
    let rt := Function.update rs 4 (.pointer h.length)
    let ru := bindResults rt [5] [.pointer q]
    have ret : Within code out ru (.ret [.register 5]) [.pointer q] out 3 := by
      simpa [values, Atom.eval, ru, bindResults] using Within.ret code out ru [.register 5]
    have sargs : values rt [.register 3, .register 4] = [.pointer rest, .pointer h.length] := by
      simp [values, Atom.eval, rt, rs, loadRegisters, decoded]
    have scall := Within.call (procedure := self)
      (arguments := [.register 3, .register 4]) (results := [5]) (regs := rt)
      (by simpa only [sargs] using hc) ret
    have alloc := Within.allocate (regs := rs) (dst := 4)
      (expr := .cons (.register 2) (.register 1)) (c := .cons xp acc)
      (by simp [CellExpr.eval, Atom.eval, rs, regs, loadRegisters, decoded, initialRegisters,
        Value.asPointer]) scall
    have loaded := Within.load (address := .register 0) (first := 2) (second := 3) (bit := 15)
      (branches := {CompiledTrie.failCases with
        nil := .ret [.register 1]
        cons := .allocate 4 (.cons (.register 2) (.register 1))
          (.call self [.register 3, .register 4] [5] (.ret [.register 5]))})
      (by simp [Atom.eval, regs, initialRegisters]) cell alloc
    simpa only [hself, body] using
      loaded.mono (b := 26 * (x :: xs).length + 13) (by simp [CellExpr.args]; omega)

end WeightedMIS.RegisterListReverse
