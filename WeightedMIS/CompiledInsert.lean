module

public import WeightedMIS.CompiledLookup

/-! # Compilation correctness and event bound for trie insertion -/

@[expose] public section

namespace WeightedMIS.CompiledTrie

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine

theorem compile_insertLeaf {p : ℕ} (code : Code p) (h : Heap) (regs : Registers)
    (items : Atom) {a old : Ptr} (ha : regs 1 = .pointer a)
    (hi : items.eval regs = .pointer old) :
    Within code h regs (insertLeaf items) [.pointer (h.length + 1)]
      ((h ++ [.cons a old]) ++ [.bucket h.length]) 17 := by
  unfold insertLeaf
  apply Within.allocate (budget := 9) (c := .cons a old)
  · simp only [CellExpr.eval, hi]
    simp [Atom.eval, ha, Value.asPointer]
  · apply Within.allocate (budget := 3) (c := .bucket h.length)
    · simp [CellExpr.eval, Atom.eval, Value.asPointer]
    · convert Within.ret code ((h ++ [Cell.cons a old]) ++ [Cell.bucket h.length])
          (Function.update (Function.update regs 9 (.pointer h.length)) 10
            (.pointer (h ++ [Cell.cons a old]).length)) [.register 10] using 1 <;>
        simp [values, Atom.eval, List.append_assoc]

theorem compile_insertBranch {p : ℕ} {code : Code p} {self : Fin p}
    {h final : Heap} {regs : Registers} {left right : Atom} {l r tail a out : Ptr}
    {b : Bool} {budget : ℕ}
    (hk : regs 6 = .pointer tail) (ha : regs 1 = .pointer a) (hb : regs 7 = .flag b)
    (hl : left.eval regs = .pointer l) (hr : right.eval regs = .pointer r)
    (hls : ∀ v, left.eval (Function.update regs 9 v) = .pointer l)
    (hrs : ∀ v, right.eval (Function.update regs 9 v) = .pointer r)
    (child : Within code h (initialRegisters [.pointer tail, .pointer a,
        .pointer (if b then r else l)]) (code self) [.pointer out] final budget) :
    Within code h regs (insertBranch self left right) [.pointer final.length]
      (final ++ [.fork (if b then l else out) (if b then out else r)]) (budget + 21) := by
  unfold insertBranch
  have hgo : Within code h regs
      (if b then .call self [.register 6, .register 1, right] [9]
          (.allocate 10 (.fork left (.register 9)) (.ret [.register 10]))
       else .call self [.register 6, .register 1, left] [9]
          (.allocate 10 (.fork (.register 9) right) (.ret [.register 10])))
      [.pointer final.length]
      (final ++ [.fork (if b then l else out) (if b then out else r)]) (budget + 18) := by
    cases b with
    | false =>
      apply Within.mono (a := 1 + 2 * 3 + budget + 11)
      · apply Within.call (calleeBudget := budget) (restBudget := 11)
          (returned := [.pointer out]) (mid := final)
        · have hargs : values regs [.register 6, .register 1, left] =
              [.pointer tail, .pointer a, .pointer l] := by
            change [regs 6, regs 1, left.eval regs] = _
            rw [hk, ha, hl]
          simpa only [hargs, Bool.false_eq_true, ite_false] using child
        · apply Within.allocate (budget := 3) (c := .fork out r)
          · simp only [CellExpr.eval, bindResults, hrs]
            simp [Atom.eval, Value.asPointer]
          · simpa [values, Atom.eval, List.append_assoc] using
              Within.ret code (final ++ [.fork out r])
                (Function.update (bindResults regs [9] [.pointer out]) 10 (.pointer final.length))
                [.register 10]
      · omega
    | true =>
      apply Within.mono (a := 1 + 2 * 3 + budget + 11)
      · apply Within.call (calleeBudget := budget) (restBudget := 11)
          (returned := [.pointer out]) (mid := final)
        · have hargs : values regs [.register 6, .register 1, right] =
              [.pointer tail, .pointer a, .pointer r] := by
            change [regs 6, regs 1, right.eval regs] = _
            rw [hk, ha, hr]
          simpa only [hargs, ite_true] using child
        · apply Within.allocate (budget := 3) (c := .fork l out)
          · simp only [CellExpr.eval, bindResults, hls]
            simp [Atom.eval, Value.asPointer]
          · simpa [values, Atom.eval, List.append_assoc] using
              Within.ret code (final ++ [.fork l out])
                (Function.update (bindResults regs [9] [.pointer out]) 10 (.pointer final.length))
                [.register 10]
      · omega
  exact (Within.branch (show (.register 7 : Atom).eval regs = .flag b from hb) hgo).mono (by omega)

/-- A fixed finite insertion procedure refines every successful tag-directed
insertion. The bound counts interpreted register transfers, loads, writes,
branches and calls before the separate physical-stack refinement. -/
theorem compile_insert {p : ℕ} {code : Code p} {self : Fin p}
    (hcode : code self = insertBody self) {h : Heap} {key a tree : Ptr}
    {result : Run (Option Ptr)} (he : InsertEval h key a tree result) (regs : Registers)
    (hk : regs 0 = .pointer key) (ha : regs 1 = .pointer a) (ht : regs 2 = .pointer tree) :
    ∃ out, result.value = some out ∧
      Within code h regs (insertBody self) [.pointer out] result.heap (20 * result.trace.length) := by
  induction he generalizing regs with
  | @emptyLeaf key a tree root keyCell =>
    refine ⟨h.length + 1, ?_, ?_⟩
    · simp [withEvents, leafInsert, Program.allocate]
    · apply Within.mono (a := 37)
      · unfold insertBody
        apply Within.load (budget := 27) (show (.register 2 : Atom).eval regs = .pointer tree from ht) root
        apply Within.load (budget := 17) (pointer := key) (c := .nil)
        · simpa [Atom.eval, loadRegisters, decoded] using hk
        · exact keyCell
        · simpa [Cases.select, withEvents, leafInsert, Program.allocate] using
            compile_insertLeaf code h
              (loadRegisters (loadRegisters regs 3 4 5 .nil) 6 8 7 .nil) .null
              (by simpa [loadRegisters, decoded] using ha) rfl
      · simp [withEvents, readTwoBefore, leafInsert, Program.allocate, Program.load]
  | @bucketLeaf key a tree items root keyCell =>
    refine ⟨h.length + 1, ?_, ?_⟩
    · simp [withEvents, leafInsert, Program.allocate]
    · apply Within.mono (a := 37)
      · unfold insertBody
        apply Within.load (budget := 27) (show (.register 2 : Atom).eval regs = .pointer tree from ht) root
        apply Within.load (budget := 17) (pointer := key) (c := .nil)
        · simpa [Atom.eval, loadRegisters, decoded] using hk
        · exact keyCell
        · simpa [Cases.select, withEvents, leafInsert, Program.allocate] using
            compile_insertLeaf code h
              (loadRegisters (loadRegisters regs 3 4 5 (.bucket items)) 6 8 7 .nil) (.register 3)
              (by simpa [loadRegisters, decoded] using ha)
              (by simp [Atom.eval, loadRegisters, decoded])
      · simp [withEvents, readTwoBefore, leafInsert, Program.allocate, Program.load]
  | @emptyBranch key a tree tail b child root keyCell childEval ih =>
    obtain ⟨out, ho, hc⟩ := ih (initialRegisters [.pointer tail, .pointer a, .pointer 0])
      (by simp [initialRegisters]) (by simp [initialRegisters]) (by simp [initialRegisters])
    refine ⟨child.heap.length, ?_, ?_⟩
    · simp [withEvents, forkAfter, ho, Program.allocate]
    · let rs := loadRegisters (loadRegisters regs 3 4 5 .nil) 6 8 7 (.bit b tail)
      have hb := compile_insertBranch (code := code) (self := self) (h := h) (final := child.heap)
        (out := out) (budget := 20 * child.trace.length) (regs := rs) (left := .null) (right := .null)
        (l := 0) (r := 0) (tail := tail) (a := a) (b := b)
        (by simp [rs, loadRegisters, decoded])
        (by simpa [rs, loadRegisters, decoded] using ha)
        (by simp [rs, loadRegisters, decoded]) rfl rfl (by intro v; rfl) (by intro v; rfl)
        (by simpa [hcode] using hc)
      have houter : Within code h regs (insertBody self) [.pointer child.heap.length]
          (child.heap ++ [.fork (if b then 0 else out) (if b then out else 0)])
          (10 + (10 + (20 * child.trace.length + 21))) := by
        unfold insertBody
        apply Within.load (budget := 10 + (20 * child.trace.length + 21)) (show (.register 2 : Atom).eval regs = .pointer tree from ht) root
        apply Within.load (budget := 20 * child.trace.length + 21) (pointer := key) (c := .bit b tail)
        · simpa [Atom.eval, loadRegisters, decoded] using hk
        · exact keyCell
        · exact hb
      simpa [withEvents, forkAfter, ho, Program.allocate, readTwoBefore, Program.load,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        houter.mono (b := 20 * (3 + (child.trace.length + 1))) (by omega)
  | @fork key a tree tail left right b child root keyCell childEval ih =>
    obtain ⟨out, ho, hc⟩ := ih
      (initialRegisters [.pointer tail, .pointer a, .pointer (if b then right else left)])
      (by simp [initialRegisters]) (by simp [initialRegisters]) (by simp [initialRegisters])
    refine ⟨child.heap.length, ?_, ?_⟩
    · simp [withEvents, forkAfter, ho, Program.allocate]
    · let rs := loadRegisters (loadRegisters regs 3 4 5 (.fork left right)) 6 8 7 (.bit b tail)
      have hb := compile_insertBranch (code := code) (self := self) (h := h) (final := child.heap)
        (out := out) (budget := 20 * child.trace.length) (regs := rs) (left := .register 3) (right := .register 4)
        (l := left) (r := right) (tail := tail) (a := a) (b := b)
        (by simp [rs, loadRegisters, decoded])
        (by simpa [rs, loadRegisters, decoded] using ha)
        (by simp [rs, loadRegisters, decoded])
        (by simp [Atom.eval, rs, loadRegisters, decoded])
        (by simp [Atom.eval, rs, loadRegisters, decoded])
        (by intro v; simp [Atom.eval, rs, loadRegisters, decoded])
        (by intro v; simp [Atom.eval, rs, loadRegisters, decoded])
        (by simpa [hcode] using hc)
      have houter : Within code h regs (insertBody self) [.pointer child.heap.length]
          (child.heap ++ [.fork (if b then left else out) (if b then out else right)])
          (10 + (10 + (20 * child.trace.length + 21))) := by
        unfold insertBody
        apply Within.load (budget := 10 + (20 * child.trace.length + 21)) (show (.register 2 : Atom).eval regs = .pointer tree from ht) root
        apply Within.load (budget := 20 * child.trace.length + 21) (pointer := key) (c := .bit b tail)
        · simpa [Atom.eval, loadRegisters, decoded] using hk
        · exact keyCell
        · exact hb
      have hheap : (.fork (if b then left else out) (if b then out else right) : Cell) =
          .fork (if b then (if b then left else right) else out)
            (if b then out else (if b then left else right)) := by cases b <;> rfl
      simpa [withEvents, forkAfter, ho, Program.allocate, hheap, readTwoBefore, Program.load,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        houter.mono (b := 20 * (3 + (child.trace.length + 1))) (by omega)

end WeightedMIS.CompiledTrie
