module

public import WeightedMIS.CompiledTrie
public import WeightedMIS.EfficientSearchCodeBounds
public import WeightedMIS.PointerEvaluation

/-! # Compilation correctness and event bound for trie lookup -/

@[expose] public section

namespace WeightedMIS.CompiledTrie

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine

theorem call_return_pointer {p : ℕ} {code : Code p} {h final : Heap} {regs : Registers}
    {self : Fin p} {args : List Atom} {dst : Register} {out budget : ℕ}
    (body : Within code h (initialRegisters (values regs args)) (code self)
      [.pointer out] final budget) :
    Within code h regs (.call self args [dst] (.ret [.register dst])) [.pointer out] final
      (1 + 2 * args.length + budget + 3) := by
  apply Within.call (calleeBudget := budget) (restBudget := 3) body
  simpa [bindResults, values, Atom.eval] using
    Within.ret code final (bindResults regs [dst] [.pointer out]) [.register dst]

/-- The same finite lookup body works for every represented key and heap.
Its recursion target is a fixed code-table entry, not a host-function argument. -/
theorem compile_lookup {p : ℕ} {code : Code p} {self : Fin p}
    (hcode : code self = lookupBody self) {h : Heap} {key tree : Ptr} {result : Run (Option Ptr)}
    (he : LookupEval h key tree result) (regs : Registers)
    (hk : regs 0 = .pointer key) (ht : regs 1 = .pointer tree) :
    ∃ out, result.value = some out ∧
      Within code h regs (lookupBody self) [.pointer out] result.heap (20 * result.trace.length) := by
  induction he generalizing regs with
  | @empty key tree root =>
    refine ⟨0, rfl, ?_⟩
    apply Within.mono (a := 13)
    · unfold lookupBody
      apply Within.load (budget := 3) (pointer := tree) (c := .nil)
      · exact ht
      · exact root
      · simpa [Cases.select, values, Atom.eval] using
          Within.ret code h (loadRegisters regs 2 3 4 .nil) [.null]
    · simp [readBefore, Program.load]
  | @bucket key tree items root =>
    refine ⟨items, rfl, ?_⟩
    apply Within.mono (a := 13)
    · unfold lookupBody
      apply Within.load (budget := 3) (pointer := tree) (c := .bucket items)
      · exact ht
      · exact root
      · simpa [Cases.select, values, Atom.eval, loadRegisters, decoded] using
          Within.ret code h (loadRegisters regs 2 3 4 (.bucket items)) [.register 2]
    · simp [readBefore, Program.load]
  | @fork key tree left right tail b child root keyCell childEval ih =>
    obtain ⟨out, ho, hc⟩ := ih (initialRegisters [.pointer tail, .pointer (if b then right else left)])
      (by simp [initialRegisters]) (by simp [initialRegisters])
    refine ⟨out, ho, ?_⟩
    let firstRegs := loadRegisters regs 2 3 4 (.fork left right)
    let innerRegs := loadRegisters firstRegs 5 6 7 (.bit b tail)
    have htrue : Within code h innerRegs
        (if b then
          .call self [.register 5, .register 3] [8] (.ret [.register 8])
        else .call self [.register 5, .register 2] [8] (.ret [.register 8]))
        [.pointer out] child.heap (20 * child.trace.length + 8) := by
      cases b with
      | false =>
        have hcall := call_return_pointer (code := code) (h := h) (final := child.heap)
          (regs := innerRegs) (self := self) (out := out) (dst := 8) (args := [.register 5, .register 2])
          (budget := 20 * child.trace.length) (by
            simpa [hcode, values, Atom.eval, innerRegs, firstRegs, loadRegisters, decoded] using hc)
        exact hcall.mono (by simp; omega)
      | true =>
        have hcall := call_return_pointer (code := code) (h := h) (final := child.heap)
          (regs := innerRegs) (self := self) (out := out) (dst := 8) (args := [.register 5, .register 3])
          (budget := 20 * child.trace.length) (by
            simpa [hcode, values, Atom.eval, innerRegs, firstRegs, loadRegisters, decoded] using hc)
        exact hcall.mono (by simp; omega)
    have hbranch := Within.branch (code := code) (test := .register 7) (b := b)
      (show Atom.eval innerRegs (.register 7) = .flag b by simp [innerRegs, loadRegisters, decoded, Atom.eval]) htrue
    have hkeyload : Within code h firstRegs
        (.load (.register 0) 5 6 7 {failCases with bit := (.branch (.register 7)
          (.call self [.register 5, .register 3] [8] (.ret [.register 8]))
          (.call self [.register 5, .register 2] [8] (.ret [.register 8])))})
        [.pointer out] child.heap (10 + (3 + (20 * child.trace.length + 8))) := by
      apply Within.load (budget := 3 + (20 * child.trace.length + 8)) (pointer := key) (c := .bit b tail)
      · simpa [Atom.eval, firstRegs, loadRegisters, decoded] using hk
      · exact keyCell
      · exact hbranch
    have houter : Within code h regs (lookupBody self) [.pointer out] child.heap
        (10 + (10 + (3 + (20 * child.trace.length + 8)))) := by
      unfold lookupBody
      apply Within.load (budget := 10 + (3 + (20 * child.trace.length + 8))) (pointer := tree)
        (c := .fork left right)
      · exact ht
      · exact root
      · exact hkeyload
    apply houter.mono
    simp [withEvents, readTwoBefore, Program.load]
    omega

end WeightedMIS.CompiledTrie
