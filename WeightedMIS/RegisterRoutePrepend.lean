module

public import WeightedMIS.RegisterRouteLookup

/-! # Constant-cost extension of the materialized route table -/

@[expose] public section

namespace WeightedMIS.RegisterRouteLookup

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords

def prependBody {p : ℕ} : Command p :=
  .allocate 3 (.pair (.register 0) (.register 1))
    (.allocate 4 (.cons (.register 3) (.register 2)) (.ret [.register 4]))

theorem prepend_compiled {p n b : ℕ} (code : Code p) (self : Fin p)
    (hself : code self = prependBody) {h : Heap} (hh : Valid h)
    {kp pp rp : Ptr} {key : Bits n} {path : List (Arc n b)} {routes : List (Route n b)}
    (hk : BitsAt h kp key) (hp : TableAt h pp path) (hr : RoutesAt h rp routes) :
    ∃ out result, Extends h out ∧ Valid out ∧
      RoutesAt out result ((key, path) :: routes) ∧ out.length = h.length + 2 ∧
      Within code h (initialRegisters [.pointer kp, .pointer pp, .pointer rp]) (code self)
        [.pointer result] out 19 := by
  let first := h ++ [.pair kp pp]
  have hs := safe_allocate h hh (.pair kp pp) (by
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hk.allocated
    · exact hp.allocated)
  have he1 : Extends h first := hs.1
  have hv1 : Valid first := hs.2.1
  have record : RouteAt first h.length (key, path) :=
    ⟨kp, pp, by simp [first], hk.mono he1, hp.mono he1⟩
  have ht := safe_allocate first hv1 (.cons h.length rp) (by
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact record.allocated
    · exact (hr.mono he1).allocated)
  let out := first ++ [.cons h.length rp]
  have he2 : Extends first out := ht.1
  have repr : RoutesAt out first.length ((key, path) :: routes) :=
    RoutesAt.cons (by simp [out]) (record.mono he2) (hr.mono (he1.trans he2))
  refine ⟨out, first.length, he1.trans he2, ht.2.1, repr, ?_, ?_⟩
  · simp [out, first]
  · let regs := initialRegisters [Value.pointer kp, .pointer pp, .pointer rp]
    let regs1 := Function.update regs 3 (Value.pointer h.length)
    let regs2 := Function.update regs1 4 (Value.pointer first.length)
    have last : Within code out regs2 (.ret [.register 4]) [.pointer first.length] out 3 := by
      simpa [regs2, values, Atom.eval] using Within.ret code out regs2 [.register 4]
    have alloc2 := Within.allocate (dst := 4) (expr := .cons (.register 3) (.register 2))
      (by simp [regs1, regs, initialRegisters, CellExpr.eval, Atom.eval, Value.asPointer]) last
    have alloc1 := Within.allocate (dst := 3) (expr := .pair (.register 0) (.register 1))
      (by simp [regs, initialRegisters, CellExpr.eval, Atom.eval, Value.asPointer]) alloc2
    rw [hself]
    simpa [prependBody, CellExpr.args] using alloc1

end WeightedMIS.RegisterRouteLookup
