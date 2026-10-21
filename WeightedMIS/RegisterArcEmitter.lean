module

public import WeightedMIS.ExpandedRecords
public import WeightedMIS.EfficientSearchCodeBounds

/-! # Constant-size finite code emitting an expanded-graph arc -/

@[expose] public section

namespace WeightedMIS.RegisterArcEmitter

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords

/-- Arguments: source key, target key, shared weight/label pair, accumulator.
Three allocations prepend the actual raw arc to the accumulator list. -/
def emitBody {p : ℕ} : Command p :=
  .allocate 4 (.pair (.register 1) (.register 2))
    (.allocate 5 (.pair (.register 0) (.register 4))
      (.allocate 6 (.cons (.register 5) (.register 3)) (.ret [.register 6])))

theorem compiled {p vbits cbits : ℕ} (code : Code p) {h : Heap} (hh : Valid h)
    {sp tp cl tail : Ptr} {source target : Bits vbits} {weight : Bits cbits} {label : Ptr}
    {entries : List (RawArc Ptr vbits cbits)}
    (hs : BitsAt h sp source) (ht : BitsAt h tp target) (hc : CostLabelAt h cl weight label)
    (hl : TraceAt h tail entries) :
    ∃ out q, Extends h out ∧ Valid out ∧
      TraceAt out q ((source, ⟨target, weight, label⟩) :: entries) ∧
      Within code h (initialRegisters [.pointer sp, .pointer tp, .pointer cl, .pointer tail])
        emitBody [.pointer q] out 27 := by
  obtain ⟨wp, hcostCell, hw, hlabel⟩ := hc
  have hcl : cl < h.length := List.getElem?_eq_some_iff.mp hcostCell |>.1
  have ha := safe_allocate h hh (.pair tp cl) (by
    intro v hv
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ht.allocated
    · exact hcl)
  let h1 := h ++ [.pair tp cl]
  have arc : ArcAt h1 h.length ⟨target, weight, label⟩ := by
    refine ⟨tp, cl, wp, ?_, ha.1.lookup hcostCell, ht.mono ha.1, hw.mono ha.1, ?_⟩
    · simp [h1]
    · exact lt_of_lt_of_le hlabel ha.1.length_le
  obtain ⟨hr, raw⟩ := storeRawArc_correct ha.2.1 (hs.mono ha.1) arc
  let h2 := h1 ++ [.pair sp h.length]
  have ext2 : Extends h h2 := ha.1.trans hr.1
  obtain ⟨ps, hlist, hitems⟩ := hl
  obtain ⟨hcons, hfinal⟩ := allocate_cons hr.2.1 raw.allocated ((hlist.mono ha.1).mono hr.1)
  let final := h2 ++ [.cons h1.length tail]
  have finalExt : Extends h final := ext2.trans hcons.1
  refine ⟨final, h2.length, finalExt, hcons.2.1, ?_, ?_⟩
  · refine ⟨h1.length :: ps, hfinal, .cons (raw.mono hcons.1) ?_⟩
    exact hitems.imp (fun _ _ hv => hv.mono finalExt)
  · unfold emitBody
    apply Within.allocate (budget := 19) (c := .pair tp cl)
    · simp [CellExpr.eval, Atom.eval, initialRegisters, Value.asPointer]
    · apply Within.allocate (budget := 11) (c := .pair sp h.length)
      · simp [CellExpr.eval, Atom.eval, initialRegisters, Value.asPointer]
      · apply Within.allocate (budget := 3) (c := .cons h1.length tail)
        · simp [CellExpr.eval, Atom.eval, initialRegisters, Value.asPointer, h1]
        · simpa [values, Atom.eval, h1, h2, final, List.append_assoc] using
            Within.ret code final
              (Function.update (Function.update (Function.update
                (initialRegisters [.pointer sp, .pointer tp, .pointer cl, .pointer tail])
                  4 (.pointer h.length)) 5 (.pointer h1.length)) 6 (.pointer h2.length)) [.register 6]

end WeightedMIS.RegisterArcEmitter
