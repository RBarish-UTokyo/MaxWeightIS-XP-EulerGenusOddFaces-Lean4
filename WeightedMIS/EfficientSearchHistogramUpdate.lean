module

public import WeightedMIS.EfficientSearchHistogramCode
public import WeightedMIS.EfficientSearchProgram

/-! # Compiled update of one binary label count -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Histogram

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.RegisterCode

abbrev TableAt {lb cb : ℕ} (h : Heap) (p : Ptr) (table : Table lb cb) :=
  Pointer.TreeAt (fun h p word => BitsAt h p word) h p table

abbrev LabelsAt {lb : ℕ} (h : Heap) (p : Ptr) (keys : List (Bits lb)) :=
  Pointer.ListRep (fun h p word => BitsAt h p word) h p keys

def budget (lb cb length : ℕ) : ℕ := 2000 * (lb + cb + 2) * length + 15

variable {p lb cb : ℕ} {code : Code p} {lookup add insert self : Fin p}

/-- The nonrecursive update continuation is executed by fixed finite code.
The supplied recursive execution is used only for the remaining list suffix. -/
theorem update_compiled
    (compileAdd : ∀ {h : Heap} {ap bp : Ptr} {carry : Bool} {result : Run (Ptr × Bool)},
      AddEval h ap bp carry result →
      Within code h (initialRegisters [.pointer ap, .pointer bp, .flag carry]) (code add)
        [.pointer result.value.1, .flag result.value.2] result.heap (10 * result.trace.length))
    (compileInsert : ∀ {h : Heap} {key a tree : Ptr} {result : Run (Option Ptr)},
      InsertEval h key a tree result →
      Within code h (initialRegisters [.pointer key, .pointer a, .pointer tree]) (code insert)
        (pointerOutput result.value) result.heap (100 * result.trace.length))
    {h : Heap} (hh : Valid h) {regs : Registers} {old : Atom}
    {tablePtr zeroPtr keyPtr tailPtr currentPtr : Ptr} {key : Bits lb} {keys : List (Bits lb)}
    {table : Table lb cb}
    (h1 : regs 1 = .pointer tablePtr) (h2 : regs 2 = .pointer zeroPtr)
    (h3 : regs 3 = .pointer keyPtr) (h4 : regs 4 = .pointer tailPtr)
    (hold : old.eval regs = .pointer currentPtr)
    (ht : TableAt h tablePtr table) (hz : BitsAt h zeroPtr (Bits.zero cb))
    (hk : BitsAt h keyPtr key) (hc : BitsAt h currentPtr (count key table))
    (hkeys : LabelsAt h tailPtr keys)
    (recurse : ∀ {nextHeap : Heap} {nextTable : Ptr}, Valid nextHeap →
      TableAt nextHeap nextTable (bump key table).1 →
      BitsAt nextHeap zeroPtr (Bits.zero cb) → LabelsAt nextHeap tailPtr keys →
      ∃ finalHeap outTable, Extends nextHeap finalHeap ∧ Valid finalHeap ∧
        TableAt finalHeap outTable (collect keys (bump key table).1).1 ∧
        Within code nextHeap (initialRegisters [.pointer tailPtr, .pointer nextTable, .pointer zeroPtr])
          (code self) [.pointer outTable, .flag (collect keys (bump key table).1).2.1] finalHeap
          (budget lb cb keys.length)) :
    ∃ finalHeap outTable, Extends h finalHeap ∧ Valid finalHeap ∧
      TableAt finalHeap outTable (collect (key :: keys) table).1 ∧
      Within code h regs (histogramUpdate lookup add insert self old)
        [.pointer outTable, .flag (collect (key :: keys) table).2.1] finalHeap
        (1000 * (lb + cb + 2) + budget lb cb keys.length) := by
  let added := addCarryPointer cb currentPtr zeroPtr true h
  obtain ⟨has, har, hac, hal⟩ := addCarryPointer_refines hh hc hz true
  have ht' : TableAt added.heap tablePtr table := ht.mono has.1 (fun p word h => h.mono has.1)
  obtain ⟨his, nextTable, hiv, hir, hil⟩ := Pointer.insert_tree_refines
    (R := fun h p word => BitsAt h p word)
    (fun hext p word h => h.mono hext) has.2.1 (hk.mono has.1) har har.allocated ht'
  have hir' : TableAt (insertPointer lb keyPtr added.value.1 tablePtr added.heap).heap nextTable (bump key table).1 := by simpa [bump, count, added] using hir
  have hext := has.1.trans his.1
  obtain ⟨finalHeap, outTable, hrestExt, hfinalValid, hfinalTable, hrec⟩ := recurse his.2.1 hir'
    (hz.mono hext) (hkeys.mono hext (fun p word h => h.mono hext))
  let addedRegs := bindResults regs [8, 9] [.pointer added.value.1, .flag added.value.2]
  let insertedRegs := bindResults addedRegs [10] [.pointer nextTable]
  let finalRegs := bindResults insertedRegs [11, 12]
    [.pointer outTable, .flag (collect keys (bump key table).1).2.1]
  have hb : Within code finalHeap finalRegs
      (.branch (r 9) (.ret [r 11, .flag true]) (.ret [r 11, r 12]))
      [.pointer outTable, .flag (added.value.2 || (collect keys (bump key table).1).2.1)] finalHeap 8 := by
    apply Within.branch (budget := 5) (b := added.value.2)
      (by simp [finalRegs, insertedRegs, addedRegs, r, Atom.eval, bindResults])
    cases hv : added.value.2 <;> simp only [Bool.false_or, Bool.true_or, Bool.false_eq_true, ↓reduceIte]
    · simpa [finalRegs, insertedRegs, addedRegs, r, values, Atom.eval, bindResults, hv] using
        Within.ret code finalHeap finalRegs [r 11, r 12]
    · simpa [finalRegs, insertedRegs, addedRegs, r, values, Atom.eval, bindResults, hv] using
        Within.ret code finalHeap finalRegs [r 11, .flag true]
  have hrc := Within.call (regs := insertedRegs) (procedure := self)
    (arguments := [r 4, r 10, r 2]) (results := [11, 12])
    (by simpa [insertedRegs, addedRegs, r, values, Atom.eval, bindResults, h4, h2] using hrec) hb
  have hie := Pointer.insert_tree_eval (ap := added.value.1) has.2.1 (hk.mono has.1) ht'
  have hic := compileInsert hie
  rw [hiv] at hic
  have hicall := Within.call (regs := addedRegs) (procedure := insert)
    (arguments := [r 3, r 8, r 1]) (results := [10])
    (by simpa [addedRegs, r, values, Atom.eval, bindResults, h3, h1, pointerOutput, added] using hic) hrc
  have hae := addCarryPointer_eval hh hc hz true
  have hacomp := compileAdd hae
  have hargs : values regs [old, r 2, .flag true] =
      [.pointer currentPtr, .pointer zeroPtr, .flag true] := by
    change [old.eval regs, regs 2, .flag true] = _
    rw [hold, h2]
  have hacall := Within.call (regs := regs) (procedure := add)
    (arguments := [old, r 2, .flag true]) (results := [8, 9])
    (by simpa [hargs, added] using hacomp) hicall
  refine ⟨finalHeap, outTable, hext.trans hrestExt, hfinalValid, hfinalTable, ?_⟩
  have hflag : added.value.2 = (bump key table).2.1 := hac
  simpa only [histogramUpdate, collect, ← hflag] using hacall.mono (by
    rw [hal, hil, Radix.insert_steps]
    simp only [List.length_cons, List.length_nil]
    omega)

end WeightedMIS.EfficientSearch.Histogram
