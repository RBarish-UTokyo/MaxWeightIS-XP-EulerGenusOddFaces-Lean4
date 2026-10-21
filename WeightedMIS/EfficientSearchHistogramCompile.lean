module

public import WeightedMIS.EfficientSearchHistogramUpdate

/-! # Uniform compiled traversal producing exact binary label multiplicities -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Histogram

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.RegisterCode

variable {p lb cb : ℕ} {code : Code p} {lookup add insert self : Fin p}

theorem collect_compiled (hself : code self = histogramBody lookup add insert self)
    (compileLookup : ∀ {h : Heap} {key tree : Ptr} {result : Run (Option Ptr)},
      LookupEval h key tree result →
      Within code h (initialRegisters [.pointer key, .pointer tree]) (code lookup)
        (pointerOutput result.value) result.heap (100 * result.trace.length))
    (compileAdd : ∀ {h : Heap} {ap bp : Ptr} {carry : Bool} {result : Run (Ptr × Bool)},
      AddEval h ap bp carry result →
      Within code h (initialRegisters [.pointer ap, .pointer bp, .flag carry]) (code add)
        [.pointer result.value.1, .flag result.value.2] result.heap (10 * result.trace.length))
    (compileInsert : ∀ {h : Heap} {key a tree : Ptr} {result : Run (Option Ptr)},
      InsertEval h key a tree result →
      Within code h (initialRegisters [.pointer key, .pointer a, .pointer tree]) (code insert)
        (pointerOutput result.value) result.heap (100 * result.trace.length))
    {h : Heap} (hh : Valid h) {labelsPtr tablePtr zeroPtr : Ptr} {keys : List (Bits lb)} {table : Table lb cb}
    (ht : TableAt h tablePtr table) (hz : BitsAt h zeroPtr (Bits.zero cb)) (hlabels : LabelsAt h labelsPtr keys) :
    ∃ finalHeap outTable, Extends h finalHeap ∧ Valid finalHeap ∧
      TableAt finalHeap outTable (collect keys table).1 ∧
      Within code h (initialRegisters [.pointer labelsPtr, .pointer tablePtr, .pointer zeroPtr])
        (code self) [.pointer outTable, .flag (collect keys table).2.1] finalHeap (budget lb cb keys.length) := by
  induction keys generalizing h labelsPtr tablePtr zeroPtr table with
  | nil =>
    obtain ⟨raw, hl, hr⟩ := hlabels
    cases hr
    cases hl with
    | nil hcell =>
      refine ⟨h, tablePtr, Extends.refl h, hh, ht, ?_⟩
      rw [hself]
      let regs := initialRegisters [.pointer labelsPtr, .pointer tablePtr, .pointer zeroPtr]
      have hret : Within code h (loadRegisters regs 3 4 15 .nil) (.ret [r 1, .flag false])
          [.pointer tablePtr, .flag false] h 5 := by
        simpa [regs, r, values, Atom.eval, initialRegisters, loadRegisters, decoded] using
          Within.ret code h (loadRegisters regs 3 4 15 .nil) [r 1, .flag false]
      apply Within.load (budget := 5) (pointer := labelsPtr) (c := .nil)
      · simp [regs, r, Atom.eval, initialRegisters]
      · exact hcell
      · simpa [listCases, Cases.select, regs, collect] using hret
  | cons key keys ih =>
    obtain ⟨raw, hlist, hrel⟩ := hlabels
    cases hrel with
    | @cons keyPtr rawTail _ _ hkey htailRel =>
      cases hlist with
      | @cons _ _ tailPtr _ hcell htailList =>
        have htail : LabelsAt h tailPtr keys := ⟨_, htailList, htailRel⟩
        obtain ⟨_, itemsPtr, hlookValue, hlookHeap, hlookList, hlookCost⟩ := Pointer.lookup_tree_refines hh hkey ht
        have hlookup := compileLookup (Pointer.lookup_tree_eval hkey ht)
        rw [hlookValue, hlookHeap] at hlookup
        let regs := initialRegisters [.pointer labelsPtr, .pointer tablePtr, .pointer zeroPtr]
        let loaded := loadRegisters regs 3 4 15 (.cons keyPtr tailPtr)
        let looked := bindResults loaded [5] [.pointer itemsPtr]
        have choose : ∃ finalHeap outTable, Extends h finalHeap ∧ Valid finalHeap ∧
            TableAt finalHeap outTable (collect (key :: keys) table).1 ∧
            Within code h looked
              (.load (r 5) 6 7 15 (listCases
                (histogramUpdate lookup add insert self (r 2))
                (histogramUpdate lookup add insert self (r 6))))
              [.pointer outTable, .flag (collect (key :: keys) table).2.1] finalHeap
              (10 + (1000 * (lb + cb + 2) + budget lb cb keys.length)) := by
          obtain ⟨pointers, hl, hrel⟩ := hlookList
          cases hs : (Radix.lookup key table).1 with
          | nil =>
            rw [hs] at hrel
            cases hrel
            cases hl with
            | nil hitems =>
              let headRegs := loadRegisters looked 6 7 15 .nil
              obtain ⟨finalHeap, outTable, hext, hv, htout, hexec⟩ := update_compiled
                (lookup := lookup) compileAdd compileInsert hh (regs := headRegs) (old := r 2) (currentPtr := zeroPtr)
                (by simp [headRegs, looked, loaded, regs, r, Atom.eval, loadRegisters, decoded, bindResults, initialRegisters])
                (by simp [headRegs, looked, loaded, regs, r, Atom.eval, loadRegisters, decoded, bindResults, initialRegisters])
                (by simp [headRegs, looked, loaded, regs, r, Atom.eval, loadRegisters, decoded, bindResults, initialRegisters])
                (by simp [headRegs, looked, loaded, regs, r, Atom.eval, loadRegisters, decoded, bindResults, initialRegisters])
                (by simp [headRegs, looked, loaded, regs, r, Atom.eval, loadRegisters, decoded, bindResults, initialRegisters])
                ht hz hkey (by simpa [count, hs] using hz) htail
                (fun hnext htable hzero hkeys => ih hnext htable hzero hkeys)
              refine ⟨finalHeap, outTable, hext, hv, htout, ?_⟩
              apply Within.load (budget := 1000 * (lb + cb + 2) + budget lb cb keys.length)
                (pointer := itemsPtr) (c := .nil)
              · simp [looked, r, Atom.eval, bindResults]
              · exact hitems
              · simpa [listCases, Cases.select, headRegs] using hexec
          | cons word words =>
            rw [hs] at hrel
            cases hrel with
            | @cons wordPtr rawWords _ _ hword hwords =>
              cases hl with
              | @cons _ _ restPtr _ hitems hrest =>
                let headRegs := loadRegisters looked 6 7 15 (.cons wordPtr restPtr)
                obtain ⟨finalHeap, outTable, hext, hv, htout, hexec⟩ := update_compiled
                  (lookup := lookup) compileAdd compileInsert hh (regs := headRegs) (old := r 6) (currentPtr := wordPtr)
                  (by simp [headRegs, looked, loaded, regs, r, Atom.eval, loadRegisters, decoded, bindResults, initialRegisters])
                  (by simp [headRegs, looked, loaded, regs, r, Atom.eval, loadRegisters, decoded, bindResults, initialRegisters])
                  (by simp [headRegs, looked, loaded, regs, r, Atom.eval, loadRegisters, decoded, bindResults, initialRegisters])
                  (by simp [headRegs, looked, loaded, regs, r, Atom.eval, loadRegisters, decoded, bindResults, initialRegisters])
                  (by simp [headRegs, r, Atom.eval, loadRegisters, decoded])
                  ht hz hkey (by simpa [count, hs] using hword) htail
                  (fun hnext htable hzero hkeys => ih hnext htable hzero hkeys)
                refine ⟨finalHeap, outTable, hext, hv, htout, ?_⟩
                apply Within.load (budget := 1000 * (lb + cb + 2) + budget lb cb keys.length)
                  (pointer := itemsPtr) (c := .cons wordPtr restPtr)
                · simp [looked, r, Atom.eval, bindResults]
                · exact hitems
                · simpa [listCases, Cases.select, headRegs] using hexec
        obtain ⟨finalHeap, outTable, hext, hv, htout, hchoose⟩ := choose
        have hcall := Within.call (regs := loaded) (procedure := lookup)
          (arguments := [r 3, r 1]) (results := [5])
          (by simpa [loaded, regs, r, values, Atom.eval, loadRegisters, decoded, initialRegisters, pointerOutput]
              using hlookup) hchoose
        have hall := Within.load (regs := regs) (address := r 0) (first := 3) (second := 4) (bit := 15)
          (branches := listCases (.ret [r 1, .flag false])
            (.call lookup [r 3, r 1] [5]
              (.load (r 5) 6 7 15 (listCases
                (histogramUpdate lookup add insert self (r 2))
                (histogramUpdate lookup add insert self (r 6))))))
          (by simp [regs, r, Atom.eval, initialRegisters]) hcell
          (by simpa [listCases, Cases.select, loaded] using hcall)
        refine ⟨finalHeap, outTable, hext, hv, htout, ?_⟩
        rw [hself]
        apply hall.mono
        have hsteps := Radix.lookup_steps key table
        simp only [List.length_cons, List.length_nil, budget]
        nlinarith

end WeightedMIS.EfficientSearch.Histogram
