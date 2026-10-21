module

public import WeightedMIS.EfficientSearchHistogramCompile

/-!
# A fixed binary histogram program with bit-costed execution

The four-procedure table is independent of word widths and the input list.
The output dictionary contains the exact multiplicity of every binary label.
The bound accounts for heap access, arithmetic, register movement and the
actual caller-stack encoding.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Histogram.Program

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch.RegisterCode

/-- Lookup, insertion, binary addition and the list traversal. -/
def code : Code 4 := fun i => match i.val with
  | 0 => WeightedMIS.CompiledTrie.lookupBody 0
  | 1 => WeightedMIS.CompiledTrie.insertBody 1
  | 2 => WeightedMIS.RegisterAdder.adderBody 2
  | _ => histogramBody 0 2 1 3

theorem lookup_compiled {h : Heap} {key tree : Ptr} {result : Run (Option Ptr)}
    (he : LookupEval h key tree result) :
    Within code h (initialRegisters [.pointer key, .pointer tree]) (code 0)
      (pointerOutput result.value) result.heap (100 * result.trace.length) := by
  obtain ⟨out, hv, hc⟩ := WeightedMIS.CompiledTrie.compile_lookup (code := code) (self := 0)
    rfl he (initialRegisters [.pointer key, .pointer tree])
    (by simp [initialRegisters]) (by simp [initialRegisters])
  rw [hv]
  exact hc.mono (by omega)

theorem insert_compiled {h : Heap} {key a tree : Ptr} {result : Run (Option Ptr)}
    (he : InsertEval h key a tree result) :
    Within code h (initialRegisters [.pointer key, .pointer a, .pointer tree]) (code 1)
      (pointerOutput result.value) result.heap (100 * result.trace.length) := by
  obtain ⟨out, hv, hc⟩ := WeightedMIS.CompiledTrie.compile_insert (code := code) (self := 1)
    rfl he (initialRegisters [.pointer key, .pointer a, .pointer tree])
    (by simp [initialRegisters]) (by simp [initialRegisters]) (by simp [initialRegisters])
  rw [hv]
  exact hc.mono (by omega)

theorem add_compiled {h : Heap} {ap bp : Ptr} {carry : Bool} {result : Run (Ptr × Bool)}
    (he : AddEval h ap bp carry result) :
    Within code h (initialRegisters [.pointer ap, .pointer bp, .flag carry]) (code 2)
      [.pointer result.value.1, .flag result.value.2] result.heap (10 * result.trace.length) :=
  WeightedMIS.RegisterAdder.compiled code 2 rfl he

/-- Exact output multiplicities, together with a concrete uniform execution
and its bit-cost bound. The null cell represents the initial empty dictionary. -/
theorem execute {lb cb : ℕ} {h : Heap} (hh : Valid h) {labelsPtr zeroPtr : Ptr}
    {keys : List (Bits lb)} (hl : LabelsAt h labelsPtr keys)
    (hz : BitsAt h zeroPtr (Bits.zero cb)) (hwidth : keys.length < 2 ^ cb) :
    ∃ (table : Table lb cb) (outTable : Ptr) (result : Run (List Value)) (tree : CallTree),
      Executes code 3 h [.pointer labelsPtr, .pointer 0, .pointer zeroPtr] result ∧
      result.value = [.pointer outTable, .flag false] ∧
      TableAt result.heap outTable table ∧
      (∀ key, (count key table).value = keys.count key) ∧
      SafeRun h result ∧
      FramedExec code h (initialRegisters [.pointer labelsPtr, .pointer 0, .pointer zeroPtr])
        (code 3) result tree ∧
      (∀ stack, StackExec h stack tree.compile result.heap stack) ∧
      result.trace.length ≤ budget lb cb keys.length ∧
      stackBitCost tree.compile ≤ budget lb cb keys.length *
        (102 + 35 * (h.length + budget lb cb keys.length).size) := by
  have hempty : TableAt h 0 (.empty : Table lb cb) :=
    ⟨.empty, .empty hh.1, .empty⟩
  obtain ⟨hf, outTable, _, _, ht, events, he, hlen⟩ :=
    collect_compiled (code := code) (lookup := 0) (add := 2) (insert := 1) (self := 3)
      rfl lookup_compiled add_compiled insert_compiled hh hempty hz hl
  obtain ⟨hflag, hcounts⟩ := empty_correct keys hwidth
  have hargs : ValuesBound h.length [.pointer labelsPtr, .pointer 0, .pointer zeroPtr] := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hl.allocated
    · exact null_allocated hh
    · exact hz.allocated
  have hr := initialRegisters_bounded (null_allocated hh) hargs
  obtain ⟨tree, hframe, _, hstack, hbits⟩ :=
    Executes.exists_stack_execution he hh hargs hlen
  refine ⟨_, outTable, _, tree, he, ?_, ht, hcounts, (he.safe hh hr).1,
    hframe, hstack, hlen, hbits⟩
  change [Value.pointer outTable, Value.flag (collect keys (.empty : Table lb cb)).2.1] = _
  rw [hflag]

end WeightedMIS.EfficientSearch.Histogram.Program
