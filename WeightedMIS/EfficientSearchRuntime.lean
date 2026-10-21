module

public import WeightedMIS.EfficientSearchProgram

/-!
# A closed sparse-search algorithm with explicit bit cost

The program table is fixed independently of the input. Its execution returns
the exact queue and predecessor dictionary of the verified shortest-path
algorithm. The bound includes cell access, binary arithmetic, register moves,
and saving/restoring the actual caller registers bit by bit.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Program

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch.RegisterCode

/-- Linear in the number of sparse arcs, with explicit word-width factors. -/
def steps (vbits cbits arcs : ℕ) : ℕ :=
  5000 * ((5 * cbits + 5 * vbits + 20) * (arcs + 1) + 6)

theorem execute {vbits cbits : ℕ} {h : Heap} (hh : Valid h) {gp sp zp : Ptr}
    {graph : Graph Ptr vbits cbits} {source : Bits vbits}
    (hg : Pointer.GraphAt h gp graph) (hs : BitsAt h sp source)
    (hz : BitsAt h zp (Bits.zero cbits)) (hcanonical : graph.canonical) :
    ∃ (outQueue outSettled : Ptr) (result : Run (List Value)) (tree : CallTree),
      Executes code 11 h [.pointer gp, .pointer sp, .pointer zp] result ∧
      result.value = [.flag ((solve graph source).status == .overflow), .pointer outQueue, .pointer outSettled] ∧
      Pointer.QueueAt result.heap outQueue (solve graph source).queue ∧
      Pointer.SettledAt result.heap outSettled (solve graph source).settled ∧
      SafeRun h result ∧
      FramedExec code h (initialRegisters [.pointer gp, .pointer sp, .pointer zp]) (code 11) result tree ∧
      (∀ stack, StackExec h stack tree.compile result.heap stack) ∧
      result.trace.length ≤ steps vbits cbits graph.elements.length ∧
      stackBitCost tree.compile ≤ steps vbits cbits graph.elements.length *
        (102 + 35 * (h.length + steps vbits cbits graph.elements.length).size) := by
  obtain ⟨_, heval, outQueue, outSettled, hv, hq, hsettled, hpCost⟩ :=
    Pointer.solvePointer_refines hh hg hs hz
  have hc := solve_compiled heval
  rw [hv] at hc
  obtain ⟨events, hexec, hcost⟩ := hc
  have hsemantic := solve_work_le graph source hcanonical
  have hlen : events.length ≤ steps vbits cbits graph.elements.length := by
    dsimp only [steps]
    nlinarith
  have hargs : ValuesBound h.length [.pointer gp, .pointer sp, .pointer zp] := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hg.allocated
    · exact hs.allocated
    · exact hz.allocated
  have hr := initialRegisters_bounded (null_allocated hh) hargs
  obtain ⟨tree, hframe, _, hstack, hbits⟩ :=
    Executes.exists_stack_execution hexec hh hargs hlen
  refine ⟨outQueue, outSettled, _, tree, hexec, rfl, hq, hsettled,
    (hexec.safe hh hr).1, hframe, hstack, hlen, hbits⟩

/-- With enough cost bits, the concrete closed program returns normal
termination together with the verified shortest-path dictionary. -/
theorem execute_finished {vbits cbits : ℕ} {h : Heap} (hh : Valid h) {gp sp zp : Ptr}
    {graph : Graph Ptr vbits cbits} {source : Bits vbits}
    (hg : Pointer.GraphAt h gp graph) (hs : BitsAt h sp source)
    (hz : BitsAt h zp (Bits.zero cbits)) (hcanonical : graph.canonical)
    (weightBound : ℕ) (hweights : GraphBound graph weightBound)
    (hwidth : (graph.elements.length + 2) * weightBound < 2 ^ cbits) :
    ∃ (outQueue outSettled : Ptr) (result : Run (List Value)) (tree : CallTree),
      Executes code 11 h [.pointer gp, .pointer sp, .pointer zp] result ∧
      result.value = [.flag false, .pointer outQueue, .pointer outSettled] ∧
      Pointer.SettledAt result.heap outSettled (solve graph source).settled ∧
      FramedExec code h (initialRegisters [.pointer gp, .pointer sp, .pointer zp]) (code 11) result tree ∧
      (∀ stack, StackExec h stack tree.compile result.heap stack) ∧
      stackBitCost tree.compile ≤ steps vbits cbits graph.elements.length *
        (102 + 35 * (h.length + steps vbits cbits graph.elements.length).size) := by
  obtain ⟨outQueue, outSettled, result, tree, he, hv, _, hsettled, _, hf, ht, _, hc⟩ :=
    execute hh hg hs hz hcanonical
  have hdone := solve_finished graph source weightBound hweights hwidth
  refine ⟨outQueue, outSettled, result, tree, he, ?_, hsettled, hf, ht, hc⟩
  have hf : (Status.finished == Status.overflow) = false := rfl
  simpa only [hdone, hf] using hv

end WeightedMIS.EfficientSearch.Program
