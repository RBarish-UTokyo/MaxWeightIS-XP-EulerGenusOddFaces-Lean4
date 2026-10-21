module

public import WeightedMIS.EfficientSearchPointerExecution
public import WeightedMIS.EfficientSearchRecovery

/-!
# Initialization and total sparse pointer search

The operational relation names the fixed initialization and search procedures.
The semantic graph size supplies only a terminating evaluator bound. A search
run performs no scan or arithmetic on that bound.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Pointer

open WeightedMIS.PointerMemory

variable {vbits cbits : ℕ}

def initializePointer (cbits : ℕ) (source zeroKey : Ptr) : Program (Option Ptr) := fun heap =>
  let candidate := storeCandidate source 0 heap
  let inserted := insertPointer cbits zeroKey candidate.value 0 candidate.heap
  ⟨inserted.value, inserted.heap, .control :: (candidate.trace ++ inserted.trace)⟩

def solvePointer (vbits cbits edgeFuel : ℕ) (graph source zeroKey : Ptr) :
    Program (Option SearchRecord) := fun heap =>
  let initialized := initializePointer cbits source zeroKey heap
  match initialized.value with
  | none => ⟨none, initialized.heap, initialized.trace⟩
  | some queue =>
      let result := runPointer vbits cbits edgeFuel graph (edgeFuel + 2) queue 0 initialized.heap
      ⟨result.value, result.heap, initialized.trace ++ result.trace⟩

inductive InitializeEval : Heap → Ptr → Ptr → Run (Option Ptr) → Prop
  | start {h : Heap} {source zeroKey : Ptr} {inserted : Run (Option Ptr)}
      (insertion : InsertEval (storeCandidate source 0 h).heap zeroKey
        (storeCandidate source 0 h).value 0 inserted) :
      InitializeEval h source zeroKey
        ⟨inserted.value, inserted.heap, .control :: ((storeCandidate source 0 h).trace ++ inserted.trace)⟩

inductive SolveEval : Heap → Ptr → Ptr → Ptr → Run (Option SearchRecord) → Prop
  | solve {h : Heap} {graph source zeroKey queue : Ptr} {initialized : Run (Option Ptr)}
      {result : Run (Option SearchRecord)}
      (initial : InitializeEval h source zeroKey initialized)
      (value : initialized.value = some queue)
      (search : SearchEval initialized.heap graph queue 0 result) :
      SolveEval h graph source zeroKey (sequenceRuns initialized result)

theorem empty_tree {α : Type*} {R : Heap → Ptr → α → Prop} {h : Heap} (hh : Valid h) (n : ℕ) :
    TreeAt R h 0 (Radix.empty : Radix α n) := ⟨.empty, .empty hh.1, .empty⟩

theorem empty_trace {h : Heap} (hh : Valid h) : TraceAt h 0 ([] : Trace Ptr vbits cbits) :=
  ⟨[], .nil hh.1, .nil⟩

theorem initializePointer_refines {h : Heap} (hh : Valid h) {sp zp : Ptr}
    {source : Bits vbits} (hs : BitsAt h sp source) (hz : BitsAt h zp (Bits.zero cbits)) :
    SafeRun h (initializePointer cbits sp zp h) ∧
      ∃ queue, (initializePointer cbits sp zp h).value = some queue ∧
        QueueAt (initializePointer cbits sp zp h).heap queue (initialQueue (cbits := cbits) source) ∧
        (initializePointer cbits sp zp h).trace.length = 4 * cbits + 7 := by
  obtain ⟨hc, hcr⟩ := storeCandidate_correct hh hs (empty_trace hh)
  obtain ⟨hi, queue, hv, hq, hcost⟩ := insert_tree_refines (R := CandidateAt)
    (fun hext p value h => h.mono hext) hc.2.1 (hz.mono hc.1) hcr hcr.allocated
    (empty_tree hc.2.1 cbits)
  have hall := safe_prefix (safe_join hc hi) [.control] (controls_bound 1 h.length)
  refine ⟨?_, queue, ?_, ?_, ?_⟩
  · simpa [initializePointer] using hall
  · simpa [initializePointer] using hv
  · simpa [initializePointer, initialQueue] using hq
  · simp only [initializePointer, List.length_cons, List.length_append,
      storeCandidate, Program.allocate, List.length_nil] at *
    rw [Radix.insert_steps] at hcost
    omega

theorem initializePointer_eval {h : Heap} (hh : Valid h) {sp zp : Ptr}
    {source : Bits vbits} (hs : BitsAt h sp source) (hz : BitsAt h zp (Bits.zero cbits)) :
    InitializeEval h sp zp (initializePointer cbits sp zp h) := by
  have hc := (storeCandidate_correct hh hs (empty_trace (vbits := vbits) (cbits := cbits) hh)).1
  exact InitializeEval.start (insert_tree_eval hc.2.1 (hz.mono hc.1)
    (empty_tree (R := CandidateAt (vbits := vbits) (cbits := cbits)) hc.2.1 cbits))

theorem InitializeEval.exec {h : Heap} {source zeroKey : Ptr} {r : Run (Option Ptr)}
    (he : InitializeEval h source zeroKey r) : HeapExec h r.trace r.heap := by
  cases he with
  | start insertion => exact .cons (.control h) ((allocate_exec h (.pair source 0)).append insertion.exec)

theorem SolveEval.exec {h : Heap} {graph source zeroKey : Ptr} {r : Run (Option SearchRecord)}
    (he : SolveEval h graph source zeroKey r) : HeapExec h r.trace r.heap := by
  cases he with
  | solve initial value search => exact initial.exec.append search.exec

theorem solvePointer_refines {h : Heap} (hh : Valid h) {gp sp zp : Ptr}
    {graph : Graph Ptr vbits cbits} {source : Bits vbits}
    (hg : GraphAt h gp graph) (hs : BitsAt h sp source) (hz : BitsAt h zp (Bits.zero cbits)) :
    SafeRun h (solvePointer vbits cbits graph.elements.length gp sp zp h) ∧
      SolveEval h gp sp zp (solvePointer vbits cbits graph.elements.length gp sp zp h) ∧
      ∃ outQueue outSettled,
        (solvePointer vbits cbits graph.elements.length gp sp zp h).value =
          some ⟨(solve graph source).status, outQueue, outSettled⟩ ∧
        QueueAt (solvePointer vbits cbits graph.elements.length gp sp zp h).heap outQueue
          (solve graph source).queue ∧
        SettledAt (solvePointer vbits cbits graph.elements.length gp sp zp h).heap outSettled
          (solve graph source).settled ∧
        (solvePointer vbits cbits graph.elements.length gp sp zp h).trace.length ≤
          50 * (solve graph source).work := by
  obtain ⟨hi, queue, hiv, hq, hicost⟩ := initializePointer_refines hh hs hz
  have hg' := hg.mono hi.1 (fun p value h => h.mono hi.1)
  have hs' := empty_tree (R := StoredAt (vbits := vbits) (cbits := cbits)) hi.2.1 vbits
  obtain ⟨hr, outQueue, outSettled, hrv, hrq, hrs, hrcost⟩ :=
    runPointer_refines hi.2.1 graph.elements.length (graph.elements.length + 2)
      (le_refl _) hg' hq hs'
  have hne : (run graph (graph.elements.length + 2) (initialQueue source) .empty).status ≠ .exhausted := by
    simpa only [solve, Radix.countEntries_value, initialQueue] using solve_not_exhausted graph source
  have hre := runPointer_eval hi.2.1 graph.elements.length (graph.elements.length + 2)
    (le_refl _) hg' hq hs' hne
  refine ⟨?_, ?_, outQueue, outSettled, ?_, ?_, ?_, ?_⟩
  · simpa [solvePointer, hiv] using safe_join hi hr
  · simpa [solvePointer, hiv, sequenceRuns] using SolveEval.solve (initializePointer_eval hh hs hz) hiv hre
  · simpa [solvePointer, hiv, solve, Radix.countEntries_value, initialQueue] using hrv
  · simpa [solvePointer, hiv, solve, Radix.countEntries_value, initialQueue] using hrq
  · simpa [solvePointer, hiv, solve, Radix.countEntries_value, initialQueue] using hrs
  · simp only [solvePointer, hiv, List.length_append, hicost, solve, Radix.countEntries_value,
      Radix.insert_steps]
    dsimp only [initialQueue] at hrcost
    omega

theorem solvePointer_work_le {h : Heap} (hh : Valid h) {gp sp zp : Ptr}
    {graph : Graph Ptr vbits cbits} {source : Bits vbits}
    (hg : GraphAt h gp graph) (hs : BitsAt h sp source) (hz : BitsAt h zp (Bits.zero cbits))
    (hcanonical : graph.canonical) :
    (solvePointer vbits cbits graph.elements.length gp sp zp h).trace.length ≤
      50 * ((5 * cbits + 5 * vbits + 20) * (graph.elements.length + 1) + 6) := by
  obtain ⟨_, _, _, _, _, _, _, hc⟩ := solvePointer_refines hh hg hs hz
  exact hc.trans (Nat.mul_le_mul_left 50 (solve_work_le graph source hcanonical))

end WeightedMIS.EfficientSearch.Pointer
