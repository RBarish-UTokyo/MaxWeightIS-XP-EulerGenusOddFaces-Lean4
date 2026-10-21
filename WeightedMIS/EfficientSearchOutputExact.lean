module

public import WeightedMIS.EfficientSearchOutput

/-!
# Search-to-output procedure with the exact returned record

`EfficientSearch.Output.compiled` states the properties of the returned path
but not which settled record it is. The versions below additionally export that
the distance word and reverse path are exactly the first record stored for the
target by `solve graph source`. Later stages that relabel the graph or read
the path back can then identify the path computed by the fixed procedure.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Output

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch.RegisterCode

variable {p : ℕ}

/-- The compiled search-to-output procedure, with the returned distance and
reverse path identified as the settled record of the actual search. -/
theorem compiled_exact (code : Code p) (search : Linked.Procedures p) (hsCode : search.Matches code)
    (recovery : RegisterSearchHistogram.Procedures p) (hrCode : recovery.Matches code)
    (readback : Fin p)
    (hreadback : code readback = RegisterSearchHistogram.readbackBody recovery.select recovery.labels recovery.histogram)
    {vb cb lb nb : ℕ} {h : Heap} (hh : Valid h) {gp sp zp tp np : Ptr}
    {graph : Graph Ptr vb cb} {source target : Bits vb}
    (hg : Pointer.GraphAt h gp graph) (hs : BitsAt h sp source)
    (hz : BitsAt h zp (Bits.zero cb)) (ht : BitsAt h tp target) (hn : BitsAt h np (Bits.zero nb))
    (hcanonical : graph.canonical) (weightBound : ℕ) (hweights : GraphBound graph weightBound)
    (hcostWidth : (graph.elements.length + 2) * weightBound < 2 ^ cb)
    (hcountWidth : graph.elements.length + 2 ≤ 2 ^ nb)
    (encode : Ptr → Bits lb) (hlabels : ∀ e ∈ graph.elements, BitsAt h e.2.label (encode e.2.label))
    (hreach : ∃ path, ShortestPath.IsWalk (arcSource (graph := graph)) arcTarget source target path) :
    ∃ (out : Heap) (dp tablePtr : Ptr) (distance : Bits cb) (path : Trace Ptr vb cb)
      (table : Histogram.Table lb nb),
      Extends h out ∧ Valid out ∧ BitsAt out dp distance ∧ Histogram.TableAt out tablePtr table ∧
      lookupResult (solve graph source) target = some (distance, path) ∧
      PathEvidence graph source target path distance ∧
      (∀ walk, ShortestPath.IsWalk (arcSource (graph := graph)) arcTarget source target walk →
        distance.value ≤ Dijkstra.cost arcWeight walk) ∧
      (∀ key, (Histogram.count key table).value = (path.map (fun e => encode e.2.label)).count key) ∧
      Within code h (initialRegisters [.pointer gp, .pointer sp, .pointer zp, .pointer tp, .pointer np])
        (body search.solve readback) [.pointer dp, .pointer tablePtr, .flag false] out
        (steps vb cb lb nb graph.elements.length) := by
  obtain ⟨safe, heval, outQueue, outSettled, hv, _, hsettled, hpCost⟩ :=
    Pointer.solvePointer_refines hh hg hs hz
  have solveCode := Linked.solve_compiled code search hsCode heval
  rw [hv] at solveCode
  have hdone := solve_finished graph source weightBound hweights hcostWidth
  have hfalse : (Status.finished == Status.overflow) = false := rfl
  simp only [searchOutput, hdone, hfalse] at solveCode
  have hsolveCost := solve_work_le graph source hcanonical
  have solveCode' := solveCode.mono (show 100 * (Pointer.solvePointer vb cb graph.elements.length gp sp zp h).trace.length ≤
      Program.steps vb cb graph.elements.length by unfold Program.steps; nlinarith)
  obtain ⟨distance, path, hfound, hpath, hminimum⟩ :=
    solve_recovers_minimum graph source target weightBound hweights hcostWidth hreach
  have hmember : (target, (distance, path)) ∈ (solve graph source).settled.elements := by
    apply (Radix.mem_lookup target (solve graph source).settled (distance, path)).mp
    have hc := List.eq_cons_of_mem_head? (show (distance, path) ∈
        (Radix.lookup target (solve graph source).settled).1.head? from hfound)
    rw [hc]
    exact List.mem_cons_self
  have hlength := solve_stored_depth graph source (target, (distance, path)) hmember
  change path.length < graph.elements.length + 2 at hlength
  obtain ⟨out, dp, tablePtr, table, hext, hout, hd, htable, hcounts, hread⟩ :=
    RegisterSearchHistogram.compiled code recovery hrCode safe.2.1 hsettled
      (ht.mono safe.1) (hn.mono safe.1) hfound encode
      (fun e he => (hlabels e (hpath.member e he)).mono safe.1)
      (lt_of_lt_of_le hlength hcountWidth)
  rw [← hreadback] at hread
  let regs := initialRegisters [Value.pointer gp, .pointer sp, .pointer zp, .pointer tp, .pointer np]
  let solved := bindResults regs [5, 6, 7] [Value.flag false, .pointer outQueue, .pointer outSettled]
  let recovered := bindResults solved [8, 9, 10] [Value.pointer dp, .pointer tablePtr, .flag false]
  have last : Within code out recovered (.ret [.register 8, .register 9, .register 10])
      [.pointer dp, .pointer tablePtr, .flag false] out 7 := by
    simpa [recovered, bindResults, values, Atom.eval] using
      Within.ret code out recovered [.register 8, .register 9, .register 10]
  have hrargs : values solved [.register 7, .register 3, .register 4] =
      [.pointer outSettled, .pointer tp, .pointer np] := by
    simp [solved, regs, bindResults, initialRegisters, values, Atom.eval]
  have recoverCall := Within.call (procedure := readback) (regs := solved)
    (arguments := [.register 7, .register 3, .register 4]) (results := [8, 9, 10])
    (by simpa only [hrargs] using hread) last
  have branch := Within.branch (test := .register 5) (b := false) (yes := .fail)
    (by simp [solved, bindResults, Atom.eval]) recoverCall
  have hsargs : values regs [.register 0, .register 1, .register 2] =
      [.pointer gp, .pointer sp, .pointer zp] := by
    simp [regs, initialRegisters, values, Atom.eval]
  have solveCall := Within.call (procedure := search.solve) (regs := regs)
    (arguments := [.register 0, .register 1, .register 2]) (results := [5, 6, 7])
    (by simpa only [hsargs] using solveCode') branch
  refine ⟨out, dp, tablePtr, distance, path, table, safe.1.trans hext, hout, hd, htable,
    hfound, hpath, hminimum, hcounts, solveCall.mono ?_⟩
  have hmono := Nat.mul_le_mul_left (2000 * (lb + nb + 2) + 54) hlength.le
  simp only [steps, RegisterSearchHistogram.budget, List.length_cons, List.length_nil]
  omega

/-- Framed stack execution of the same procedure, also exporting the exact
settled record whose distance and reverse path are returned. -/
theorem execute_exact (code : Code p) (search : Linked.Procedures p) (hsCode : search.Matches code)
    (recovery : RegisterSearchHistogram.Procedures p) (hrCode : recovery.Matches code)
    (readback entry : Fin p)
    (hreadback : code readback = RegisterSearchHistogram.readbackBody recovery.select recovery.labels recovery.histogram)
    (hentry : code entry = body search.solve readback)
    {vb cb lb nb : ℕ} {h : Heap} (hh : Valid h) {gp sp zp tp np : Ptr}
    {graph : Graph Ptr vb cb} {source target : Bits vb}
    (hg : Pointer.GraphAt h gp graph) (hs : BitsAt h sp source)
    (hz : BitsAt h zp (Bits.zero cb)) (ht : BitsAt h tp target) (hn : BitsAt h np (Bits.zero nb))
    (hcanonical : graph.canonical) (weightBound : ℕ) (hweights : GraphBound graph weightBound)
    (hcostWidth : (graph.elements.length + 2) * weightBound < 2 ^ cb)
    (hcountWidth : graph.elements.length + 2 ≤ 2 ^ nb)
    (encode : Ptr → Bits lb) (hlabels : ∀ e ∈ graph.elements, BitsAt h e.2.label (encode e.2.label))
    (hreach : ∃ path, ShortestPath.IsWalk (arcSource (graph := graph)) arcTarget source target path) :
    ∃ (dp tablePtr : Ptr) (distance : Bits cb) (path : Trace Ptr vb cb)
      (table : Histogram.Table lb nb) (result : Run (List Value)) (tree : CallTree),
      Executes code entry h [.pointer gp, .pointer sp, .pointer zp, .pointer tp, .pointer np] result ∧
      result.value = [.pointer dp, .pointer tablePtr, .flag false] ∧
      BitsAt result.heap dp distance ∧ Histogram.TableAt result.heap tablePtr table ∧
      lookupResult (solve graph source) target = some (distance, path) ∧
      PathEvidence graph source target path distance ∧
      (∀ walk, ShortestPath.IsWalk (arcSource (graph := graph)) arcTarget source target walk →
        distance.value ≤ Dijkstra.cost arcWeight walk) ∧
      (∀ key, (Histogram.count key table).value = (path.map (fun e => encode e.2.label)).count key) ∧
      SafeRun h result ∧
      FramedExec code h (initialRegisters [.pointer gp, .pointer sp, .pointer zp, .pointer tp, .pointer np])
        (code entry) result tree ∧
      (∀ stack, StackExec h stack tree.compile result.heap stack) ∧
      result.trace.length ≤ steps vb cb lb nb graph.elements.length ∧
      stackBitCost tree.compile ≤ steps vb cb lb nb graph.elements.length *
        (102 + 35 * (h.length + steps vb cb lb nb graph.elements.length).size) := by
  obtain ⟨out, dp, tablePtr, distance, path, table, _, _, hd, htable,
      hfound, hpath, hminimum, hcounts, events, he, hcost⟩ :=
    compiled_exact code search hsCode recovery hrCode readback hreadback hh hg hs hz ht hn
      hcanonical weightBound hweights hcostWidth hcountWidth encode hlabels hreach
  rw [← hentry] at he
  have hargs : ValuesBound h.length [.pointer gp, .pointer sp, .pointer zp, .pointer tp, .pointer np] := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact hg.allocated
    · exact hs.allocated
    · exact hz.allocated
    · exact ht.allocated
    · exact hn.allocated
  have hr := initialRegisters_bounded (null_allocated hh) hargs
  obtain ⟨tree, hframe, _, hstack, hbits⟩ := Executes.exists_stack_execution he hh hargs hcost
  exact ⟨dp, tablePtr, distance, path, table, _, tree, he, rfl, hd, htable, hfound, hpath,
    hminimum, hcounts, (he.safe hh hr).1, hframe, hstack, hcost, hbits⟩

end WeightedMIS.EfficientSearch.Output
