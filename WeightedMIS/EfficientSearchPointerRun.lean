module

public import WeightedMIS.EfficientSearchPointerFresh
public import WeightedMIS.EfficientSearchPointerInspect

/-!
# Pointer execution of the sparse search loop

All graph, queue, distance and predecessor data are addressed through the
heap. The natural fuel parameters bound the evaluator; successful execution
branches on the loaded queue, record, and adjacency-list cells.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Pointer

open WeightedMIS.PointerMemory

structure SearchRecord where
  status : Status
  queue : Ptr
  settled : Ptr

def runPointer (vbits cbits edgeFuel : ℕ) (graph : Ptr) :
    ℕ → Ptr → Ptr → Program (Option SearchRecord)
  | 0, queue, settled, heap =>
      ⟨some ⟨.exhausted, queue, settled⟩, heap, List.replicate 3 .control⟩
  | fuel + 1, queue, settled, heap =>
      let popped := popPointer cbits queue heap
      let afterPop : Run (Option SearchRecord) := match popped.value with
      | none => ⟨some ⟨.finished, queue, settled⟩, popped.heap, []⟩
      | some (distance, candidate, restQueue) =>
          let record := readPair candidate popped.heap
          let afterRecord : Run (Option SearchRecord) := match record.value with
          | none => ⟨none, record.heap, []⟩
          | some (vertex, path) =>
              let known := lookupEmptyPointer vbits vertex settled record.heap
              let afterKnown : Run (Option SearchRecord) := match known.value with
              | none => ⟨none, known.heap, []⟩
              | some false => runPointer vbits cbits edgeFuel graph fuel restQueue settled known.heap
              | some true =>
                  let fresh := freshPointer vbits cbits edgeFuel graph vertex path distance
                    restQueue settled known.heap
                  let afterFresh : Run (Option SearchRecord) := match fresh.value with
                  | none => ⟨none, fresh.heap, []⟩
                  | some (newQueue, newSettled, true) =>
                      ⟨some ⟨.overflow, newQueue, newSettled⟩, fresh.heap, []⟩
                  | some (newQueue, newSettled, false) =>
                      runPointer vbits cbits edgeFuel graph fuel newQueue newSettled fresh.heap
                  ⟨afterFresh.value, afterFresh.heap, fresh.trace ++ afterFresh.trace⟩
              ⟨afterKnown.value, afterKnown.heap, known.trace ++ afterKnown.trace⟩
          ⟨afterRecord.value, afterRecord.heap, record.trace ++ afterRecord.trace⟩
      ⟨afterPop.value, afterPop.heap, List.replicate 3 .control ++ popped.trace ++ afterPop.trace⟩

variable {vbits cbits : ℕ}

theorem runPointer_refines {heap : Heap} (hh : Valid heap)
    {gp qp sp : Ptr} {graph : Graph Ptr vbits cbits}
    {queue : Queue Ptr vbits cbits} {settled : Settled Ptr vbits cbits}
    (edgeFuel fuel : ℕ) (hedges : graph.elements.length ≤ edgeFuel)
    (hg : GraphAt heap gp graph) (hq : QueueAt heap qp queue) (hs : SettledAt heap sp settled) :
    SafeRun heap (runPointer vbits cbits edgeFuel gp fuel qp sp heap) ∧
      ∃ outQueue outSettled,
        (runPointer vbits cbits edgeFuel gp fuel qp sp heap).value =
          some ⟨(run graph fuel queue settled).status, outQueue, outSettled⟩ ∧
        QueueAt (runPointer vbits cbits edgeFuel gp fuel qp sp heap).heap outQueue
          (run graph fuel queue settled).queue ∧
        SettledAt (runPointer vbits cbits edgeFuel gp fuel qp sp heap).heap outSettled
          (run graph fuel queue settled).settled ∧
        (runPointer vbits cbits edgeFuel gp fuel qp sp heap).trace.length ≤
          50 * (run graph fuel queue settled).work := by
  induction fuel generalizing heap qp sp queue settled with
  | zero =>
    refine ⟨?_, qp, sp, rfl, hq, hs, by simp [runPointer, run]⟩
    exact safe_prefix (safe_pure heap hh _) _ (controls_bound 3 heap.length)
  | succ fuel ih =>
    obtain ⟨hpop, hpopRep, hpopCost⟩ := pop_tree_refines (R := CandidateAt)
      (fun hext p value h => h.mono hext) hh hq
    cases hp : (Radix.pop queue).1 with
    | none =>
      have hpv := hpopRep.none_iff.mpr hp
      have hsaf := safe_prefix (safe_change_value hpop (some (SearchRecord.mk .finished qp sp)))
        _ (controls_bound 3 heap.length)
      refine ⟨?_, qp, sp, ?_, ?_, ?_, ?_⟩
      · simpa [runPointer, hpv] using hsaf
      · simp [runPointer, hpv, run, hp]
      · simpa [runPointer, hpv, run, hp] using hq.mono hpop.1 (fun p value h => h.mono hpop.1)
      · simpa [runPointer, hpv, run, hp] using hs.mono hpop.1 (fun p value h => h.mono hpop.1)
      · simp only [runPointer, hpv, run, hp, List.length_append, List.length_replicate,
          List.length_nil, Nat.add_zero]
        omega
    | some item =>
      obtain ⟨distance, candidate, queue'⟩ := item
      rw [hp] at hpopRep
      obtain ⟨dp, cp, q'p, hpv, hd, hc, hq'⟩ := hpopRep.get_some
      obtain ⟨vp, pp, hcell, hv, hpath⟩ := hc
      obtain ⟨hread, hreadValue, _, hreadCost⟩ := readPair_refines hpop.2.1 hcell
      have hreadExt := hpop.1.trans hread.1
      have hsettledRead := hs.mono hreadExt (fun p value h => h.mono hreadExt)
      obtain ⟨hknown, hknownValue, _, hknownCost⟩ := lookupEmptyPointer_refines hread.2.1
        (hv.mono hread.1) hsettledRead
      have hknownExt := hreadExt.trans hknown.1
      have hgraphKnown := hg.mono hknownExt (fun p value h => h.mono hknownExt)
      have hqueueKnown := hq'.mono (hread.1.trans hknown.1)
        (fun p value h => h.mono (hread.1.trans hknown.1))
      have hsettledKnown := hs.mono hknownExt (fun p value h => h.mono hknownExt)
      have hprefix := safe_join (safe_join hpop hread) hknown
      cases hk : (Radix.lookup candidate.vertex settled).1 with
      | cons old rest =>
        have hkvalue : (lookupEmptyPointer vbits vp sp
            (readPair cp (popPointer cbits qp heap).heap).heap).value = some false := by
          simpa [hk] using hknownValue
        obtain ⟨hrec, outQueue, outSettled, hrecValue, hrecQueue, hrecSettled, hrecCost⟩ :=
          ih hknown.2.1 hgraphKnown hqueueKnown hsettledKnown
        have hall := safe_prefix (safe_join hprefix hrec) _ (controls_bound 3 heap.length)
        refine ⟨?_, outQueue, outSettled, ?_, ?_, ?_, ?_⟩
        · simpa [runPointer, hpv, hreadValue, hkvalue, List.append_assoc] using hall
        · simpa [runPointer, hpv, hreadValue, hkvalue, run, hp, hk] using hrecValue
        · simpa [runPointer, hpv, hreadValue, hkvalue, run, hp, hk] using hrecQueue
        · simpa [runPointer, hpv, hreadValue, hkvalue, run, hp, hk] using hrecSettled
        · simp only [runPointer, hpv, hreadValue, hkvalue, run, hp, hk,
            List.length_append, List.length_replicate]
          omega
      | nil =>
        have hkvalue : (lookupEmptyPointer vbits vp sp
            (readPair cp (popPointer cbits qp heap).heap).heap).value = some true := by
          simpa [hk] using hknownValue
        have houtlength : (Radix.lookup candidate.vertex graph).1.length ≤ edgeFuel := by
          rw [Radix.lookup_length]
          exact (List.length_filter_le _ _).trans hedges
        have hdataExt := hread.1.trans hknown.1
        obtain ⟨hfresh, newQueue, newSettled, hfreshValue, hfreshQueue, hfreshSettled,
            hfreshCost⟩ := freshPointer_refines hknown.2.1 edgeFuel houtlength
          hgraphKnown (hv.mono hdataExt) (hpath.mono hdataExt) (hd.mono hdataExt)
          hqueueKnown hsettledKnown
        have hallPrefix := safe_join hprefix hfresh
        cases hov : (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue').2.1
        · have hfv : (freshPointer vbits cbits edgeFuel gp vp pp dp q'p sp
              (lookupEmptyPointer vbits vp sp (readPair cp (popPointer cbits qp heap).heap).heap).heap).value =
              some (newQueue, newSettled, false) := by simpa [hov] using hfreshValue
          have hgraphFresh := hgraphKnown.mono hfresh.1 (fun p value h => h.mono hfresh.1)
          obtain ⟨hrec, outQueue, outSettled, hrecValue, hrecQueue, hrecSettled, hrecCost⟩ :=
            ih hfresh.2.1 hgraphFresh hfreshQueue hfreshSettled
          have hall := safe_prefix (safe_join hallPrefix hrec) _ (controls_bound 3 heap.length)
          refine ⟨?_, outQueue, outSettled, ?_, ?_, ?_, ?_⟩
          · simpa [runPointer, hpv, hreadValue, hkvalue, hfv, List.append_assoc] using hall
          · simpa [runPointer, hpv, hreadValue, hkvalue, hfv, run, hp, hk, hov] using hrecValue
          · simpa [runPointer, hpv, hreadValue, hkvalue, hfv, run, hp, hk, hov] using hrecQueue
          · simpa [runPointer, hpv, hreadValue, hkvalue, hfv, run, hp, hk, hov] using hrecSettled
          · simp only [runPointer, hpv, hreadValue, hkvalue, hfv, run, hp, hk, hov,
              Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_replicate]
            omega
        · have hfv : (freshPointer vbits cbits edgeFuel gp vp pp dp q'p sp
              (lookupEmptyPointer vbits vp sp (readPair cp (popPointer cbits qp heap).heap).heap).heap).value =
              some (newQueue, newSettled, true) := by simpa [hov] using hfreshValue
          have hall := safe_prefix (safe_change_value hallPrefix
            (some (SearchRecord.mk .overflow newQueue newSettled))) _ (controls_bound 3 heap.length)
          refine ⟨?_, newQueue, newSettled, ?_, ?_, ?_, ?_⟩
          · simpa [runPointer, hpv, hreadValue, hkvalue, hfv, List.append_assoc] using hall
          · simp [runPointer, hpv, hreadValue, hkvalue, hfv, run, hp, hk, hov]
          · simpa [runPointer, hpv, hreadValue, hkvalue, hfv, run, hp, hk, hov] using hfreshQueue
          · simpa [runPointer, hpv, hreadValue, hkvalue, hfv, run, hp, hk, hov] using hfreshSettled
          · simp only [runPointer, hpv, hreadValue, hkvalue, hfv, run, hp, hk, hov,
              ↓reduceIte, List.length_append, List.length_replicate, List.length_nil, Nat.add_zero]
            omega

end WeightedMIS.EfficientSearch.Pointer
