module

public import WeightedMIS.EfficientSearchPointerRelax

/-! # Pointer execution of settling and expanding a fresh vertex -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Pointer

open WeightedMIS.PointerMemory

variable {vbits cbits : ℕ}

/-- The queue and settled-dictionary outputs, followed by the overflow flag. -/
abbrev FreshValue := Ptr × Ptr × Bool

def freshPointer (vbits cbits edgeFuel : ℕ)
    (graph vertex path distance queue settled : Ptr) : Program (Option FreshValue) := fun heap =>
  let stored := storeSettled distance path heap
  let inserted := insertPointer vbits vertex stored.value settled stored.heap
  match inserted.value with
  | none => ⟨none, inserted.heap, .control :: (stored.trace ++ inserted.trace)⟩
  | some newSettled =>
      let outgoing := lookupPointer vbits vertex graph inserted.heap
      match outgoing.value with
      | none => ⟨none, outgoing.heap, .control :: (stored.trace ++ inserted.trace ++ outgoing.trace)⟩
      | some edges =>
          let expanded := relaxPointer cbits edgeFuel vertex path distance edges queue outgoing.heap
          ⟨expanded.value.map (fun result => (result.1, newSettled, result.2)), expanded.heap,
            .control :: (stored.trace ++ inserted.trace ++ outgoing.trace ++ expanded.trace)⟩

theorem freshPointer_refines {heap : Heap} (hh : Valid heap)
    {gp vp pp dp qp sp : Ptr} {graph : Graph Ptr vbits cbits}
    {candidate : Candidate Ptr vbits cbits} {distance : Bits cbits}
    {queue : Queue Ptr vbits cbits} {settled : Settled Ptr vbits cbits}
    (edgeFuel : ℕ) (hfuel : (Radix.lookup candidate.vertex graph).1.length ≤ edgeFuel)
    (hg : GraphAt heap gp graph) (hv : BitsAt heap vp candidate.vertex)
    (hp : TraceAt heap pp candidate.reversePath) (hd : BitsAt heap dp distance)
    (hq : QueueAt heap qp queue) (hs : SettledAt heap sp settled) :
    SafeRun heap (freshPointer vbits cbits edgeFuel gp vp pp dp qp sp heap) ∧
      ∃ newQueue newSettled,
        (freshPointer vbits cbits edgeFuel gp vp pp dp qp sp heap).value =
          some (newQueue, newSettled,
            (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue).2.1) ∧
        QueueAt (freshPointer vbits cbits edgeFuel gp vp pp dp qp sp heap).heap newQueue
          (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue).1 ∧
        SettledAt (freshPointer vbits cbits edgeFuel gp vp pp dp qp sp heap).heap newSettled
          (Radix.insert candidate.vertex (distance, candidate.reversePath) settled).1 ∧
        (freshPointer vbits cbits edgeFuel gp vp pp dp qp sp heap).trace.length ≤
          20 * ((Radix.insert candidate.vertex (distance, candidate.reversePath) settled).2 +
            (Radix.lookup candidate.vertex graph).2 +
            (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue).2.2 + 1) := by
  obtain ⟨hss, hsr⟩ := storeSettled_correct hh hd hp
  have hsrOld := hs.mono hss.1 (fun p value h => h.mono hss.1)
  obtain ⟨his, newSettled, hiv, hir, hicost⟩ := insert_tree_refines (R := StoredAt)
    (fun hext p value h => h.mono hext) hss.2.1 (hv.mono hss.1) hsr hsr.allocated hsrOld
  have hext := hss.1.trans his.1
  obtain ⟨hls, edges, hlv, hlheap, hlr, hlcost⟩ := lookup_tree_refines his.2.1
    (hv.mono hext) (hg.mono hext (fun p value h => h.mono hext))
  have hallExt := hext.trans hls.1
  have hlr' : ListRep ArcAt (lookupPointer vbits vp gp
      (insertPointer vbits vp (storeSettled dp pp heap).value sp (storeSettled dp pp heap).heap).heap).heap
      edges (Radix.lookup candidate.vertex graph).1 := by rw [hlheap]; exact hlr
  obtain ⟨hrs, newQueue, hrv, hrr, hrcost⟩ := relaxPointer_refines hls.2.1 edgeFuel hfuel
    (hv.mono hallExt) (hp.mono hallExt) (hd.mono hallExt) hlr'
    (hq.mono hallExt (fun p value h => h.mono hallExt))
  have hfinalStored := hir.mono (hls.1.trans hrs.1)
    (fun p value h => h.mono (hls.1.trans hrs.1))
  have hsall := safe_prefix (safe_change_value
    (safe_join (safe_join (safe_join hss his) hls) hrs)
    (some (newQueue, newSettled,
      (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue).2.1)))
    [.control] (controls_bound 1 heap.length)
  refine ⟨?_, newQueue, newSettled, ?_, ?_, ?_, ?_⟩
  · simpa [freshPointer, hiv, hlv, hrv, List.append_assoc] using hsall
  · simp [freshPointer, hiv, hlv, hrv]
  · simpa [freshPointer, hiv, hlv] using hrr
  · simpa [freshPointer, hiv, hlv] using hfinalStored
  · simp only [freshPointer, hiv, hlv, List.length_cons, List.length_append]
    have hstoreCost : (storeSettled dp pp heap).trace.length = 1 := rfl
    rw [hstoreCost]
    nlinarith

end WeightedMIS.EfficientSearch.Pointer
