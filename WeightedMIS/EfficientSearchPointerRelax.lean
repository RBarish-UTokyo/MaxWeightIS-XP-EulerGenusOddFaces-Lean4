module

public import WeightedMIS.EfficientSearchPointerTrie
public import WeightedMIS.PointerArithmetic

/-! # Pointer execution of candidate creation and outgoing relaxation -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Pointer

open WeightedMIS.PointerMemory

variable {vbits cbits : ℕ}

/-- Three allocations extend a reverse path and package its new endpoint. -/
def extendCandidate (vertex path arc target : Ptr) : Program Ptr := fun heap =>
  let raw := storeRawArc vertex arc heap
  let chain := storeTraceCons raw.value path raw.heap
  let candidate := storeCandidate target chain.value chain.heap
  ⟨candidate.value, candidate.heap, raw.trace ++ chain.trace ++ candidate.trace⟩

theorem extendCandidate_refines {heap : Heap} (hh : Valid heap)
    {vp pp ap tp : Ptr} {vertex : Bits vbits} {path : Trace Ptr vbits cbits}
    {edge : Arc Ptr vbits cbits} (hv : BitsAt heap vp vertex) (hp : TraceAt heap pp path)
    (ha : ArcAt heap ap edge) (ht : BitsAt heap tp edge.target) :
    SafeRun heap (extendCandidate vp pp ap tp heap) ∧
      CandidateAt (extendCandidate vp pp ap tp heap).heap
        (extendCandidate vp pp ap tp heap).value ⟨edge.target, (vertex, edge) :: path⟩ ∧
      (extendCandidate vp pp ap tp heap).trace.length = 3 := by
  obtain ⟨hrs, hrr⟩ := storeRawArc_correct hh hv ha
  obtain ⟨hcs, hcr⟩ := storeTraceCons_correct hrs.2.1 hrr (hp.mono hrs.1)
  obtain ⟨hns, hnr⟩ := storeCandidate_correct hcs.2.1
    (ht.mono (hrs.1.trans hcs.1)) hcr
  refine ⟨?_, hnr, ?_⟩
  · exact safe_join (safe_join hrs hcs) hns
  · simp [extendCandidate, storeRawArc, storeTraceCons, storeCandidate, Program.allocate]

/-- Load the weight and target of one actual adjacency record, add its weight
bit by bit, create a shared candidate, and insert its key into the queue. -/
def pushEdge (cbits : ℕ) (vertex path distance arc queue : Ptr) :
    Program (Option (Ptr × Bool)) := fun heap =>
  let ar := Program.load arc heap
  match ar.value with
  | some (.pair target weightLabel) =>
      let wl := Program.load weightLabel heap
      match wl.value with
      | some (.pair weight _label) =>
          let added := addPointer cbits distance weight heap
          let candidate := extendCandidate vertex path arc target added.heap
          let inserted := insertPointer cbits added.value.1 candidate.value queue candidate.heap
          ⟨inserted.value.map (fun p => (p, added.value.2)), inserted.heap,
            .control :: (ar.trace ++ wl.trace ++ added.trace ++ candidate.trace ++ inserted.trace)⟩
      | _ => ⟨none, heap, .control :: (ar.trace ++ wl.trace)⟩
  | _ => ⟨none, heap, .control :: ar.trace⟩

theorem pushEdge_refines {heap : Heap} (hh : Valid heap)
    {vp pp dp ap qp : Ptr} {vertex : Bits vbits} {path : Trace Ptr vbits cbits}
    {distance : Bits cbits} {edge : Arc Ptr vbits cbits} {queue : Queue Ptr vbits cbits}
    (hv : BitsAt heap vp vertex) (hp : TraceAt heap pp path) (hd : BitsAt heap dp distance)
    (ha : ArcAt heap ap edge) (hq : QueueAt heap qp queue) :
    SafeRun heap (pushEdge cbits vp pp dp ap qp heap) ∧
      ∃ out, (pushEdge cbits vp pp dp ap qp heap).value =
          some (out, (Bits.add distance edge.weight).2.1) ∧
        QueueAt (pushEdge cbits vp pp dp ap qp heap).heap out
          (Radix.insert (Bits.add distance edge.weight).1
            ⟨edge.target, (vertex, edge) :: path⟩ queue).1 ∧
        (pushEdge cbits vp pp dp ap qp heap).trace.length ≤ 20 * (cbits + 1) := by
  obtain ⟨tp, wlp, wp, hac, hwlc, ht, hw, hlabel⟩ := ha
  have ha : ArcAt heap ap edge := ⟨tp, wlp, wp, hac, hwlc, ht, hw, hlabel⟩
  obtain ⟨has, har, hacarry, halength⟩ := addPointer_refines hh hd hw
  obtain ⟨hcs, hcr, hclength⟩ := extendCandidate_refines has.2.1
    (hv.mono has.1) (hp.mono has.1) (ha.mono has.1) (ht.mono has.1)
  have hext := has.1.trans hcs.1
  have hqr : QueueAt _ qp queue := hq.mono hext (fun p value h => h.mono hext)
  obtain ⟨his, out, hiv, hir, hilength⟩ := insert_tree_refines (R := CandidateAt)
    (fun hext p value h => CandidateAt.mono hext h) hcs.2.1
    (har.mono hcs.1) hcr hcr.allocated hqr
  have hb : TraceBound (.control :: ((Program.load ap heap).trace ++
      (Program.load wlp heap).trace)) heap.length := by
    intro e he p href
    rcases List.mem_cons.mp he with rfl | he
    · simp [Event.references] at href
    · exact traceBound_append (safe_load heap hh ap ha.allocated).2.2.1
        (safe_load heap hh wlp (List.getElem?_eq_some_iff.mp hwlc |>.1)).2.2.1 e he p href
  have hsafe := safe_prefix (safe_change_value (safe_join (safe_join has hcs) his)
    (some (out, (Bits.add distance edge.weight).2.1))) _ hb
  refine ⟨?_, out, ?_, ?_, ?_⟩
  · simpa [pushEdge, Program.load, hac, hwlc, hiv, hacarry, List.append_assoc] using hsafe
  · simp [pushEdge, Program.load, hac, hwlc, hiv, hacarry]
  · simpa [pushEdge, Program.load, hac, hwlc] using hir
  · simp only [pushEdge, Program.load, hac, hwlc, List.length_cons, List.length_append,
      List.length_nil]
    rw [halength, hclength, hilength, Radix.insert_steps]
    omega

/-- The natural parameter bounds evaluation only. Each successful recursive
call first observes an actual nonempty adjacency-list cell. -/
def relaxPointer (cbits : ℕ) : ℕ → Ptr → Ptr → Ptr → Ptr → Ptr →
    Program (Option (Ptr × Bool))
  | 0, _vertex, _path, _distance, edges, queue, heap =>
      let loaded := Program.load edges heap
      let before := [.control, .control] ++ loaded.trace
      match loaded.value with
      | some .nil => ⟨some (queue, false), heap, before⟩
      | _ => ⟨none, heap, before⟩
  | fuel + 1, vertex, path, distance, edges, queue, heap =>
      let loaded := Program.load edges heap
      let before := [.control, .control] ++ loaded.trace
      match loaded.value with
      | some .nil => ⟨some (queue, false), heap, before⟩
      | some (.cons arc tail) =>
          let step := pushEdge cbits vertex path distance arc queue heap
          match step.value with
          | none => ⟨none, step.heap, before ++ step.trace⟩
          | some (nextQueue, overflow) =>
              let rest := relaxPointer cbits fuel vertex path distance tail nextQueue step.heap
              ⟨rest.value.map (fun result => (result.1, overflow || result.2)), rest.heap,
                before ++ step.trace ++ rest.trace⟩
      | _ => ⟨none, heap, before⟩

theorem relaxPointer_refines {heap : Heap} (hh : Valid heap)
    {vp pp dp ep qp : Ptr} {candidate : Candidate Ptr vbits cbits} {distance : Bits cbits}
    {edges : List (Arc Ptr vbits cbits)} {queue : Queue Ptr vbits cbits}
    (fuel : ℕ) (hfuel : edges.length ≤ fuel)
    (hv : BitsAt heap vp candidate.vertex) (hp : TraceAt heap pp candidate.reversePath)
    (hd : BitsAt heap dp distance) (he : ListRep ArcAt heap ep edges) (hq : QueueAt heap qp queue) :
    SafeRun heap (relaxPointer cbits fuel vp pp dp ep qp heap) ∧
      ∃ out, (relaxPointer cbits fuel vp pp dp ep qp heap).value =
          some (out, (relax candidate distance edges queue).2.1) ∧
        QueueAt (relaxPointer cbits fuel vp pp dp ep qp heap).heap out
          (relax candidate distance edges queue).1 ∧
        (relaxPointer cbits fuel vp pp dp ep qp heap).trace.length ≤
          12 * (relax candidate distance edges queue).2.2 := by
  induction edges generalizing fuel heap ep qp queue with
  | nil =>
    obtain ⟨pointers, hlist, hrel⟩ := he
    cases hrel
    cases hlist with
    | nil hcell =>
      have hb : TraceBound ([.control, .control] ++ (Program.load ep heap).trace) heap.length :=
        traceBound_append (controls_bound 2 heap.length)
          (safe_load heap hh ep (List.getElem?_eq_some_iff.mp hcell |>.1)).2.2.1
      have hs := safe_prefix (safe_pure heap hh (some (qp, false))) _ hb
      refine ⟨?_, qp, ?_, ?_, ?_⟩
      · cases fuel <;> simpa [relaxPointer, Program.load, hcell, Program.pure] using hs
      · cases fuel <;> simp [relaxPointer, Program.load, hcell, relax]
      · cases fuel <;> simpa [relaxPointer, Program.load, hcell, relax] using hq
      · cases fuel <;> simp [relaxPointer, Program.load, hcell, relax]
  | cons edge rest ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ fuel =>
      obtain ⟨pointers, hlist, hrel⟩ := he
      cases hrel with
      | @cons arc tail _ _ har htail =>
        cases hlist with
        | @cons _ _ tailPtr _ hcell hlistTail =>
          have htailRep : ListRep ArcAt heap tailPtr rest := ⟨_, hlistTail, htail⟩
          obtain ⟨hstep, nextQueue, hstepValue, hstepQueue, hstepCost⟩ :=
            pushEdge_refines hh hv hp hd har hq
          have hext := hstep.1
          obtain ⟨hrest, out, hrestValue, hrestQueue, hrestCost⟩ := ih hstep.2.1 fuel
            (by simp at hfuel; omega) (hv.mono hext) (hp.mono hext) (hd.mono hext)
            (htailRep.mono hext (fun p value h => h.mono hext)) hstepQueue
          have hb : TraceBound ([.control, .control] ++ (Program.load ep heap).trace) heap.length :=
            traceBound_append (controls_bound 2 heap.length)
              (safe_load heap hh ep (List.getElem?_eq_some_iff.mp hcell |>.1)).2.2.1
          have hs := safe_prefix (safe_change_value (safe_join hstep hrest)
            (some (out, (relax candidate distance (edge :: rest) queue).2.1))) _ hb
          refine ⟨?_, out, ?_, ?_, ?_⟩
          · simpa [relaxPointer, Program.load, hcell, hstepValue, hrestValue, relax,
              List.append_assoc] using hs
          · simp [relaxPointer, Program.load, hcell, hstepValue, hrestValue, relax]
          · simpa [relaxPointer, Program.load, hcell, hstepValue, relax] using hrestQueue
          · simp only [relaxPointer, Program.load, hcell, hstepValue,
              List.length_append, List.length_cons, List.length_nil]
            rw [relax_steps] at hrestCost ⊢
            simp only [List.length_cons]
            nlinarith

end WeightedMIS.EfficientSearch.Pointer
