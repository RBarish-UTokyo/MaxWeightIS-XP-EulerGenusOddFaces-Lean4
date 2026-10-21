module

public import WeightedMIS.EfficientSearchPointerRun
public import WeightedMIS.PointerArithmeticEval

/-!
# Uniform data-directed search evaluation

These rules name one fixed recursive algorithm. Their only branch premises
inspect a loaded cell or a Boolean returned by a specified subroutine. Widths
and natural evaluation fuel do not occur in this operational interface.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Pointer

open WeightedMIS.PointerMemory

inductive ReadPairEval : Heap → Ptr → Run (Option (Ptr × Ptr)) → Prop
  | pair {h : Heap} {p a b : Ptr} (cell : h[p]? = some (.pair a b)) :
      ReadPairEval h p ⟨some (a, b), h, readBefore h p⟩

inductive EmptyListEval : Heap → Ptr → Run (Option Bool) → Prop
  | nil {h : Heap} {p : Ptr} (cell : h[p]? = some .nil) :
      EmptyListEval h p ⟨some true, h, readBefore h p⟩
  | cons {h : Heap} {p a tail : Ptr} (cell : h[p]? = some (.cons a tail)) :
      EmptyListEval h p ⟨some false, h, readBefore h p⟩

inductive LookupEmptyEval : Heap → Ptr → Ptr → Run (Option Bool) → Prop
  | inspect {h : Heap} {key tree items : Ptr} {looked : Run (Option Ptr)}
      {checked : Run (Option Bool)}
      (lookup : LookupEval h key tree looked) (found : looked.value = some items)
      (inspect : EmptyListEval looked.heap items checked) :
      LookupEmptyEval h key tree (sequenceRuns looked checked)

inductive PushEdgeEval : Heap → Ptr → Ptr → Ptr → Ptr → Ptr → Run (Option (Ptr × Bool)) → Prop
  | push {h : Heap} {vertex path distance arc queue target weightLabel weight label : Ptr}
      {added : Run (Ptr × Bool)} {inserted : Run (Option Ptr)}
      (arcCell : h[arc]? = some (.pair target weightLabel))
      (weightCell : h[weightLabel]? = some (.pair weight label))
      (addition : AddEval h distance weight false added)
      (insertion : InsertEval (extendCandidate vertex path arc target added.heap).heap
        added.value.1 (extendCandidate vertex path arc target added.heap).value queue inserted) :
      PushEdgeEval h vertex path distance arc queue
        ⟨inserted.value.map (fun p => (p, added.value.2)), inserted.heap,
          .control :: ((Program.load arc h).trace ++ (Program.load weightLabel h).trace ++
            added.trace ++ (extendCandidate vertex path arc target added.heap).trace ++ inserted.trace)⟩

inductive RelaxEval : Heap → Ptr → Ptr → Ptr → Ptr → Ptr → Run (Option (Ptr × Bool)) → Prop
  | nil {h : Heap} {vertex path distance edges queue : Ptr}
      (cell : h[edges]? = some .nil) :
      RelaxEval h vertex path distance edges queue
        ⟨some (queue, false), h, [.control, .control] ++ (Program.load edges h).trace⟩
  | cons {h : Heap} {vertex path distance edges queue arc tail nextQueue : Ptr} {overflow : Bool}
      {step rest : Run (Option (Ptr × Bool))}
      (cell : h[edges]? = some (.cons arc tail))
      (edge : PushEdgeEval h vertex path distance arc queue step)
      (value : step.value = some (nextQueue, overflow))
      (next : RelaxEval step.heap vertex path distance tail nextQueue rest) :
      RelaxEval h vertex path distance edges queue
        ⟨rest.value.map (fun result => (result.1, overflow || result.2)), rest.heap,
          [.control, .control] ++ (Program.load edges h).trace ++ step.trace ++ rest.trace⟩

inductive FreshEval : Heap → Ptr → Ptr → Ptr → Ptr → Ptr → Ptr → Run (Option FreshValue) → Prop
  | expand {h : Heap} {graph vertex path distance queue settled newSettled edges : Ptr}
      {inserted outgoing : Run (Option Ptr)} {expanded : Run (Option (Ptr × Bool))}
      (insertion : InsertEval (storeSettled distance path h).heap vertex
        (storeSettled distance path h).value settled inserted)
      (insertValue : inserted.value = some newSettled)
      (lookup : LookupEval inserted.heap vertex graph outgoing)
      (lookupValue : outgoing.value = some edges)
      (relax : RelaxEval outgoing.heap vertex path distance edges queue expanded) :
      FreshEval h graph vertex path distance queue settled
        ⟨expanded.value.map (fun result => (result.1, newSettled, result.2)), expanded.heap,
          .control :: ((storeSettled distance path h).trace ++ inserted.trace ++
            outgoing.trace ++ expanded.trace)⟩

inductive SearchEval : Heap → Ptr → Ptr → Ptr → Run (Option SearchRecord) → Prop
  | finished {h : Heap} {graph queue settled : Ptr} {popped : Run PopValue}
      (heapValid : Valid h) (pop : PopEval h queue popped) (empty : popped.value = none) :
      SearchEval h graph queue settled
        ⟨some ⟨.finished, queue, settled⟩, popped.heap, List.replicate 3 .control ++ popped.trace⟩
  | stale {h : Heap} {graph queue settled distance candidate restQueue vertex path : Ptr}
      {popped : Run PopValue} {record : Run (Option (Ptr × Ptr))}
      {known : Run (Option Bool)} {rest : Run (Option SearchRecord)}
      (heapValid : Valid h) (pop : PopEval h queue popped) (popValue : popped.value = some (distance, candidate, restQueue))
      (read : ReadPairEval popped.heap candidate record) (readValue : record.value = some (vertex, path))
      (lookup : LookupEmptyEval record.heap vertex settled known) (knownValue : known.value = some false)
      (next : SearchEval known.heap graph restQueue settled rest) :
      SearchEval h graph queue settled
        ⟨rest.value, rest.heap, List.replicate 3 .control ++ popped.trace ++
          record.trace ++ known.trace ++ rest.trace⟩
  | overflow {h : Heap} {graph queue settled distance candidate restQueue vertex path newQueue newSettled : Ptr}
      {popped : Run PopValue} {record : Run (Option (Ptr × Ptr))}
      {known : Run (Option Bool)} {fresh : Run (Option FreshValue)}
      (heapValid : Valid h) (pop : PopEval h queue popped) (popValue : popped.value = some (distance, candidate, restQueue))
      (read : ReadPairEval popped.heap candidate record) (readValue : record.value = some (vertex, path))
      (lookup : LookupEmptyEval record.heap vertex settled known) (knownValue : known.value = some true)
      (expand : FreshEval known.heap graph vertex path distance restQueue settled fresh)
      (freshValue : fresh.value = some (newQueue, newSettled, true)) :
      SearchEval h graph queue settled
        ⟨some ⟨.overflow, newQueue, newSettled⟩, fresh.heap,
          List.replicate 3 .control ++ popped.trace ++ record.trace ++ known.trace ++ fresh.trace⟩
  | advance {h : Heap} {graph queue settled distance candidate restQueue vertex path newQueue newSettled : Ptr}
      {popped : Run PopValue} {record : Run (Option (Ptr × Ptr))}
      {known : Run (Option Bool)} {fresh : Run (Option FreshValue)} {rest : Run (Option SearchRecord)}
      (heapValid : Valid h) (pop : PopEval h queue popped) (popValue : popped.value = some (distance, candidate, restQueue))
      (read : ReadPairEval popped.heap candidate record) (readValue : record.value = some (vertex, path))
      (lookup : LookupEmptyEval record.heap vertex settled known) (knownValue : known.value = some true)
      (expand : FreshEval known.heap graph vertex path distance restQueue settled fresh)
      (freshValue : fresh.value = some (newQueue, newSettled, false))
      (next : SearchEval fresh.heap graph newQueue newSettled rest) :
      SearchEval h graph queue settled
        ⟨rest.value, rest.heap, List.replicate 3 .control ++ popped.trace ++
          record.trace ++ known.trace ++ fresh.trace ++ rest.trace⟩

theorem readPair_eval {h : Heap} {p a b : Ptr} (hc : h[p]? = some (.pair a b)) :
    ReadPairEval h p (readPair p h) := by
  simpa [readPair, Program.load, hc, readBefore] using ReadPairEval.pair hc

theorem emptyListPointer_eval {h : Heap} {p : Ptr} {items : List Ptr}
    (hi : ListAt h p items) : EmptyListEval h p (emptyListPointer p h) := by
  cases hi with
  | nil hc => simpa [emptyListPointer, Program.load, hc, readBefore] using EmptyListEval.nil hc
  | cons hc ht => simpa [emptyListPointer, Program.load, hc, readBefore] using EmptyListEval.cons hc

theorem lookup_tree_eval {α : Type*} {R : Heap → Ptr → α → Prop} {n : ℕ}
    {h : Heap} {kp tp : Ptr} {key : Bits n} {tree : Radix α n}
    (hk : BitsAt h kp key) (ht : TreeAt R h tp tree) :
    LookupEval h kp tp (lookupPointer n kp tp h) := by
  obtain ⟨raw, hr, _⟩ := ht
  exact lookupPointer_eval hk hr

theorem insert_tree_eval {α : Type*} {R : Heap → Ptr → α → Prop} {n : ℕ}
    {h : Heap} (hh : Valid h) {kp ap tp : Ptr} {key : Bits n} {tree : Radix α n}
    (hk : BitsAt h kp key) (ht : TreeAt R h tp tree) :
    InsertEval h kp ap tp (insertPointer n kp ap tp h) := by
  obtain ⟨raw, hr, _⟩ := ht
  exact insertPointer_eval hh hk hr

theorem pop_tree_eval {α : Type*} {R : Heap → Ptr → α → Prop} {n : ℕ}
    {h : Heap} (hh : Valid h) {tp : Ptr} {tree : Radix α n}
    (ht : TreeAt R h tp tree) : PopEval h tp (popPointer n tp h) := by
  obtain ⟨raw, hr, _⟩ := ht
  exact popPointer_eval hh hr

theorem lookupEmptyPointer_eval {α : Type*} {R : Heap → Ptr → α → Prop} {n : ℕ}
    {h : Heap} (hh : Valid h) {kp tp : Ptr} {key : Bits n} {tree : Radix α n}
    (hk : BitsAt h kp key) (ht : TreeAt R h tp tree) :
    LookupEmptyEval h kp tp (lookupEmptyPointer n kp tp h) := by
  obtain ⟨_, out, ho, he, ⟨pointers, hl, _⟩, _⟩ := lookup_tree_refines hh hk ht
  have hl' : ListAt (lookupPointer n kp tp h).heap out pointers := by rw [he]; exact hl
  simpa [lookupEmptyPointer, ho, sequenceRuns] using
    LookupEmptyEval.inspect (lookup_tree_eval hk ht) ho (emptyListPointer_eval hl')

variable {vbits cbits : ℕ}

theorem pushEdge_eval {h : Heap} (hh : Valid h)
    {vp pp dp ap qp : Ptr} {vertex : Bits vbits} {path : Trace Ptr vbits cbits}
    {distance : Bits cbits} {edge : Arc Ptr vbits cbits} {queue : Queue Ptr vbits cbits}
    (hv : BitsAt h vp vertex) (hp : TraceAt h pp path) (hd : BitsAt h dp distance)
    (ha : ArcAt h ap edge) (hq : QueueAt h qp queue) :
    PushEdgeEval h vp pp dp ap qp (pushEdge cbits vp pp dp ap qp h) := by
  obtain ⟨tp, wlp, wp, hac, hwlc, ht, hw, hlabel⟩ := ha
  have ha : ArcAt h ap edge := ⟨tp, wlp, wp, hac, hwlc, ht, hw, hlabel⟩
  obtain ⟨has, har, _, _⟩ := addPointer_refines hh hd hw
  obtain ⟨hcs, _, _⟩ := extendCandidate_refines has.2.1
    (hv.mono has.1) (hp.mono has.1) (ha.mono has.1) (ht.mono has.1)
  have hext := has.1.trans hcs.1
  have hqr := hq.mono hext (fun p value h => h.mono hext)
  have hins := insert_tree_eval (ap := (extendCandidate vp pp ap tp (addPointer cbits dp wp h).heap).value) hcs.2.1 (har.mono hcs.1) hqr
  simpa [pushEdge, Program.load, hac, hwlc, addPointer] using
    PushEdgeEval.push hac hwlc (addCarryPointer_eval hh hd hw false) hins

theorem relaxPointer_eval {heap : Heap} (hh : Valid heap)
    {vp pp dp ep qp : Ptr} {candidate : Candidate Ptr vbits cbits} {distance : Bits cbits}
    {edges : List (Arc Ptr vbits cbits)} {queue : Queue Ptr vbits cbits}
    (fuel : ℕ) (hfuel : edges.length ≤ fuel)
    (hv : BitsAt heap vp candidate.vertex) (hp : TraceAt heap pp candidate.reversePath)
    (hd : BitsAt heap dp distance) (he : ListRep ArcAt heap ep edges) (hq : QueueAt heap qp queue) :
    RelaxEval heap vp pp dp ep qp (relaxPointer cbits fuel vp pp dp ep qp heap) := by
  induction edges generalizing fuel heap ep qp queue with
  | nil =>
    obtain ⟨pointers, hlist, hrel⟩ := he
    cases hrel
    cases hlist with
    | nil hcell =>
      cases fuel <;> simpa [relaxPointer, Program.load, hcell] using
        RelaxEval.nil (vertex := vp) (path := pp) (distance := dp) (queue := qp) hcell
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
          obtain ⟨hstep, nextQueue, hstepValue, hstepQueue, _⟩ :=
            pushEdge_refines hh hv hp hd har hq
          have hext := hstep.1
          have hrest := ih hstep.2.1 fuel (by simp at hfuel; omega)
            (hv.mono hext) (hp.mono hext) (hd.mono hext)
            (htailRep.mono hext (fun p value h => h.mono hext)) hstepQueue
          simpa [relaxPointer, Program.load, hcell, hstepValue, List.append_assoc] using
            RelaxEval.cons hcell (pushEdge_eval hh hv hp hd har hq) hstepValue hrest

theorem freshPointer_eval {heap : Heap} (hh : Valid heap)
    {gp vp pp dp qp sp : Ptr} {graph : Graph Ptr vbits cbits}
    {candidate : Candidate Ptr vbits cbits} {distance : Bits cbits}
    {queue : Queue Ptr vbits cbits} {settled : Settled Ptr vbits cbits}
    (edgeFuel : ℕ) (hfuel : (Radix.lookup candidate.vertex graph).1.length ≤ edgeFuel)
    (hg : GraphAt heap gp graph) (hv : BitsAt heap vp candidate.vertex)
    (hp : TraceAt heap pp candidate.reversePath) (hd : BitsAt heap dp distance)
    (hq : QueueAt heap qp queue) (hs : SettledAt heap sp settled) :
    FreshEval heap gp vp pp dp qp sp (freshPointer vbits cbits edgeFuel gp vp pp dp qp sp heap) := by
  obtain ⟨hss, hsr⟩ := storeSettled_correct hh hd hp
  have hsrOld := hs.mono hss.1 (fun p value h => h.mono hss.1)
  obtain ⟨his, newSettled, hiv, hir, _⟩ := insert_tree_refines (R := StoredAt)
    (fun hext p value h => h.mono hext) hss.2.1 (hv.mono hss.1) hsr hsr.allocated hsrOld
  have hext := hss.1.trans his.1
  have hg' := hg.mono hext (fun p value h => h.mono hext)
  obtain ⟨hls, edges, hlv, hlheap, hlr, _⟩ := lookup_tree_refines his.2.1
    (hv.mono hext) hg'
  have hallExt := hext.trans hls.1
  have hlr' : ListRep ArcAt (lookupPointer vbits vp gp
      (insertPointer vbits vp (storeSettled dp pp heap).value sp (storeSettled dp pp heap).heap).heap).heap
      edges (Radix.lookup candidate.vertex graph).1 := by rw [hlheap]; exact hlr
  have hre := relaxPointer_eval hls.2.1 edgeFuel hfuel (hv.mono hallExt) (hp.mono hallExt)
    (hd.mono hallExt) hlr' (hq.mono hallExt (fun p value h => h.mono hallExt))
  simpa [freshPointer, hiv, hlv] using FreshEval.expand
    (insert_tree_eval hss.2.1 (hv.mono hss.1) hsrOld) hiv
    (lookup_tree_eval (hv.mono hext) hg') hlv hre

theorem runPointer_eval {heap : Heap} (hh : Valid heap)
    {gp qp sp : Ptr} {graph : Graph Ptr vbits cbits}
    {queue : Queue Ptr vbits cbits} {settled : Settled Ptr vbits cbits}
    (edgeFuel fuel : ℕ) (hedges : graph.elements.length ≤ edgeFuel)
    (hg : GraphAt heap gp graph) (hq : QueueAt heap qp queue) (hs : SettledAt heap sp settled)
    (hfinished : (run graph fuel queue settled).status ≠ .exhausted) :
    SearchEval heap gp qp sp (runPointer vbits cbits edgeFuel gp fuel qp sp heap) := by
  induction fuel generalizing heap qp sp queue settled with
  | zero => simp [run] at hfinished
  | succ fuel ih =>
    have hpe := pop_tree_eval hh hq
    obtain ⟨hpop, hpopRep, _⟩ := pop_tree_refines (R := CandidateAt)
      (fun hext p value h => h.mono hext) hh hq
    cases hp : (Radix.pop queue).1 with
    | none =>
      have hpv := hpopRep.none_iff.mpr hp
      simpa [runPointer, hpv] using SearchEval.finished (graph := gp) (settled := sp) hh hpe hpv
    | some item =>
      obtain ⟨distance, candidate, queue'⟩ := item
      rw [hp] at hpopRep
      obtain ⟨dp, cp, q'p, hpv, hd, hc, hq'⟩ := hpopRep.get_some
      obtain ⟨vp, pp, hcell, hv, hpath⟩ := hc
      have hre := readPair_eval hcell
      obtain ⟨hread, hreadValue, _, _⟩ := readPair_refines hpop.2.1 hcell
      have hreadExt := hpop.1.trans hread.1
      have hsettledRead := hs.mono hreadExt (fun p value h => h.mono hreadExt)
      have hke := lookupEmptyPointer_eval hread.2.1 (hv.mono hread.1) hsettledRead
      obtain ⟨hknown, hknownValue, _, _⟩ := lookupEmptyPointer_refines hread.2.1
        (hv.mono hread.1) hsettledRead
      have hknownExt := hreadExt.trans hknown.1
      have hgraphKnown := hg.mono hknownExt (fun p value h => h.mono hknownExt)
      have hqueueKnown := hq'.mono (hread.1.trans hknown.1)
        (fun p value h => h.mono (hread.1.trans hknown.1))
      have hsettledKnown := hs.mono hknownExt (fun p value h => h.mono hknownExt)
      cases hk : (Radix.lookup candidate.vertex settled).1 with
      | cons old rest =>
        have hkvalue : (lookupEmptyPointer vbits vp sp
            (readPair cp (popPointer cbits qp heap).heap).heap).value = some false := by
          simpa [hk] using hknownValue
        have hrec := ih hknown.2.1 hgraphKnown hqueueKnown hsettledKnown
          (by simpa [run, hp, hk] using hfinished)
        simpa [runPointer, hpv, hreadValue, hkvalue, List.append_assoc] using
          SearchEval.stale hh hpe hpv hre hreadValue hke hkvalue hrec
      | nil =>
        have hkvalue : (lookupEmptyPointer vbits vp sp
            (readPair cp (popPointer cbits qp heap).heap).heap).value = some true := by
          simpa [hk] using hknownValue
        have houtlength : (Radix.lookup candidate.vertex graph).1.length ≤ edgeFuel := by
          rw [Radix.lookup_length]
          exact (List.length_filter_le _ _).trans hedges
        have hdataExt := hread.1.trans hknown.1
        have hfe := freshPointer_eval hknown.2.1 edgeFuel houtlength hgraphKnown
          (hv.mono hdataExt) (hpath.mono hdataExt) (hd.mono hdataExt) hqueueKnown hsettledKnown
        obtain ⟨hfresh, newQueue, newSettled, hfreshValue, hfreshQueue, hfreshSettled, _⟩ :=
          freshPointer_refines hknown.2.1 edgeFuel houtlength hgraphKnown
            (hv.mono hdataExt) (hpath.mono hdataExt) (hd.mono hdataExt) hqueueKnown hsettledKnown
        cases hov : (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue').2.1
        · have hfv : (freshPointer vbits cbits edgeFuel gp vp pp dp q'p sp
              (lookupEmptyPointer vbits vp sp (readPair cp (popPointer cbits qp heap).heap).heap).heap).value =
              some (newQueue, newSettled, false) := by simpa [hov] using hfreshValue
          have hgraphFresh := hgraphKnown.mono hfresh.1 (fun p value h => h.mono hfresh.1)
          have hrec := ih hfresh.2.1 hgraphFresh hfreshQueue hfreshSettled
            (by simpa [run, hp, hk, hov] using hfinished)
          simpa [runPointer, hpv, hreadValue, hkvalue, hfv, List.append_assoc] using
            SearchEval.advance hh hpe hpv hre hreadValue hke hkvalue hfe hfv hrec
        · have hfv : (freshPointer vbits cbits edgeFuel gp vp pp dp q'p sp
              (lookupEmptyPointer vbits vp sp (readPair cp (popPointer cbits qp heap).heap).heap).heap).value =
              some (newQueue, newSettled, true) := by simpa [hov] using hfreshValue
          simpa [runPointer, hpv, hreadValue, hkvalue, hfv, List.append_assoc] using
            SearchEval.overflow hh hpe hpv hre hreadValue hke hkvalue hfe hfv

end WeightedMIS.EfficientSearch.Pointer
