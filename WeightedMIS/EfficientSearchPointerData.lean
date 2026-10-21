module

public import WeightedMIS.EfficientSearchRelations
public import WeightedMIS.EfficientSearchRecovery
public import WeightedMIS.PointerRepresentations

/-!
# Heap representations of sparse-search data

Labels are opaque allocated pointers. Arcs, candidate records and stored labels
are pointer pairs. Reverse predecessor chains share their tails.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Pointer

open WeightedMIS.PointerMemory

variable {vbits cbits : ℕ}

def ArcAt (heap : Heap) (p : Ptr) (edge : Arc Ptr vbits cbits) : Prop :=
  ∃ targetPtr weightLabelPtr weightPtr,
    heap[p]? = some (.pair targetPtr weightLabelPtr) ∧
    heap[weightLabelPtr]? = some (.pair weightPtr edge.label) ∧
    BitsAt heap targetPtr edge.target ∧ BitsAt heap weightPtr edge.weight ∧
    edge.label < heap.length

def RawArcAt (heap : Heap) (p : Ptr) (edge : RawArc Ptr vbits cbits) : Prop :=
  ∃ sourcePtr arcPtr, heap[p]? = some (.pair sourcePtr arcPtr) ∧
    BitsAt heap sourcePtr edge.1 ∧ ArcAt heap arcPtr edge.2

def TraceAt (heap : Heap) (p : Ptr) (path : Trace Ptr vbits cbits) : Prop :=
  ∃ pointers, ListAt heap p pointers ∧ List.Forall₂ (RawArcAt heap) pointers path

def CandidateAt (heap : Heap) (p : Ptr) (candidate : Candidate Ptr vbits cbits) : Prop :=
  ∃ vertexPtr pathPtr, heap[p]? = some (.pair vertexPtr pathPtr) ∧
    BitsAt heap vertexPtr candidate.vertex ∧ TraceAt heap pathPtr candidate.reversePath

def StoredAt (heap : Heap) (p : Ptr) (stored : Bits cbits × Trace Ptr vbits cbits) : Prop :=
  ∃ distancePtr pathPtr, heap[p]? = some (.pair distancePtr pathPtr) ∧
    BitsAt heap distancePtr stored.1 ∧ TraceAt heap pathPtr stored.2

def TreeAt {α : Type*} (R : Heap → Ptr → α → Prop) (heap : Heap)
    {n : ℕ} (p : Ptr) (tree : Radix α n) : Prop :=
  ∃ pointers : Radix Ptr n, TrieAt heap p pointers ∧ Radix.Related (R heap) pointers tree

abbrev QueueAt (heap : Heap) (p : Ptr) (queue : Queue Ptr vbits cbits) :=
  TreeAt CandidateAt heap p queue

abbrev SettledAt (heap : Heap) (p : Ptr) (settled : Settled Ptr vbits cbits) :=
  TreeAt StoredAt heap p settled

abbrev GraphAt (heap : Heap) (p : Ptr) (graph : Graph Ptr vbits cbits) :=
  TreeAt ArcAt heap p graph

theorem ArcAt.allocated {heap : Heap} {p : Ptr} {edge : Arc Ptr vbits cbits}
    (h : ArcAt heap p edge) : p < heap.length := by
  obtain ⟨_, _, _, hc, _⟩ := h
  exact List.getElem?_eq_some_iff.mp hc |>.1

theorem RawArcAt.allocated {heap : Heap} {p : Ptr} {edge : RawArc Ptr vbits cbits}
    (h : RawArcAt heap p edge) : p < heap.length := by
  obtain ⟨_, _, hc, _⟩ := h
  exact List.getElem?_eq_some_iff.mp hc |>.1

theorem TraceAt.allocated {heap : Heap} {p : Ptr} {path : Trace Ptr vbits cbits}
    (h : TraceAt heap p path) : p < heap.length := by
  obtain ⟨_, hlist, _⟩ := h
  exact hlist.allocated

theorem CandidateAt.allocated {heap : Heap} {p : Ptr} {candidate : Candidate Ptr vbits cbits}
    (h : CandidateAt heap p candidate) : p < heap.length := by
  obtain ⟨_, _, hc, _⟩ := h
  exact List.getElem?_eq_some_iff.mp hc |>.1

theorem StoredAt.allocated {heap : Heap} {p : Ptr} {stored : Bits cbits × Trace Ptr vbits cbits}
    (h : StoredAt heap p stored) : p < heap.length := by
  obtain ⟨_, _, hc, _⟩ := h
  exact List.getElem?_eq_some_iff.mp hc |>.1

theorem TreeAt.allocated {α : Type*} {R : Heap → Ptr → α → Prop} {heap : Heap}
    {n : ℕ} {p : Ptr} {tree : Radix α n} (h : TreeAt R heap p tree) : p < heap.length := by
  obtain ⟨_, htree, _⟩ := h
  exact htree.allocated

theorem ArcAt.mono {old new : Heap} (hext : Extends old new)
    {p : Ptr} {edge : Arc Ptr vbits cbits} (h : ArcAt old p edge) : ArcAt new p edge := by
  obtain ⟨tp, wlp, wp, hc, hw, ht, hweight, hl⟩ := h
  exact ⟨tp, wlp, wp, hext.lookup hc, hext.lookup hw, ht.mono hext, hweight.mono hext,
    lt_of_lt_of_le hl hext.length_le⟩

theorem RawArcAt.mono {old new : Heap} (hext : Extends old new)
    {p : Ptr} {edge : RawArc Ptr vbits cbits} (h : RawArcAt old p edge) : RawArcAt new p edge := by
  obtain ⟨sp, ap, hc, hs, ha⟩ := h
  exact ⟨sp, ap, hext.lookup hc, hs.mono hext, ha.mono hext⟩

theorem TraceAt.mono {old new : Heap} (hext : Extends old new)
    {p : Ptr} {path : Trace Ptr vbits cbits} (h : TraceAt old p path) : TraceAt new p path := by
  obtain ⟨pointers, hlist, hitems⟩ := h
  refine ⟨pointers, hlist.mono hext, ?_⟩
  clear hlist
  induction hitems with
  | nil => exact .nil
  | cons hx hs ih => exact .cons (hx.mono hext) ih

theorem CandidateAt.mono {old new : Heap} (hext : Extends old new)
    {p : Ptr} {candidate : Candidate Ptr vbits cbits} (h : CandidateAt old p candidate) :
    CandidateAt new p candidate := by
  obtain ⟨vp, pp, hc, hv, hp⟩ := h
  exact ⟨vp, pp, hext.lookup hc, hv.mono hext, hp.mono hext⟩

theorem StoredAt.mono {old new : Heap} (hext : Extends old new)
    {p : Ptr} {stored : Bits cbits × Trace Ptr vbits cbits} (h : StoredAt old p stored) :
    StoredAt new p stored := by
  obtain ⟨dp, pp, hc, hd, hp⟩ := h
  exact ⟨dp, pp, hext.lookup hc, hd.mono hext, hp.mono hext⟩

theorem TreeAt.mono {α : Type*} {R : Heap → Ptr → α → Prop} {old new : Heap}
    (hext : Extends old new) (hR : ∀ p value, R old p value → R new p value)
    {n : ℕ} {p : Ptr} {tree : Radix α n} (h : TreeAt R old p tree) : TreeAt R new p tree := by
  obtain ⟨pointers, htree, hitems⟩ := h
  exact ⟨pointers, htree.mono hext, hitems.imp _ hR⟩

/-- One shared raw-arc record. -/
def storeRawArc (source arc : Ptr) : Program Ptr := Program.allocate (.pair source arc)

theorem storeRawArc_correct {heap : Heap} (hh : Valid heap)
    {source arc : Ptr} {s : Bits vbits} {edge : Arc Ptr vbits cbits}
    (hs : BitsAt heap source s) (he : ArcAt heap arc edge) :
    SafeRun heap (storeRawArc source arc heap) ∧
      RawArcAt (storeRawArc source arc heap).heap (storeRawArc source arc heap).value (s, edge) := by
  have hr := safe_allocate heap hh (.pair source arc) (by
    intro p hp
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hs.allocated
    · exact he.allocated)
  refine ⟨hr, ⟨source, arc, ?_, hs.mono hr.1, he.mono hr.1⟩⟩
  simp [storeRawArc, Program.allocate]

/-- Extending a path uses one list allocation and retains the old tail. -/
def storeTraceCons (arc path : Ptr) : Program Ptr := Program.allocate (.cons arc path)

theorem storeTraceCons_correct {heap : Heap} (hh : Valid heap)
    {arc path : Ptr} {edge : RawArc Ptr vbits cbits} {trace : Trace Ptr vbits cbits}
    (he : RawArcAt heap arc edge) (hp : TraceAt heap path trace) :
    SafeRun heap (storeTraceCons arc path heap) ∧
      TraceAt (storeTraceCons arc path heap).heap (storeTraceCons arc path heap).value (edge :: trace) := by
  obtain ⟨pointers, hlist, hitems⟩ := hp
  have hs := allocate_cons hh he.allocated hlist
  have hext := hs.1.1
  refine ⟨hs.1, arc :: pointers, hs.2, .cons (he.mono hext) ?_⟩
  clear hlist hs
  induction hitems with
  | nil => exact .nil
  | cons hx ht ih => exact .cons (hx.mono hext) ih

def storeCandidate (vertex path : Ptr) : Program Ptr := Program.allocate (.pair vertex path)

theorem storeCandidate_correct {heap : Heap} (hh : Valid heap)
    {vertex path : Ptr} {v : Bits vbits} {trace : Trace Ptr vbits cbits}
    (hv : BitsAt heap vertex v) (hp : TraceAt heap path trace) :
    SafeRun heap (storeCandidate vertex path heap) ∧
      CandidateAt (storeCandidate vertex path heap).heap (storeCandidate vertex path heap).value
        ⟨v, trace⟩ := by
  have hr := safe_allocate heap hh (.pair vertex path) (by
    intro p hm
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact hv.allocated
    · exact hp.allocated)
  refine ⟨hr, ⟨vertex, path, ?_, hv.mono hr.1, hp.mono hr.1⟩⟩
  simp [storeCandidate, Program.allocate]

def storeSettled (distance path : Ptr) : Program Ptr := Program.allocate (.pair distance path)

theorem storeSettled_correct {heap : Heap} (hh : Valid heap)
    {distance path : Ptr} {d : Bits cbits} {trace : Trace Ptr vbits cbits}
    (hd : BitsAt heap distance d) (hp : TraceAt heap path trace) :
    SafeRun heap (storeSettled distance path heap) ∧
      StoredAt (storeSettled distance path heap).heap (storeSettled distance path heap).value (d, trace) := by
  have hr := safe_allocate heap hh (.pair distance path) (by
    intro p hm
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact hd.allocated
    · exact hp.allocated)
  refine ⟨hr, ⟨distance, path, ?_, hd.mono hr.1, hp.mono hr.1⟩⟩
  simp [storeSettled, Program.allocate]

end WeightedMIS.EfficientSearch.Pointer
