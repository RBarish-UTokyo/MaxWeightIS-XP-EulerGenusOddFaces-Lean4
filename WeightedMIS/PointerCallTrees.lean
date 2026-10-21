module

public import WeightedMIS.PointerStack

/-! # Concrete saved-register frames for trie evaluations -/

@[expose] public section

namespace WeightedMIS.PointerMemory

theorem traceBound_append_iff {xs ys : List Event} {bound : ℕ} :
    TraceBound (xs ++ ys) bound ↔ TraceBound xs bound ∧ TraceBound ys bound := by
  constructor
  · intro h
    constructor
    · intro e he p hp; exact h e (List.mem_append_left ys he) p hp
    · intro e he p hp; exact h e (List.mem_append_right xs he) p hp
  · rintro ⟨hx, hy⟩
    exact traceBound_append hx hy

/-- A call tree includes concrete continuation registers, an exact heap-event
erasure, bounded frame width, and a proved bound on the number of calls. -/
def StackRealizes (bound slots : ℕ) (events : List Event) (tree : CallTree) : Prop :=
  tree.memoryTrace = events ∧ tree.Bounded bound slots ∧ tree.calls ≤ events.length

theorem realizes_code (bound slots : ℕ) (events : List Event) :
    StackRealizes bound slots events (.code events) := ⟨rfl, trivial, by simp [CallTree.calls]⟩

theorem realizes_before {bound slots : ℕ} {events : List Event} {tree : CallTree}
    (ht : StackRealizes bound slots events tree) (before : List Event) :
    StackRealizes bound slots (before ++ events) (.seq (.code before) tree) := by
  refine ⟨?_, ⟨trivial, ht.2.1⟩, ?_⟩
  · simp only [CallTree.memoryTrace, ht.1]
  · simpa only [CallTree.calls, zero_add, List.length_append] using
      le_trans ht.2.2 (Nat.le_add_left events.length before.length)

theorem InsertEval.value_some {h : Heap} {kp a tp : Ptr} {r : Run (Option Ptr)}
    (he : InsertEval h kp a tp r) : ∃ out, r.value = some out := by
  induction he with
  | emptyLeaf => simp [withEvents, leafInsert]
  | bucketLeaf => simp [withEvents, leafInsert]
  | emptyBranch root keyCell child ih =>
    obtain ⟨out, ho⟩ := ih
    simp [withEvents, forkAfter, ho]
  | fork root keyCell child ih =>
    obtain ⟨out, ho⟩ := ih
    simp [withEvents, forkAfter, ho]

/-- Insertion saves the branch direction and untouched sibling across its
recursive call. Rebuilding the parent executes its original allocation. -/
theorem forkAfter_stack {bound : ℕ} {b : Bool} {sibling out : Ptr}
    {r : Run (Option Ptr)} {child : CallTree} (hs : sibling < bound)
    (hv : r.value = some out) (hc : StackRealizes bound 2 r.trace child) :
    ∃ tree, StackRealizes bound 2 (forkAfter b sibling r).trace tree := by
  let write := (Program.allocate (.fork (if b then sibling else out)
    (if b then out else sibling)) r.heap).trace
  let tree := CallTree.seq (.call [.flag b, .pointer sibling] child) (.code write)
  refine ⟨tree, ?_, ?_, ?_⟩
  · simp only [tree, CallTree.memoryTrace, hc.1, forkAfter, hv, write]
  · refine ⟨⟨by simp, ?_, hc.2.1⟩, trivial⟩
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · trivial
    · exact hs
  · have hn := hc.2.2
    simp only [tree, CallTree.calls, add_zero, forkAfter, hv, Program.allocate,
      List.length_append, List.length_cons, List.length_nil]
    omega

/-- Every insertion evaluation admits a concrete stack execution with exactly
the two continuation words needed at each recursive return. -/
theorem InsertEval.stackTree {h : Heap} {kp a tp : Ptr} {r : Run (Option Ptr)}
    (he : InsertEval h kp a tp r) {bound : ℕ} (hpos : 0 < bound)
    (hb : TraceBound r.trace bound) :
    ∃ tree, StackRealizes bound 2 r.trace tree := by
  induction he with
  | emptyLeaf => exact ⟨_, realizes_code _ _ _⟩
  | bucketLeaf => exact ⟨_, realizes_code _ _ _⟩
  | @emptyBranch h key tree tail b r root keyCell child ih =>
    obtain ⟨out, hv⟩ := child.value_some
    have hafter : TraceBound (forkAfter b 0 r).trace bound := (traceBound_append_iff.mp hb).2
    have hchild : TraceBound r.trace bound := by
      rw [forkAfter, hv] at hafter
      exact (traceBound_append_iff.mp hafter).1
    obtain ⟨ct, hct⟩ := ih hchild
    obtain ⟨ft, hft⟩ := forkAfter_stack hpos hv hct
    exact ⟨_, realizes_before hft _⟩
  | @fork h key tree tail left right b r root keyCell child ih =>
    obtain ⟨out, hv⟩ := child.value_some
    have hafter : TraceBound (forkAfter b (if b then left else right) r).trace bound :=
      (traceBound_append_iff.mp hb).2
    have hchild : TraceBound r.trace bound := by
      rw [forkAfter, hv] at hafter
      exact (traceBound_append_iff.mp hafter).1
    have hs : (if b then left else right) < bound := by
      apply hb (.load tree (some (.fork left right)))
      · simp [withEvents, readTwoBefore, Program.load, root]
      · cases b <;> simp [Event.references, Cell.references]
    obtain ⟨ct, hct⟩ := ih hchild
    obtain ⟨ft, hft⟩ := forkAfter_stack hs hv hct
    exact ⟨_, realizes_before hft _⟩

theorem singleCall_realizes {bound slots : ℕ} {events : List Event} {child : CallTree}
    (hc : StackRealizes bound slots events child) (frame : List Word)
    (hf : frame.length ≤ slots ∧ ∀ w ∈ frame, w.Bounded bound)
    (before after : List Event) (hbefore : 1 ≤ before.length) :
    StackRealizes bound slots (before ++ events ++ after)
      (.seq (.code before) (.seq (.call frame child) (.code after))) := by
  refine ⟨?_, ⟨trivial, ⟨⟨hf.1, hf.2, hc.2.1⟩, trivial⟩⟩, ?_⟩
  · simp only [CallTree.memoryTrace, hc.1, List.append_assoc]
  · have h := hc.2.2
    simp only [CallTree.calls, zero_add, add_zero, List.length_append]
    omega

theorem twoCalls_realizes {bound slots : ℕ} {first second : List Event} {a b : CallTree}
    (ha : StackRealizes bound slots first a) (hb : StackRealizes bound slots second b)
    (frame : List Word) (hf : frame.length ≤ slots ∧ ∀ w ∈ frame, w.Bounded bound)
    (before after : List Event) (hbefore : 2 ≤ before.length) :
    StackRealizes bound slots (before ++ (first ++ second) ++ after)
      (.seq (.code before) (.seq (.call frame a) (.seq (.call frame b) (.code after)))) := by
  refine ⟨?_, ⟨trivial, ⟨⟨hf.1, hf.2, ha.2.1⟩, ⟨⟨hf.1, hf.2, hb.2.1⟩, trivial⟩⟩⟩, ?_⟩
  · simp only [CallTree.memoryTrace, ha.1, hb.1, List.append_assoc]
  · have h1 := ha.2.2
    have h2 := hb.2.2
    simp only [CallTree.calls, zero_add, add_zero, List.length_append]
    omega

theorem fork_frame_bound {h : Heap} {tree left right bound : Ptr}
    (root : h[tree]? = some (.fork left right)) (hb : TraceBound (readBefore h tree) bound) :
    [Word.pointer left, Word.pointer right].length ≤ 2 ∧
      ∀ w ∈ [Word.pointer left, Word.pointer right], w.Bounded bound := by
  refine ⟨by simp, ?_⟩
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · apply hb (.load tree (some (.fork left right)))
    · simp [readBefore, Program.load, root]
    · simp [Event.references, Cell.references]
  · apply hb (.load tree (some (.fork left right)))
    · simp [readBefore, Program.load, root]
    · simp [Event.references, Cell.references]

/-- Minimum extraction saves the original pair of child roots. This is enough
to restore the untouched sibling and, after an empty left result, to start the
right search. Both recursive calls are separately saved/restored. -/
theorem PopEval.stackTree {h : Heap} {tp : Ptr} {r : Run PopValue}
    (he : PopEval h tp r) {bound : ℕ} (hb : TraceBound r.trace bound) :
    ∃ tree, StackRealizes bound 2 r.trace tree := by
  induction he with
  | empty => exact ⟨_, realizes_code _ _ _⟩
  | emptyBucket => exact ⟨_, realizes_code _ _ _⟩
  | bucket => exact ⟨_, realizes_code _ _ _⟩
  | @left h tree left right key a left' lp root child found ih =>
    have hsplit := traceBound_append_iff.mp hb
    have hc := (traceBound_append_iff.mp hsplit.2).1
    obtain ⟨ct, hct⟩ := ih hc
    have hf := fork_frame_bound root hsplit.1
    have hs := singleCall_realizes hct _ hf (readBefore h tree)
      (extendPop false right key a left' lp.heap).trace (by simp [readBefore, Program.load])
    exact ⟨_, by simpa only [withEvents, sequenceRuns, List.append_assoc] using hs⟩
  | @right h tree left right key a right' lp rp root leftChild noLeft rightChild found ihl ihr =>
    have hsplit := traceBound_append_iff.mp hb
    have hchildren := (traceBound_append_iff.mp hsplit.2).1
    have hchildren' := traceBound_append_iff.mp hchildren
    obtain ⟨lt, hlt⟩ := ihl hchildren'.1
    obtain ⟨rt, hrt⟩ := ihr hchildren'.2
    have hf := fork_frame_bound root hsplit.1
    have hs := twoCalls_realizes hlt hrt _ hf (readBefore h tree)
      (extendPop true left key a right' rp.heap).trace (by simp [readBefore, Program.load])
    exact ⟨_, by simpa only [withEvents, sequenceRuns, List.append_assoc] using hs⟩
  | @noChildren h tree left right lp rp root leftChild noLeft rightChild noRight ihl ihr =>
    have hsplit := traceBound_append_iff.mp hb
    have hchildren := (traceBound_append_iff.mp hsplit.2).1
    have hchildren' := traceBound_append_iff.mp hchildren
    obtain ⟨lt, hlt⟩ := ihl hchildren'.1
    obtain ⟨rt, hrt⟩ := ihr hchildren'.2
    have hf := fork_frame_bound root hsplit.1
    have hs := twoCalls_realizes hlt hrt _ hf (readBefore h tree) [] (by simp [readBefore, Program.load])
    exact ⟨_, by simpa only [withEvents, sequenceRuns, Program.pure, List.append_assoc] using hs⟩

/-- Lookup is a tail call at every branch, so it needs no continuation frame. -/
theorem LookupEval.stackTree {h : Heap} {kp tp : Ptr} {r : Run (Option Ptr)}
    (_he : LookupEval h kp tp r) (bound : ℕ) :
    ∃ tree, StackRealizes bound 2 r.trace tree := ⟨_, realizes_code _ _ _⟩

end WeightedMIS.PointerMemory
