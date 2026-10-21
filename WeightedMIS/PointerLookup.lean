module

public import WeightedMIS.PointerRepresentations

/-! # Executed pointer-trie lookup and its refinement -/

@[expose] public section

namespace WeightedMIS.PointerMemory

open WeightedMIS.EfficientSearch

/-- Each nonempty branch loads one key cell and one trie cell. The fuel is the
key width; its decrement is a control transition. Ill-shaped memory returns
`none`, whereas a successful empty lookup returns the shared empty-list pointer. -/
def lookupPointer : ℕ → Ptr → Ptr → Program (Option Ptr)
  | 0, _key, tree, h =>
      let loaded := Program.load tree h
      let before := Event.control :: loaded.trace
      match loaded.value with
      | some .nil => ⟨some 0, h, before⟩
      | some (.bucket items) => ⟨some items, h, before⟩
      | _ => ⟨none, h, before⟩
  | n + 1, key, tree, h =>
      let loaded := Program.load tree h
      let before := Event.control :: loaded.trace
      match loaded.value with
      | some .nil => ⟨some 0, h, before⟩
      | some (.fork left right) =>
          let keyCell := Program.load key h
          match keyCell.value with
          | some (.bit b tail) =>
              let rest := lookupPointer n tail (if b then right else left) h
              ⟨rest.value, rest.heap, before ++ keyCell.trace ++ rest.trace⟩
          | _ => ⟨none, h, before ++ keyCell.trace⟩
      | _ => ⟨none, h, before⟩

theorem load_control_bound {h : Heap} (hh : Valid h) {p : Ptr} (hp : p < h.length) :
    TraceBound (.control :: (Program.load p h).trace) h.length := by
  intro e he q hq
  rcases List.mem_cons.mp he with rfl | he
  · simp [Event.references] at hq
  · exact (safe_load h hh p hp).2.2.1 e he q hq

/-- Actual RAM output represents exactly the existing radix lookup. This also
bounds the executed memory/control trace by three times its structural count. -/
theorem lookupPointer_refines {n : ℕ} {h : Heap} (hh : Valid h)
    {kp tp : Ptr} {key : Bits n} {tree : Radix Ptr n}
    (hk : BitsAt h kp key) (ht : TrieAt h tp tree) :
    ∃ out, (lookupPointer n kp tp h).value = some out ∧
      (lookupPointer n kp tp h).heap = h ∧
      ListAt h out (Radix.lookup key tree).1 ∧
      TraceBound (lookupPointer n kp tp h).trace h.length ∧
      (lookupPointer n kp tp h).trace.length ≤ 3 * (Radix.lookup key tree).2 := by
  induction key generalizing kp tp with
  | nil =>
    cases ht with
    | empty hc =>
      refine ⟨0, ?_, ?_, .nil hh.1, ?_, ?_⟩
      · simp [lookupPointer, Program.load, hc]
      · simp [lookupPointer, Program.load, hc]
      · simpa [lookupPointer, Program.load, hc] using load_control_bound hh (List.getElem?_eq_some_iff.mp hc |>.1)
      · simp [lookupPointer, Program.load, hc, Radix.lookup]
    | bucket hc hl =>
      refine ⟨_, ?_, ?_, hl, ?_, ?_⟩
      · simp [lookupPointer, Program.load, hc]
      · simp [lookupPointer, Program.load, hc]
      · simpa [lookupPointer, Program.load, hc] using load_control_bound hh (List.getElem?_eq_some_iff.mp hc |>.1)
      · simp [lookupPointer, Program.load, hc, Radix.lookup]
  | @cons n b key ih =>
    cases ht with
    | empty hc =>
      refine ⟨0, ?_, ?_, .nil hh.1, ?_, ?_⟩
      · simp [lookupPointer, Program.load, hc]
      · simp [lookupPointer, Program.load, hc]
      · simpa [lookupPointer, Program.load, hc] using load_control_bound hh (List.getElem?_eq_some_iff.mp hc |>.1)
      · simp [lookupPointer, Program.load, hc, Radix.lookup]
    | @fork _ left right _ l r hc hl hr =>
      cases hk with
      | @cons _ kt _ _ _ hkey htail =>
        have selected : TrieAt h (if b then right else left) (if b then r else l) := by
          cases b <;> assumption
        obtain ⟨out, ho, hheap, hlist, hbound, hlen⟩ := ih htail selected
        refine ⟨out, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [lookupPointer, Program.load, hc, hkey] using ho
        · simpa [lookupPointer, Program.load, hc, hkey] using hheap
        · simpa only [Radix.lookup] using hlist
        · have hpre := load_control_bound hh (show tp < h.length from
            List.getElem?_eq_some_iff.mp hc |>.1)
          have hkeyb := (safe_load h hh kp (List.getElem?_eq_some_iff.mp hkey |>.1)).2.2.1
          simpa [lookupPointer, Program.load, hc, hkey] using
            traceBound_append (traceBound_append hpre hkeyb) hbound
        · simp only [lookupPointer, Program.load, hc, hkey, Radix.lookup,
            List.length_append, List.length_cons, List.length_nil]
          omega

theorem lookupPointer_safe {n : ℕ} {h : Heap} (hh : Valid h)
    {kp tp : Ptr} {key : Bits n} {tree : Radix Ptr n}
    (hk : BitsAt h kp key) (ht : TrieAt h tp tree) :
    SafeRun h (lookupPointer n kp tp h) := by
  obtain ⟨out, hv, hheap, hl, hb, hc⟩ := lookupPointer_refines hh hk ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hheap]
  · rwa [hheap]
  · rwa [hheap]
  · simp [hheap]

end WeightedMIS.PointerMemory
