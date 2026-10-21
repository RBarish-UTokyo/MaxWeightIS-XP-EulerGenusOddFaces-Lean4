module

public import WeightedMIS.PointerEvaluation

/-! # Memory safety of tag-directed extraction -/

@[expose] public section

namespace WeightedMIS.PointerMemory

def PopAllocated (h : Heap) (v : PopValue) : Prop :=
  ∀ k a t, v = some (k, a, t) → k < h.length ∧ a < h.length ∧ t < h.length

theorem leafPointer_safe {h : Heap} (hh : Valid h) {items : Ptr} (hi : items < h.length) :
    SafeRun h (leafPointer items h) ∧ (leafPointer items h).value < (leafPointer items h).heap.length := by
  have hb := load_control_bound hh hi
  by_cases he : h[items]? = some .nil
  · refine ⟨?_, ?_⟩
    · simpa [leafPointer, Program.load, Program.pure, he] using
        safe_prefix (safe_pure h hh 0) _ hb
    · simpa [leafPointer, Program.load, Program.pure, he] using
        (List.getElem?_eq_some_iff.mp hh.1 |>.1)
  · have hs := safe_allocate h hh (.bucket items) (by
      intro q hq; simp only [Cell.references, List.mem_singleton] at hq; exact hq ▸ hi)
    refine ⟨?_, ?_⟩
    · simpa [leafPointer, Program.load, he] using safe_prefix hs _ hb
    · simp [leafPointer, Program.load, Program.allocate, he]

theorem joinPointer_safe {h : Heap} (hh : Valid h) {left right : Ptr}
    (hl : left < h.length) (hr : right < h.length) :
    SafeRun h (joinPointer left right h) ∧
      (joinPointer left right h).value < (joinPointer left right h).heap.length := by
  have hb := traceBound_append (load_control_bound hh hl) (safe_load h hh right hr).2.2.1
  by_cases he : h[left]? = some .nil ∧ h[right]? = some .nil
  · refine ⟨?_, ?_⟩
    · simpa [joinPointer, Program.load, Program.pure, he, List.append_assoc] using
        safe_prefix (safe_pure h hh 0) _ hb
    · simpa [joinPointer, Program.load, Program.pure, he] using
        (List.getElem?_eq_some_iff.mp hh.1 |>.1)
  · have hs := safe_allocate h hh (.fork left right) (by
      intro q hq
      simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> assumption)
    refine ⟨?_, ?_⟩
    · simpa [joinPointer, Program.load, he, List.append_assoc] using safe_prefix hs _ hb
    · simp [joinPointer, Program.load, Program.allocate, he]

theorem extendPop_safe {h : Heap} (hh : Valid h) (b : Bool) {sibling key a tree : Ptr}
    (hs : sibling < h.length) (hk : key < h.length) (ha : a < h.length) (ht : tree < h.length) :
    SafeRun h (extendPop b sibling key a tree h) ∧
      PopAllocated (extendPop b sibling key a tree h).heap (extendPop b sibling key a tree h).value := by
  have hl : (if b then sibling else tree) < h.length := by cases b <;> assumption
  have hr : (if b then tree else sibling) < h.length := by cases b <;> assumption
  obtain ⟨hj, hv⟩ := joinPointer_safe hh hl hr
  let joined := joinPointer (if b then sibling else tree) (if b then tree else sibling) h
  have hkey : key < joined.heap.length := lt_of_lt_of_le hk hj.1.length_le
  have hab := safe_allocate joined.heap hj.2.1 (.bit b key) (by
    intro q hq; simp only [Cell.references, List.mem_singleton] at hq; exact hq ▸ hkey)
  refine ⟨?_, ?_⟩
  · exact safe_change_value (safe_join hj hab) _
  · intro k v t he
    simp only [extendPop, Program.allocate, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    change joined.heap.length < (joined.heap ++ [Cell.bit b key]).length ∧
      a < (joined.heap ++ [Cell.bit b key]).length ∧ joined.value < (joined.heap ++ [Cell.bit b key]).length
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
    exact ⟨Nat.lt_succ_self _, Nat.lt_succ_of_lt (lt_of_lt_of_le ha hj.1.length_le),
      Nat.lt_succ_of_lt hv⟩

/-- Every tag-directed extraction from a valid heap remains memory safe; all
three returned pointers refer to actually allocated cells. -/
theorem PopEval.safe {h : Heap} {tree : Ptr} {result : Run PopValue}
    (he : PopEval h tree result) : Valid h →
    SafeRun h result ∧ PopAllocated result.heap result.value := by
  induction he with
  | @empty h tree root =>
    intro hh
    have hb := load_control_bound hh (List.getElem?_eq_some_iff.mp root |>.1)
    refine ⟨?_, ?_⟩
    · exact safe_prefix (safe_pure h hh none) _ hb
    · intro k a t hv; cases hv
  | @emptyBucket h tree items root item =>
    intro hh
    have hb := traceBound_append
      (load_control_bound hh (List.getElem?_eq_some_iff.mp root |>.1))
      (safe_load h hh items (List.getElem?_eq_some_iff.mp item |>.1)).2.2.1
    refine ⟨?_, ?_⟩
    · simpa only [readTwoBefore, readBefore, List.cons_append, Program.pure, List.append_nil] using safe_prefix (safe_pure h hh none) _ hb
    · intro k a t hv; cases hv
  | @bucket h tree items a tail root item =>
    intro hh
    have ha : a < h.length := hh.2 _ _ item a (by simp [Cell.references])
    have ht : tail < h.length := hh.2 _ _ item tail (by simp [Cell.references])
    obtain ⟨hl, hvalue⟩ := leafPointer_safe hh ht
    have hb := traceBound_append
      (load_control_bound hh (List.getElem?_eq_some_iff.mp root |>.1))
      (safe_load h hh items (List.getElem?_eq_some_iff.mp item |>.1)).2.2.1
    refine ⟨?_, ?_⟩
    · simpa only [withEvents, readTwoBefore, readBefore, List.cons_append] using
        safe_prefix (safe_change_value hl (some (0, a, (leafPointer tail h).value))) _ hb
    · intro k v t hv
      simp only [withEvents, Option.some.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact ⟨List.getElem?_eq_some_iff.mp hl.2.1.1 |>.1,
        lt_of_lt_of_le ha hl.1.length_le, hvalue⟩
  | @left h tree left right key a left' lp root child found ih =>
    intro hh
    obtain ⟨hl, hv⟩ := ih hh
    obtain ⟨hk, ha, ht⟩ := hv _ _ _ found
    have hright : right < lp.heap.length := lt_of_lt_of_le
      (hh.2 _ _ root right (by simp [Cell.references])) hl.1.length_le
    obtain ⟨he, hval⟩ := extendPop_safe hl.2.1 false hright hk ha ht
    have hb := load_control_bound hh (List.getElem?_eq_some_iff.mp root |>.1)
    exact ⟨safe_prefix (safe_join hl he) _ hb, hval⟩
  | @right h tree left right key a right' lp rp root leftChild noLeft rightChild found ihl ihr =>
    intro hh
    obtain ⟨hl, _⟩ := ihl hh
    obtain ⟨hr, hv⟩ := ihr hl.2.1
    obtain ⟨hk, ha, ht⟩ := hv _ _ _ found
    have hleft : left < rp.heap.length := lt_of_lt_of_le
      (hh.2 _ _ root left (by simp [Cell.references])) (hl.1.trans hr.1).length_le
    obtain ⟨he, hval⟩ := extendPop_safe hr.2.1 true hleft hk ha ht
    have hb := load_control_bound hh (List.getElem?_eq_some_iff.mp root |>.1)
    exact ⟨safe_prefix (safe_join (safe_join hl hr) he) _ hb, hval⟩
  | @noChildren h tree left right lp rp root leftChild noLeft rightChild noRight ihl ihr =>
    intro hh
    obtain ⟨hl, _⟩ := ihl hh
    obtain ⟨hr, _⟩ := ihr hl.2.1
    have hb := load_control_bound hh (List.getElem?_eq_some_iff.mp root |>.1)
    refine ⟨safe_prefix (safe_join (safe_join hl hr) (safe_pure rp.heap hr.2.1 none)) _ hb, ?_⟩
    intro k a t hv; cases hv

end WeightedMIS.PointerMemory
