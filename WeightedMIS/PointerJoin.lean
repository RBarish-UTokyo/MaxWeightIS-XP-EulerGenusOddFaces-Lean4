module

public import WeightedMIS.PointerLookup

/-! # Constant-allocation canonical trie constructors -/

@[expose] public section

namespace WeightedMIS.PointerMemory

open WeightedMIS.EfficientSearch

theorem TrieAt.emptyRoot_iff {h : Heap} {n p} {t : Radix Ptr n} (ht : TrieAt h p t) :
    h[p]? = some .nil ↔ t.emptyRoot = true := by
  cases ht <;> simp_all [Radix.emptyRoot]

/-- Construct a canonical leaf by inspecting the shared list head. -/
def leafPointer (items : Ptr) : Program Ptr := fun h =>
  let loaded := Program.load items h
  let result := if loaded.value = some .nil then Program.pure 0 h
    else Program.allocate (.bucket items) h
  ⟨result.value, result.heap, .control :: (loaded.trace ++ result.trace)⟩

theorem leafPointer_refines {h : Heap} (hh : Valid h) {items : Ptr} {xs : List Ptr}
    (hx : ListAt h items xs) :
    SafeRun h (leafPointer items h) ∧
      TrieAt (leafPointer items h).heap (leafPointer items h).value (Radix.leaf xs) ∧
      (leafPointer items h).trace.length ≤ 3 := by
  have hb := load_control_bound hh hx.allocated
  cases hx with
  | nil hc =>
    refine ⟨?_, ?_, ?_⟩
    · simpa [leafPointer, Program.load, Program.pure, hc] using safe_prefix (safe_pure h hh 0) _ hb
    · simpa [leafPointer, Program.load, Program.pure, hc, Radix.leaf] using TrieAt.empty (n := 0) hh.1
    · simp [leafPointer, Program.load, Program.pure, hc]
  | cons hc ht =>
    obtain ⟨ha, hbuck⟩ := allocate_bucket hh (.cons hc ht)
    refine ⟨?_, ?_, ?_⟩
    · simpa [leafPointer, Program.load, hc] using safe_prefix ha _ hb
    · simpa [leafPointer, Program.load, hc, Radix.leaf] using hbuck
    · simp [leafPointer, Program.load, Program.allocate, hc]

/-- Join two shared subtries, allocating a branch exactly when at least one
child is nonempty. Both root-tag loads are recorded. -/
def joinPointer (left right : Ptr) : Program Ptr := fun h =>
  let l := Program.load left h
  let r := Program.load right h
  let result := if l.value = some .nil ∧ r.value = some .nil then Program.pure 0 h
    else Program.allocate (.fork left right) h
  ⟨result.value, result.heap, .control :: (l.trace ++ r.trace ++ result.trace)⟩

theorem joinPointer_refines {h : Heap} (hh : Valid h) {n : ℕ} {left right : Ptr}
    {l r : Radix Ptr n} (hl : TrieAt h left l) (hr : TrieAt h right r) :
    SafeRun h (joinPointer left right h) ∧
      TrieAt (joinPointer left right h).heap (joinPointer left right h).value (Radix.join l r) ∧
      (joinPointer left right h).trace.length ≤ 4 := by
  have hb := traceBound_append (load_control_bound hh hl.allocated)
    (safe_load h hh right hr.allocated).2.2.1
  have heq : (h[left]? = some .nil ∧ h[right]? = some .nil) ↔
      (l.emptyRoot && r.emptyRoot) = true := by
    rw [Bool.and_eq_true, hl.emptyRoot_iff, hr.emptyRoot_iff]
  by_cases he : (l.emptyRoot && r.emptyRoot) = true
  · have hm := heq.mpr he
    refine ⟨?_, ?_, ?_⟩
    · simpa [joinPointer, Program.load, Program.pure, hm, List.append_assoc] using
        safe_prefix (safe_pure h hh 0) _ hb
    · simpa [joinPointer, Program.load, Program.pure, hm, Radix.join, he] using
        TrieAt.empty (n := n + 1) hh.1
    · simp [joinPointer, Program.load, Program.pure, hm]
  · have hm : ¬(h[left]? = some .nil ∧ h[right]? = some .nil) := fun h => he (heq.mp h)
    obtain ⟨ha, hat⟩ := allocate_fork hh hl hr
    refine ⟨?_, ?_, ?_⟩
    · simpa [joinPointer, Program.load, hm, List.append_assoc] using safe_prefix ha _ hb
    · simpa [joinPointer, Program.load, hm, Radix.join, he] using hat
    · simp [joinPointer, Program.load, Program.allocate, hm]

end WeightedMIS.PointerMemory
