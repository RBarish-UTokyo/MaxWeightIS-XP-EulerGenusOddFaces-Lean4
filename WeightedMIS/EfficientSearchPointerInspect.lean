module

public import WeightedMIS.EfficientSearchPointerTrie

/-! # Executed record and dictionary-status inspections -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Pointer

open WeightedMIS.PointerMemory

def readPair (p : Ptr) : Program (Option (Ptr × Ptr)) := fun heap =>
  let loaded := Program.load p heap
  let value := match loaded.value with
    | some (.pair a b) => some (a, b)
    | _ => none
  ⟨value, heap, .control :: loaded.trace⟩

theorem readPair_refines {heap : Heap} (hh : Valid heap) {p a b : Ptr}
    (hc : heap[p]? = some (.pair a b)) :
    SafeRun heap (readPair p heap) ∧ (readPair p heap).value = some (a, b) ∧
      (readPair p heap).heap = heap ∧ (readPair p heap).trace.length = 2 := by
  have hs := safe_prefix (safe_change_value
    (safe_load heap hh p (List.getElem?_eq_some_iff.mp hc |>.1)) (some (a, b)))
    [.control] (by intro e he q hq; simp_all [Event.references])
  exact ⟨by simpa [readPair, Program.load, hc] using hs,
    by simp [readPair, Program.load, hc], rfl, rfl⟩

def emptyListPointer (p : Ptr) : Program (Option Bool) := fun heap =>
  let loaded := Program.load p heap
  let value := match loaded.value with
    | some .nil => some true
    | some (.cons _ _) => some false
    | _ => none
  ⟨value, heap, .control :: loaded.trace⟩

theorem emptyListPointer_refines {heap : Heap} (hh : Valid heap) {p : Ptr} {items : List Ptr}
    (hl : ListAt heap p items) :
    SafeRun heap (emptyListPointer p heap) ∧
      (emptyListPointer p heap).value = some items.isEmpty ∧
      (emptyListPointer p heap).heap = heap ∧ (emptyListPointer p heap).trace.length = 2 := by
  have hs := safe_prefix (safe_change_value (safe_load heap hh p hl.allocated)
    (some items.isEmpty)) [.control] (by intro e he q hq; simp_all [Event.references])
  cases hl with
  | nil hc =>
    exact ⟨by simpa [emptyListPointer, Program.load, hc] using hs,
      by simp [emptyListPointer, Program.load, hc], rfl, rfl⟩
  | cons hc ht =>
    exact ⟨by simpa [emptyListPointer, Program.load, hc] using hs,
      by simp [emptyListPointer, Program.load, hc], rfl, rfl⟩

def lookupEmptyPointer (n : ℕ) (key tree : Ptr) : Program (Option Bool) := fun heap =>
  let looked := lookupPointer n key tree heap
  match looked.value with
  | none => ⟨none, looked.heap, looked.trace⟩
  | some items =>
      let checked := emptyListPointer items looked.heap
      ⟨checked.value, checked.heap, looked.trace ++ checked.trace⟩

theorem lookupEmptyPointer_refines {α : Type*} {R : Heap → Ptr → α → Prop}
    {n : ℕ} {heap : Heap} (hh : Valid heap) {kp tp : Ptr} {key : Bits n} {tree : Radix α n}
    (hk : BitsAt heap kp key) (ht : TreeAt R heap tp tree) :
    SafeRun heap (lookupEmptyPointer n kp tp heap) ∧
      (lookupEmptyPointer n kp tp heap).value = some (Radix.lookup key tree).1.isEmpty ∧
      (lookupEmptyPointer n kp tp heap).heap = heap ∧
      (lookupEmptyPointer n kp tp heap).trace.length ≤ 3 * (Radix.lookup key tree).2 + 2 := by
  obtain ⟨hls, out, hlv, hlh, ⟨pointers, hlr, hrel⟩, hlcost⟩ := lookup_tree_refines hh hk ht
  have hlr' : ListAt (lookupPointer n kp tp heap).heap out pointers := by rw [hlh]; exact hlr
  obtain ⟨hcs, hcv, hch, hccost⟩ := emptyListPointer_refines hls.2.1 hlr'
  have hempty : pointers.isEmpty = (Radix.lookup key tree).1.isEmpty := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.isEmpty_iff, ← List.length_eq_zero_iff]
    rw [hrel.length_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [lookupEmptyPointer, hlv] using safe_join hls hcs
  · simpa [lookupEmptyPointer, hlv, hempty] using hcv
  · simpa [lookupEmptyPointer, hlv, hlh] using hch
  · simp only [lookupEmptyPointer, hlv, List.length_append]
    omega

end WeightedMIS.EfficientSearch.Pointer
