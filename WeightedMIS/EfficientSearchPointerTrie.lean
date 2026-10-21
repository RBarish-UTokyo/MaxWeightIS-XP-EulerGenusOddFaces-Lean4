module

public import WeightedMIS.EfficientSearchPointerData
public import WeightedMIS.PointerLookup
public import WeightedMIS.PointerInsert
public import WeightedMIS.PointerPop

/-! # Pointer-trie refinement with structured search payloads -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Pointer

open WeightedMIS.PointerMemory

def ListRep {α : Type*} (R : Heap → Ptr → α → Prop) (heap : Heap)
    (p : Ptr) (values : List α) : Prop :=
  ∃ pointers, ListAt heap p pointers ∧ List.Forall₂ (R heap) pointers values

theorem ListRep.allocated {α : Type*} {R : Heap → Ptr → α → Prop} {heap : Heap}
    {p : Ptr} {values : List α} (h : ListRep R heap p values) : p < heap.length := by
  obtain ⟨_, hlist, _⟩ := h
  exact hlist.allocated

theorem ListRep.mono {α : Type*} {R : Heap → Ptr → α → Prop} {old new : Heap}
    (hext : Extends old new) (hR : ∀ p value, R old p value → R new p value)
    {p : Ptr} {values : List α} (h : ListRep R old p values) : ListRep R new p values := by
  obtain ⟨pointers, hlist, hrel⟩ := h
  exact ⟨pointers, hlist.mono hext, hrel.imp hR⟩

theorem lookup_tree_refines {α : Type*} {R : Heap → Ptr → α → Prop}
    {n : ℕ} {heap : Heap} (hh : Valid heap) {kp tp : Ptr} {key : Bits n} {tree : Radix α n}
    (hk : BitsAt heap kp key) (ht : TreeAt R heap tp tree) :
    SafeRun heap (lookupPointer n kp tp heap) ∧
      ∃ out, (lookupPointer n kp tp heap).value = some out ∧
        (lookupPointer n kp tp heap).heap = heap ∧
        ListRep R heap out (Radix.lookup key tree).1 ∧
        (lookupPointer n kp tp heap).trace.length ≤ 3 * (Radix.lookup key tree).2 := by
  obtain ⟨pointers, hp, hr⟩ := ht
  obtain ⟨out, ho, he, hl, hb, hcost⟩ := lookupPointer_refines hh hk hp
  have hrel := hr.lookup _ key
  refine ⟨lookupPointer_safe hh hk hp, out, ho, he, ⟨_, hl, hrel.1⟩, ?_⟩
  simpa [hrel.2] using hcost

theorem insert_tree_refines {α : Type*} {R : Heap → Ptr → α → Prop}
    (hmono : ∀ {old new : Heap}, Extends old new → ∀ p value, R old p value → R new p value)
    {n : ℕ} {heap : Heap} (hh : Valid heap) {kp ap tp : Ptr}
    {key : Bits n} {a : α} {tree : Radix α n}
    (hk : BitsAt heap kp key) (ha : R heap ap a) (hallocated : ap < heap.length)
    (ht : TreeAt R heap tp tree) :
    SafeRun heap (insertPointer n kp ap tp heap) ∧
      ∃ out, (insertPointer n kp ap tp heap).value = some out ∧
        TreeAt R (insertPointer n kp ap tp heap).heap out (Radix.insert key a tree).1 ∧
        (insertPointer n kp ap tp heap).trace.length = 4 * (Radix.insert key a tree).2 + 1 := by
  obtain ⟨pointers, hp, hr⟩ := ht
  obtain ⟨hs, out, ho, ht, hc⟩ := insertPointer_refines hh hallocated hk hp
  refine ⟨hs, out, ho, ⟨_, ht, ?_⟩, ?_⟩
  · exact (hr.insert _ key ha).imp _ (hmono hs.1)
  · simpa only [Radix.insert_steps] using hc

inductive PopRep {α : Type*} (R : Heap → Ptr → α → Prop) (heap : Heap) {n : ℕ} :
    PopValue → Option (Bits n × α × Radix α n) → Prop
  | empty : PopRep R heap none none
  | item {kp ap tp : Ptr} {key : Bits n} {a : α} {tree : Radix α n}
      (keyRep : BitsAt heap kp key) (payload : R heap ap a) (treeRep : TreeAt R heap tp tree) :
      PopRep R heap (some (kp, ap, tp)) (some (key, a, tree))

theorem PopRep.none_iff {α : Type*} {R : Heap → Ptr → α → Prop}
    {heap : Heap} {n : ℕ} {raw : PopValue} {semantic : Option (Bits n × α × Radix α n)}
    (h : PopRep R heap raw semantic) : raw = none ↔ semantic = none := by
  cases h <;> simp

theorem PopRep.get_some {α : Type*} {R : Heap → Ptr → α → Prop}
    {heap : Heap} {n : ℕ} {raw : PopValue} {key : Bits n} {a : α} {tree : Radix α n}
    (h : PopRep R heap raw (some (key, a, tree))) :
    ∃ kp ap tp, raw = some (kp, ap, tp) ∧ BitsAt heap kp key ∧
      R heap ap a ∧ TreeAt R heap tp tree := by
  cases h with
  | item hk ha ht => exact ⟨_, _, _, rfl, hk, ha, ht⟩

theorem pop_tree_refines {α : Type*} {R : Heap → Ptr → α → Prop}
    (hmono : ∀ {old new : Heap}, Extends old new → ∀ p value, R old p value → R new p value)
    {n : ℕ} {heap : Heap} (hh : Valid heap) {tp : Ptr} {tree : Radix α n}
    (ht : TreeAt R heap tp tree) :
    SafeRun heap (popPointer n tp heap) ∧
      PopRep R (popPointer n tp heap).heap (popPointer n tp heap).value (Radix.pop tree).1 ∧
      (popPointer n tp heap).trace.length ≤ 8 * (Radix.pop tree).2 := by
  obtain ⟨pointers, hp, hr⟩ := ht
  obtain ⟨hs, hv, hc⟩ := popPointer_refines hh hp
  have hrel := hr.pop _
  refine ⟨hs, ?_, by simpa [hrel.2] using hc⟩
  cases hraw : (Radix.pop pointers).1 with
  | none =>
    have hv' : (popPointer n tp heap).value = none := hv.none_iff.mpr hraw
    cases hsemantic : (Radix.pop tree).1 with
    | none => rw [hv']; exact .empty
    | some result => simp [hraw, hsemantic, Radix.PopRelated] at hrel
  | some result =>
    obtain ⟨key, ap, rawTail⟩ := result
    have hv' : PopAt (popPointer n tp heap).heap (popPointer n tp heap).value
        (some (key, ap, rawTail)) := by simpa [hraw] using hv
    obtain ⟨kp, tailPtr, hvalue, hkey, _, htail⟩ := hv'.get_some
    cases hsemantic : (Radix.pop tree).1 with
    | none => simp [hraw, hsemantic, Radix.PopRelated] at hrel
    | some result =>
      obtain ⟨key', a, tail⟩ := result
      have hhrel := hrel.1
      simp only [hraw, hsemantic, Radix.PopRelated] at hhrel
      obtain ⟨rfl, ha, ht⟩ := hhrel
      rw [hvalue]
      exact .item hkey (hmono hs.1 _ _ ha) ⟨rawTail, htail, ht.imp _ (hmono hs.1)⟩

end WeightedMIS.EfficientSearch.Pointer
