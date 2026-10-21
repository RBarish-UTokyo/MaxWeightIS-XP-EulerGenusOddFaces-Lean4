module

public import WeightedMIS.CompiledTrie
public import WeightedMIS.EfficientSearchCodeBounds
public import WeightedMIS.EfficientSearchPointerTrie

/-!
# Shared facts for linked-list register combinators

The empty list is the shared null cell, and one executed `cons` allocation
extends a represented list by one item without copying its tail. These two
facts are used by the map, filter, zip, and reverse combinators.
-/

@[expose] public section

namespace WeightedMIS.RegisterListCommon

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer

/-- The null address represents the empty list in every valid heap. -/
theorem listRep_null {α : Type*} {R : Heap → Ptr → α → Prop} {h : Heap} (hh : Valid h) :
    ListRep R h 0 [] :=
  ⟨[], .nil hh.1, .nil⟩

/-- Every item address stored in a represented list of a valid heap is allocated. -/
theorem ListAt.head_allocated {h : Heap} (hh : Valid h) {p a tail : Ptr}
    (cell : h[p]? = some (.cons a tail)) : a < h.length :=
  hh.2 p _ cell a (by simp [Cell.references])

/-- One `cons` allocation keeps the heap valid and represents the extended list. -/
theorem allocate_consRep {α : Type*} {R : Heap → Ptr → α → Prop}
    (mono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, R h ptr x → R h' ptr x)
    {h : Heap} (hh : Valid h) {a tail : Ptr} {x : α} {xs : List α}
    (ha : R h a x) (hal : a < h.length) (ht : ListRep R h tail xs) :
    Extends h (h ++ [.cons a tail]) ∧ Valid (h ++ [.cons a tail]) ∧
      ListRep R (h ++ [.cons a tail]) h.length (x :: xs) := by
  obtain ⟨pointers, hlist, hrel⟩ := ht
  obtain ⟨hs, hl⟩ := allocate_cons hh hal hlist
  have hext : Extends h (h ++ [.cons a tail]) := ⟨[.cons a tail], rfl⟩
  refine ⟨hext, hs.2.1, a :: pointers, ?_, .cons (mono hext a x ha) (hrel.imp (mono hext))⟩
  simpa [Program.allocate] using hl

/-- The fixed closing sequence: allocate one `cons` cell and return it. -/
theorem within_consRet {p : ℕ} (code : Code p) (h : Heap) {regs : Registers}
    {dst head tail : Register} {a t : Ptr}
    (hhead : regs head = .pointer a) (htail : regs tail = .pointer t) :
    Within code h regs (.allocate dst (.cons (.register head) (.register tail))
      (.ret [.register dst])) [.pointer h.length] (h ++ [.cons a t]) 11 := by
  apply Within.allocate (budget := 3) (c := .cons a t)
  · simp [CellExpr.eval, Atom.eval, hhead, htail, Value.asPointer]
  · simpa [values, Atom.eval] using
      Within.ret code (h ++ [.cons a t]) (Function.update regs dst (.pointer h.length))
        [.register dst]

theorem sum_map_const {α : Type*} (xs : List α) (b : ℕ) :
    (xs.map (fun _ => b)).sum = b * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; ring

end WeightedMIS.RegisterListCommon
