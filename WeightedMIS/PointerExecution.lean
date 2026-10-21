module

public import WeightedMIS.PointerEvaluation

/-! # Operational authenticity of heap traces -/

@[expose] public section

namespace WeightedMIS.PointerMemory

inductive HeapStep : Heap → Event → Heap → Prop
  | load (h : Heap) (p : Ptr) : HeapStep h (.load p h[p]?) h
  | allocate (h : Heap) (c : Cell) : HeapStep h (.allocate h.length c) (h ++ [c])
  | copyPointer (h : Heap) (p : Ptr) : HeapStep h (.copyPointer p) h
  | copyFlag (h : Heap) (b : Bool) : HeapStep h (.copyFlag b) h
  | control (h : Heap) : HeapStep h .control h

inductive HeapExec : Heap → List Event → Heap → Prop
  | nil (h : Heap) : HeapExec h [] h
  | cons {h h' h'' : Heap} {e : Event} {es : List Event}
      (head : HeapStep h e h') (tail : HeapExec h' es h'') : HeapExec h (e :: es) h''

theorem HeapExec.append {h h' h'' : Heap} {xs ys : List Event}
    (hx : HeapExec h xs h') (hy : HeapExec h' ys h'') : HeapExec h (xs ++ ys) h'' := by
  induction hx with
  | nil => exact hy
  | cons he ht ih => exact .cons he (ih hy)

theorem HeapExec.append_iff {h h'' : Heap} {xs ys : List Event} :
    HeapExec h (xs ++ ys) h'' ↔ ∃ h', HeapExec h xs h' ∧ HeapExec h' ys h'' := by
  constructor
  · intro he
    induction xs generalizing h with
    | nil => exact ⟨h, .nil h, he⟩
    | cons e es ih =>
      cases he with
      | cons head tail =>
        obtain ⟨mid, first, last⟩ := ih tail
        exact ⟨mid, .cons head first, last⟩
  · rintro ⟨mid, hx, hy⟩
    exact hx.append hy

theorem load_exec (h : Heap) (p : Ptr) :
    HeapExec h (Program.load p h).trace (Program.load p h).heap := .cons (.load h p) (.nil h)

theorem allocate_exec (h : Heap) (c : Cell) :
    HeapExec h (Program.allocate c h).trace (Program.allocate c h).heap :=
  .cons (.allocate h c) (.nil _)

theorem readBefore_exec (h : Heap) (p : Ptr) : HeapExec h (readBefore h p) h :=
  .cons (.control h) (load_exec h p)

theorem readTwoBefore_exec (h : Heap) (p q : Ptr) : HeapExec h (readTwoBefore h p q) h :=
  .cons (.control h) ((load_exec h p).append (load_exec h q))

theorem leafInsert_exec (h : Heap) (a items : Ptr) :
    HeapExec h (leafInsert a items h).trace (leafInsert a items h).heap :=
  (allocate_exec h (.cons a items)).append (allocate_exec _ (.bucket h.length))

theorem forkAfter_exec {h : Heap} {child : Run (Option Ptr)} (b : Bool) (sibling : Ptr)
    (hc : HeapExec h child.trace child.heap) :
    HeapExec h (forkAfter b sibling child).trace (forkAfter b sibling child).heap := by
  cases hv : child.value with
  | none => simpa [forkAfter, hv] using hc
  | some p =>
    simpa [forkAfter, hv] using hc.append
      (allocate_exec child.heap (.fork (if b then sibling else p) (if b then p else sibling)))

theorem leafPointer_exec (h : Heap) (items : Ptr) :
    HeapExec h (leafPointer items h).trace (leafPointer items h).heap := by
  by_cases hc : h[items]? = some .nil
  · simpa [leafPointer, Program.load, Program.pure, hc, readBefore] using readBefore_exec h items
  · simpa [leafPointer, Program.load, hc, readBefore] using
      (readBefore_exec h items).append (allocate_exec h (.bucket items))

theorem joinPointer_exec (h : Heap) (left right : Ptr) :
    HeapExec h (joinPointer left right h).trace (joinPointer left right h).heap := by
  by_cases hc : h[left]? = some .nil ∧ h[right]? = some .nil
  · simpa [joinPointer, Program.load, Program.pure, hc, readTwoBefore] using readTwoBefore_exec h left right
  · simpa [joinPointer, Program.load, hc, readTwoBefore, List.append_assoc] using
      (readTwoBefore_exec h left right).append (allocate_exec h (.fork left right))

theorem extendPop_exec (h : Heap) (b : Bool) (sibling key a tree : Ptr) :
    HeapExec h (extendPop b sibling key a tree h).trace (extendPop b sibling key a tree h).heap :=
  (joinPointer_exec h _ _).append (allocate_exec _ (.bit b key))

theorem LookupEval.exec {h : Heap} {kp tp : Ptr} {r : Run (Option Ptr)}
    (he : LookupEval h kp tp r) : HeapExec h r.trace r.heap := by
  induction he with
  | empty => exact readBefore_exec _ _
  | bucket => exact readBefore_exec _ _
  | fork root keyCell child ih => exact (readTwoBefore_exec _ _ _).append ih

theorem InsertEval.exec {h : Heap} {kp a tp : Ptr} {r : Run (Option Ptr)}
    (he : InsertEval h kp a tp r) : HeapExec h r.trace r.heap := by
  induction he with
  | emptyLeaf => exact (readTwoBefore_exec _ _ _).append (leafInsert_exec _ _ _)
  | bucketLeaf => exact (readTwoBefore_exec _ _ _).append (leafInsert_exec _ _ _)
  | emptyBranch root keyCell child ih => exact (readTwoBefore_exec _ _ _).append (forkAfter_exec _ _ ih)
  | fork root keyCell child ih => exact (readTwoBefore_exec _ _ _).append (forkAfter_exec _ _ ih)

theorem PopEval.exec {h : Heap} {tp : Ptr} {r : Run PopValue}
    (he : PopEval h tp r) : HeapExec h r.trace r.heap := by
  induction he with
  | empty => exact readBefore_exec _ _
  | emptyBucket => exact readTwoBefore_exec _ _ _
  | bucket => exact (readTwoBefore_exec _ _ _).append (leafPointer_exec _ _)
  | left root child found ih => exact (readBefore_exec _ _).append (ih.append (extendPop_exec _ _ _ _ _ _))
  | right root leftChild noLeft rightChild found ihl ihr =>
    exact (readBefore_exec _ _).append ((ihl.append ihr).append (extendPop_exec _ _ _ _ _ _))
  | noChildren root leftChild noLeft rightChild noRight ihl ihr =>
    exact (readBefore_exec _ _).append ((ihl.append ihr).append (.nil _))

end WeightedMIS.PointerMemory
