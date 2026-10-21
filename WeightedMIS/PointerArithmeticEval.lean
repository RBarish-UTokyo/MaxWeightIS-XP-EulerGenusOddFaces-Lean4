module

public import WeightedMIS.PointerArithmetic
public import WeightedMIS.PointerStack

/-!
# Data-directed addition and its explicit continuation frames

The evaluation rules branch on the two loaded cell tags, without a word width
or natural-number fuel. A recursive call saves precisely the two head bits;
the concrete bit-stack simulation accounts for copying and restoring them.
-/

@[expose] public section

namespace WeightedMIS.PointerMemory

open WeightedMIS.EfficientSearch

def adderAfter (a b : Bool) (tail : Run (Ptr × Bool)) : Run (Ptr × Bool) :=
  let head := Bits.fullAdd a b tail.value.2
  let out := Program.allocate (.bit head.1 tail.value.1) tail.heap
  ⟨(out.value, head.2), out.heap,
    tail.trace ++ List.replicate 7 .control ++ out.trace⟩

/-- The fixed ripple-carry procedure, specified solely by observed tags. -/
inductive AddEval : Heap → Ptr → Ptr → Bool → Run (Ptr × Bool) → Prop
  | nil {h : Heap} {ap bp : Ptr} (carry : Bool)
      (left : h[ap]? = some .nil) (right : h[bp]? = some .nil) :
      AddEval h ap bp carry ⟨(0, carry), h, readTwoBefore h ap bp⟩
  | bit {h : Heap} {ap bp atail btail : Ptr} {a b carry : Bool} {r : Run (Ptr × Bool)}
      (left : h[ap]? = some (.bit a atail)) (right : h[bp]? = some (.bit b btail))
      (child : AddEval h atail btail carry r) :
      AddEval h ap bp carry (withEvents (readTwoBefore h ap bp) (adderAfter a b r))

/-- The bounded evaluator realizes the same fixed procedure on represented words. -/
theorem addCarryPointer_eval {n : ℕ} {h : Heap} (hh : Valid h)
    {ap bp : Ptr} {a b : Bits n} (ha : BitsAt h ap a) (hb : BitsAt h bp b)
    (carry : Bool) : AddEval h ap bp carry (addCarryPointer n ap bp carry h) := by
  induction a generalizing ap bp with
  | nil =>
    cases b
    cases ha with
    | nil hac =>
      cases hb with
      | nil hbc => exact .nil carry hac hbc
  | cons av as ih =>
    cases b with
    | cons bv bs =>
      cases ha with
      | cons hac hat =>
        cases hb with
        | cons hbc hbt =>
          have ht := ih hat hbt
          simpa [addCarryPointer, Program.load, hac, hbc, withEvents, adderAfter,
            readTwoBefore, List.append_assoc] using AddEval.bit hac hbc ht

theorem controls_exec (h : Heap) (n : ℕ) : HeapExec h (List.replicate n .control) h := by
  induction n with
  | zero => exact .nil h
  | succ n ih => simpa only [List.replicate_succ] using HeapExec.cons (.control h) ih

theorem adderAfter_exec {h : Heap} {tail : Run (Ptr × Bool)}
    (he : HeapExec h tail.trace tail.heap) (a b : Bool) :
    HeapExec h (adderAfter a b tail).trace (adderAfter a b tail).heap := by
  exact (he.append (controls_exec tail.heap 7)).append
    (allocate_exec tail.heap (.bit (Bits.fullAdd a b tail.value.2).1 tail.value.1))

theorem AddEval.exec {h : Heap} {ap bp : Ptr} {carry : Bool} {r : Run (Ptr × Bool)}
    (he : AddEval h ap bp carry r) : HeapExec h r.trace r.heap := by
  induction he with
  | nil => exact readTwoBefore_exec _ _ _
  | bit left right child ih => exact (readTwoBefore_exec _ _ _).append (adderAfter_exec ih _ _)

/-- Every recursive call saves the two actual Boolean head bits. -/
theorem AddEval.callTree {h : Heap} {ap bp : Ptr} {carry : Bool} {r : Run (Ptr × Bool)}
    (he : AddEval h ap bp carry r) (bound : ℕ) :
    ∃ tree : CallTree, tree.memoryTrace = r.trace ∧ tree.Bounded bound 2 ∧
      tree.calls ≤ r.trace.length := by
  induction he with
  | nil =>
    refine ⟨.code (readTwoBefore _ _ _), rfl, trivial, ?_⟩
    simp [CallTree.calls]
  | @bit ap bp atail btail a b carry r left right child ih =>
    obtain ⟨tree, ht, hb, hc⟩ := ih
    let after : List Event := List.replicate 7 .control ++
      (Program.allocate (.bit (Bits.fullAdd a b r.value.2).1 r.value.1) r.heap).trace
    refine ⟨.seq (.code (readTwoBefore h ap bp))
      (.seq (.call [.flag a, .flag b] tree) (.code after)), ?_, ?_, ?_⟩
    · simp [CallTree.memoryTrace, ht, withEvents, adderAfter, after, List.append_assoc]
    · refine ⟨trivial, ⟨?_, trivial⟩⟩
      exact ⟨by simp, by simp [Word.Bounded], hb⟩
    · simp only [CallTree.calls, withEvents, adderAfter, readTwoBefore, Program.load,
        Program.allocate, List.length_append, List.length_cons, List.length_nil,
        List.length_replicate]
      omega

/-- Actual heap execution plus explicit stack-symbol execution has the stated
linear-times-address-width cost. -/
theorem addCarryPointer_stack_cost {n : ℕ} {h : Heap} (hh : Valid h)
    {ap bp : Ptr} {a b : Bits n} (ha : BitsAt h ap a) (hb : BitsAt h bp b) (carry : Bool) :
    ∃ tree : CallTree,
      tree.memoryTrace = (addCarryPointer n ap bp carry h).trace ∧
      (∀ stack, StackExec h stack tree.compile (addCarryPointer n ap bp carry h).heap stack) ∧
      stackBitCost tree.compile ≤ (11 * n + 3) *
        (6 + 3 * (h.length + (11 * n + 3)).size +
          4 * ((h.length + (11 * n + 3)).size + 3)) := by
  have he := addCarryPointer_eval hh ha hb carry
  have hr := addCarryPointer_refines hh ha hb carry
  let bound := h.length + (11 * n + 3)
  obtain ⟨tree, ht, hbnd, hc⟩ := he.callTree bound
  have hlen := hr.2.2.2
  have hbound : (addCarryPointer n ap bp carry h).heap.length ≤ bound := by
    simpa only [bound, hlen] using hr.1.2.2.2
  have htrace : TraceBound tree.memoryTrace bound := by
    rw [ht]
    exact traceBound_mono hr.1.2.2.1 hbound
  refine ⟨tree, ht, ?_, ?_⟩
  · intro stack
    exact tree.exec (ht ▸ he.exec) stack
  · have hhcost := tree.bitCost_le bound 2 htrace hbnd (ht ▸ hc)
    simpa only [ht, hlen, bound, Nat.reduceMul] using hhcost

end WeightedMIS.PointerMemory
