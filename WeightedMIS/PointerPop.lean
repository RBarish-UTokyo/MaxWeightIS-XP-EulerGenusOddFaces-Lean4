module

public import WeightedMIS.PointerJoin

/-!
# Pointer implementation of minimum extraction

The implementation follows actual trie pointers, shares the untouched branch,
and allocates only the returned key spine and changed branch spine. Its
refinement relates every returned pointer to the existing radix algorithm.
-/

@[expose] public section

namespace WeightedMIS.PointerMemory

open WeightedMIS.EfficientSearch

abbrev PopValue := Option (Ptr × Ptr × Ptr)

inductive PopAt (h : Heap) {n : ℕ} : PopValue → Option (Bits n × Ptr × Radix Ptr n) → Prop
  | empty : PopAt h none none
  | item {kp a tp : Ptr} {key : Bits n} {tree : Radix Ptr n}
      (keyRep : BitsAt h kp key) (payloadAllocated : a < h.length)
      (treeRep : TrieAt h tp tree) : PopAt h (some (kp, a, tp)) (some (key, a, tree))

theorem PopAt.none_iff {h : Heap} {n : ℕ} {out : PopValue}
    {value : Option (Bits n × Ptr × Radix Ptr n)} (hr : PopAt h out value) :
    out = none ↔ value = none := by
  cases hr <;> simp

theorem PopAt.get_some {h : Heap} {n : ℕ} {out : PopValue}
    {key : Bits n} {a : Ptr} {tree : Radix Ptr n} (hr : PopAt h out (some (key, a, tree))) :
    ∃ kp tp, out = some (kp, a, tp) ∧ BitsAt h kp key ∧ a < h.length ∧ TrieAt h tp tree := by
  cases hr with
  | item hk ha ht => exact ⟨_, _, rfl, hk, ha, ht⟩

/-- Extend a successful child extraction by one key bit and a canonical join. -/
def extendPop (b : Bool) (sibling key payload tree : Ptr) : Program PopValue := fun h =>
  let joined := joinPointer (if b then sibling else tree) (if b then tree else sibling) h
  let bit := Program.allocate (.bit b key) joined.heap
  ⟨some (bit.value, payload, joined.value), bit.heap, joined.trace ++ bit.trace⟩

theorem extendPop_refines {h : Heap} (hh : Valid h) {n : ℕ} {sibling kp a tp : Ptr}
    {key : Bits n} {s t : Radix Ptr n} (b : Bool)
    (hs : TrieAt h sibling s) (hk : BitsAt h kp key) (ha : a < h.length)
    (ht : TrieAt h tp t) :
    SafeRun h (extendPop b sibling kp a tp h) ∧
      PopAt (extendPop b sibling kp a tp h).heap (extendPop b sibling kp a tp h).value
        (some (.cons b key, a, Radix.join (if b then s else t) (if b then t else s))) ∧
      (extendPop b sibling kp a tp h).trace.length ≤ 5 := by
  have hl : TrieAt h (if b then sibling else tp) (if b then s else t) := by
    cases b <;> assumption
  have hr : TrieAt h (if b then tp else sibling) (if b then t else s) := by
    cases b <;> assumption
  obtain ⟨hj, hjt, hjlen⟩ := joinPointer_refines hh hl hr
  obtain ⟨hb, hbk⟩ := allocate_bit hj.2.1 b (hk.mono hj.1)
  refine ⟨safe_change_value (safe_join hj hb) _, ?_, ?_⟩
  · exact .item hbk (lt_of_lt_of_le ha (hj.1.trans hb.1).length_le) (hjt.mono hb.1)
  · simp only [extendPop, Program.allocate, List.length_append, List.length_cons, List.length_nil]
    omega

/-- Explicit RAM execution of the recursive extraction. Invalid tags return
empty; well-represented inputs are handled by the refinement theorem. -/
def popPointer : ℕ → Ptr → Program PopValue
  | 0, tree, h =>
      let root := Program.load tree h
      match root.value with
      | some (.bucket items) =>
          let item := Program.load items h
          match item.value with
          | some (.cons a tail) =>
              let leaf := leafPointer tail h
              ⟨some (0, a, leaf.value), leaf.heap,
                .control :: (root.trace ++ item.trace ++ leaf.trace)⟩
          | _ => ⟨none, h, .control :: (root.trace ++ item.trace)⟩
      | _ => ⟨none, h, .control :: root.trace⟩
  | n + 1, tree, h =>
      let root := Program.load tree h
      match root.value with
      | some (.fork left right) =>
          let lp := popPointer n left h
          let result : Run PopValue := match lp.value with
          | some (key, a, left') =>
              let extended := extendPop false right key a left' lp.heap
              ⟨extended.value, extended.heap, lp.trace ++ extended.trace⟩
          | none =>
              let rp := popPointer n right lp.heap
              let after : Run PopValue := match rp.value with
              | some (key, a, right') => extendPop true left key a right' rp.heap
              | none => Program.pure none rp.heap
              ⟨after.value, after.heap, lp.trace ++ rp.trace ++ after.trace⟩
          ⟨result.value, result.heap, .control :: (root.trace ++ result.trace)⟩
      | _ => ⟨none, h, .control :: root.trace⟩

/-- Every load/write of extraction is represented by the execution trace. The
constant factor includes shared-list inspection, canonical joins, and new key
bits; it is proved from this pointer implementation, not from tree size. -/
theorem popPointer_refines {n : ℕ} {h : Heap} (hh : Valid h)
    {tp : Ptr} {tree : Radix Ptr n} (ht : TrieAt h tp tree) :
    SafeRun h (popPointer n tp h) ∧
      PopAt (popPointer n tp h).heap (popPointer n tp h).value (Radix.pop tree).1 ∧
      (popPointer n tp h).trace.length ≤ 8 * (Radix.pop tree).2 := by
  induction tree generalizing h tp with
  | @empty n =>
    cases ht with
    | empty hc =>
      have hb := load_control_bound hh (List.getElem?_eq_some_iff.mp hc |>.1)
      refine ⟨?_, ?_, ?_⟩
      · cases n <;> simpa [popPointer, Program.load, Program.pure, hc] using
          safe_prefix (safe_pure h hh (none : PopValue)) _ hb
      · cases n <;> simpa [popPointer, Program.load, hc, Radix.pop] using
          (PopAt.empty (h := h) (n := _))
      · cases n <;> simp [popPointer, Program.load, hc, Radix.pop]
  | bucket xs =>
    cases ht with
    | @bucket _ items _ hc hx =>
      have hb := traceBound_append
        (load_control_bound hh (List.getElem?_eq_some_iff.mp hc |>.1))
        (safe_load h hh items hx.allocated).2.2.1
      cases hx with
      | nil hitem =>
        refine ⟨?_, ?_, ?_⟩
        · simpa [popPointer, Program.load, Program.pure, hc, hitem, List.append_assoc] using
            safe_prefix (safe_pure h hh (none : PopValue)) _ hb
        · simpa [popPointer, Program.load, hc, hitem, Radix.pop] using
            (PopAt.empty (h := h) (n := 0))
        · simp [popPointer, Program.load, hc, hitem, Radix.pop]
      | @cons _ a tail rest hitem htail =>
        obtain ⟨hs, hr, hlen⟩ := leafPointer_refines hh htail
        have ha : a < h.length := hh.2 items (.cons a tail) hitem a (by simp [Cell.references])
        refine ⟨?_, ?_, ?_⟩
        · simpa [popPointer, Program.load, hc, hitem, List.append_assoc] using
            safe_prefix (safe_change_value hs
              (some (0, a, (leafPointer tail h).value) : PopValue)) _ hb
        · have hk : BitsAt (leafPointer tail h).heap 0 Bits.nil := .nil (hs.1.lookup hh.1)
          have hp := PopAt.item hk (lt_of_lt_of_le ha hs.1.length_le) hr
          simpa [popPointer, Program.load, hc, hitem, Radix.pop] using hp
        · simp only [popPointer, Program.load, hc, hitem, Radix.pop,
            List.length_cons, List.length_append, List.length_nil]
          omega
  | @fork n l r ihl ihr =>
    cases ht with
    | @fork _ left right _ _ _ hc hl hr =>
      have hb := load_control_bound hh (List.getElem?_eq_some_iff.mp hc |>.1)
      obtain ⟨hls, hlrep, hlcost⟩ := ihl hh hl
      cases hpl : (Radix.pop l).1 with
      | none =>
        have hvl : (popPointer n left h).value = none := hlrep.none_iff.mpr hpl
        obtain ⟨hrs, hrrep, hrcost⟩ := ihr hls.2.1 (hr.mono hls.1)
        cases hpr : (Radix.pop r).1 with
        | none =>
          have hvr : (popPointer n right (popPointer n left h).heap).value = none :=
            hrrep.none_iff.mpr hpr
          refine ⟨?_, ?_, ?_⟩
          · simpa [popPointer, Program.load, Program.pure, hc, hvl, hvr, List.append_assoc] using
              safe_prefix (safe_join hls hrs) _ hb
          · simpa [popPointer, Program.load, Program.pure, hc, hvl, hvr, Radix.pop, hpl, hpr] using
              (PopAt.empty (h := (popPointer n right (popPointer n left h).heap).heap) (n := n + 1))
          · simp only [popPointer, Program.load, Program.pure, hc, hvl, hvr, Radix.pop, hpl, hpr,
              List.length_cons, List.length_append, List.length_nil]
            omega
        | some value =>
          obtain ⟨key, a, r'⟩ := value
          have hreps : PopAt (popPointer n right (popPointer n left h).heap).heap
              (popPointer n right (popPointer n left h).heap).value (some (key, a, r')) := by
            simpa only [hpr] using hrrep
          obtain ⟨kp, rp, hvr, hk, ha, ht'⟩ := hreps.get_some
          obtain ⟨hes, herep, hecost⟩ := extendPop_refines hrs.2.1 true
            (hl.mono (hls.1.trans hrs.1)) hk ha ht'
          refine ⟨?_, ?_, ?_⟩
          · simpa [popPointer, Program.load, hc, hvl, hvr, List.append_assoc] using
              safe_prefix (safe_join (safe_join hls hrs) hes) _ hb
          · simpa [popPointer, Program.load, hc, hvl, hvr, Radix.pop, hpl, hpr] using herep
          · simp only [popPointer, Program.load, hc, hvl, hvr, Radix.pop, hpl, hpr,
              List.length_cons, List.length_append, List.length_nil]
            omega
      | some value =>
        obtain ⟨key, a, l'⟩ := value
        have hlreps : PopAt (popPointer n left h).heap (popPointer n left h).value
            (some (key, a, l')) := by simpa only [hpl] using hlrep
        obtain ⟨kp, lp, hvl, hk, ha, ht'⟩ := hlreps.get_some
        obtain ⟨hes, herep, hecost⟩ := extendPop_refines hls.2.1 false
          (hr.mono hls.1) hk ha ht'
        refine ⟨?_, ?_, ?_⟩
        · simpa [popPointer, Program.load, hc, hvl, List.append_assoc] using
            safe_prefix (safe_join hls hes) _ hb
        · simpa [popPointer, Program.load, hc, hvl, Radix.pop, hpl] using herep
        · simp only [popPointer, Program.load, hc, hvl, Radix.pop, hpl,
            List.length_cons, List.length_append, List.length_nil]
          omega

end WeightedMIS.PointerMemory
