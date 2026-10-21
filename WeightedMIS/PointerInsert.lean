module

public import WeightedMIS.PointerLookup

/-! # Persistent pointer-trie insertion -/

@[expose] public section

namespace WeightedMIS.PointerMemory

open WeightedMIS.EfficientSearch

/-- Allocate one item-list cons and one leaf. The old item list is shared. -/
def leafInsert (a items : Ptr) : Program (Option Ptr) := fun h =>
  let item := Program.allocate (.cons a items) h
  let leaf := Program.allocate (.bucket item.value) item.heap
  ⟨some leaf.value, leaf.heap, item.trace ++ leaf.trace⟩

theorem leafInsert_refines {h : Heap} (hh : Valid h) {a items : Ptr} {xs : List Ptr}
    (ha : a < h.length) (hx : ListAt h items xs) :
    SafeRun h (leafInsert a items h) ∧
      ∃ out, (leafInsert a items h).value = some out ∧
        TrieAt (leafInsert a items h).heap out (.bucket (a :: xs)) ∧
        (leafInsert a items h).trace.length = 2 := by
  obtain ⟨hs, hl⟩ := allocate_cons hh ha hx
  obtain ⟨ht, hb⟩ := allocate_bucket hs.2.1 hl
  refine ⟨safe_change_value (safe_join hs ht) _, ?_⟩
  refine ⟨_, rfl, hb, ?_⟩
  simp [leafInsert, Program.allocate]

/-- Allocate one branch after a recursive insertion, sharing the sibling. -/
def forkAfter (b : Bool) (sibling : Ptr) (child : Run (Option Ptr)) : Run (Option Ptr) :=
  match child.value with
  | none => child
  | some p =>
      let branch := Program.allocate
        (.fork (if b then sibling else p) (if b then p else sibling)) child.heap
      ⟨some branch.value, branch.heap, child.trace ++ branch.trace⟩

theorem forkAfter_refines {h : Heap} {n : ℕ} {sibling out : Ptr}
    {s t : Radix Ptr n} {child : Run (Option Ptr)} (b : Bool)
    (hs : TrieAt h sibling s) (hc : SafeRun h child)
    (hv : child.value = some out) (ht : TrieAt child.heap out t) :
    SafeRun h (forkAfter b sibling child) ∧
      ∃ p, (forkAfter b sibling child).value = some p ∧
        TrieAt (forkAfter b sibling child).heap p
          (.fork (if b then s else t) (if b then t else s)) ∧
        (forkAfter b sibling child).trace.length = child.trace.length + 1 := by
  have hs' := hs.mono hc.1
  have hl : TrieAt child.heap (if b then sibling else out) (if b then s else t) := by
    cases b <;> assumption
  have hr : TrieAt child.heap (if b then out else sibling) (if b then t else s) := by
    cases b <;> assumption
  obtain ⟨ha, haTree⟩ := allocate_fork hc.2.1 hl hr
  refine ⟨?_, ?_⟩
  · simpa only [forkAfter, hv] using safe_change_value (safe_join hc ha)
      (some (Program.allocate (.fork (if b then sibling else out)
        (if b then out else sibling)) child.heap).value)
  · refine ⟨child.heap.length, ?_, ?_, ?_⟩
    · simp only [forkAfter, hv, Program.allocate]
    · simpa only [forkAfter, hv, Program.allocate] using haTree
    · simp [forkAfter, hv, Program.allocate]

/-- Insertion follows the stored key. Each level executes one control event,
one trie load, at most one key load, and one new branch; a leaf uses two writes. -/
def insertPointer : ℕ → Ptr → Ptr → Ptr → Program (Option Ptr)
  | 0, key, a, tree, h =>
      let loaded := Program.load tree h
      let keyCell := Program.load key h
      let made := match loaded.value, keyCell.value with
        | some .nil, some .nil => leafInsert a 0 h
        | some (.bucket items), some .nil => leafInsert a items h
        | _, _ => ⟨none, h, []⟩
      ⟨made.value, made.heap, .control :: (loaded.trace ++ keyCell.trace ++ made.trace)⟩
  | n + 1, key, a, tree, h =>
      let loaded := Program.load tree h
      let keyCell := Program.load key h
      let made := match loaded.value, keyCell.value with
        | some .nil, some (.bit b tail) =>
            forkAfter b 0 (insertPointer n tail a 0 h)
        | some (.fork left right), some (.bit b tail) =>
            forkAfter b (if b then left else right)
              (insertPointer n tail a (if b then right else left) h)
        | _, _ => ⟨none, h, []⟩
      ⟨made.value, made.heap, .control :: (loaded.trace ++ keyCell.trace ++ made.trace)⟩

/-- Pointer insertion has exactly the same persistent trie value as radix
insertion, and at most four RAM/control events per structural recursive step. -/
theorem insertPointer_refines {n : ℕ} {h : Heap} (hh : Valid h)
    {kp a tp : Ptr} {key : Bits n} {tree : Radix Ptr n}
    (ha : a < h.length) (hk : BitsAt h kp key) (ht : TrieAt h tp tree) :
    SafeRun h (insertPointer n kp a tp h) ∧
      ∃ out, (insertPointer n kp a tp h).value = some out ∧
        TrieAt (insertPointer n kp a tp h).heap out (Radix.insert key a tree).1 ∧
        (insertPointer n kp a tp h).trace.length = 4 * (Radix.insert key a tree).2 + 1 := by
  induction key generalizing h kp tp with
  | nil =>
    cases hk with
    | nil hkey =>
      cases ht with
      | empty hc =>
        obtain ⟨hs, out, hv, hout, hlen⟩ := leafInsert_refines hh ha (.nil hh.1)
        have hb := traceBound_append
            (load_control_bound hh (List.getElem?_eq_some_iff.mp hc |>.1))
            (safe_load h hh kp (List.getElem?_eq_some_iff.mp hkey |>.1)).2.2.1
        refine ⟨?_, out, ?_, ?_, ?_⟩
        · simpa [insertPointer, Program.load, hc, hkey, List.append_assoc] using safe_prefix hs _ hb
        · simpa [insertPointer, Program.load, hc, hkey, List.append_assoc] using hv
        · simpa [insertPointer, Program.load, hc, hkey, Radix.insert] using hout
        · simp only [insertPointer, Program.load, hc, hkey, Radix.insert, List.length_cons,
            List.length_append, List.length_nil]
          omega
      | bucket hc hl =>
        obtain ⟨hs, out, hv, hout, hlen⟩ := leafInsert_refines hh ha hl
        have hb := traceBound_append
            (load_control_bound hh (List.getElem?_eq_some_iff.mp hc |>.1))
            (safe_load h hh kp (List.getElem?_eq_some_iff.mp hkey |>.1)).2.2.1
        refine ⟨?_, out, ?_, ?_, ?_⟩
        · simpa [insertPointer, Program.load, hc, hkey, List.append_assoc] using safe_prefix hs _ hb
        · simpa [insertPointer, Program.load, hc, hkey, List.append_assoc] using hv
        · simpa [insertPointer, Program.load, hc, hkey, Radix.insert] using hout
        · simp only [insertPointer, Program.load, hc, hkey, Radix.insert, List.length_cons,
            List.length_append, List.length_nil]
          omega
  | @cons n b key ih =>
    cases hk with
    | @cons _ kt _ _ _ hkey htail =>
      cases ht with
      | empty hc =>
        have hzero : TrieAt h 0 (Radix.empty : Radix Ptr n) := .empty hh.1
        obtain ⟨hs, out, hv, hout, hlen⟩ := ih hh ha htail hzero
        obtain ⟨hf, p, hp, htree, hflen⟩ := forkAfter_refines b hzero hs hv hout
        have hb := traceBound_append
          (load_control_bound hh (List.getElem?_eq_some_iff.mp hc |>.1))
          (safe_load h hh kp (List.getElem?_eq_some_iff.mp hkey |>.1)).2.2.1
        refine ⟨?_, p, ?_, ?_, ?_⟩
        · simpa [insertPointer, Program.load, hc, hkey, List.append_assoc] using safe_prefix hf _ hb
        · simpa [insertPointer, Program.load, hc, hkey] using hp
        · cases b <;> simpa [insertPointer, Program.load, hc, hkey, Radix.insert] using htree
        · simp only [insertPointer, Program.load, hc, hkey, List.length_cons,
            List.length_append, List.length_nil]
          rw [Radix.insert_steps] at hlen ⊢
          omega
      | @fork _ left right _ l r hc hl hr =>
        have selected : TrieAt h (if b then right else left) (if b then r else l) := by
          cases b <;> assumption
        have sibling : TrieAt h (if b then left else right) (if b then l else r) := by
          cases b <;> assumption
        obtain ⟨hs, out, hv, hout, hlen⟩ := ih hh ha htail selected
        obtain ⟨hf, p, hp, htree, hflen⟩ := forkAfter_refines b sibling hs hv hout
        have hb := traceBound_append
          (load_control_bound hh (List.getElem?_eq_some_iff.mp hc |>.1))
          (safe_load h hh kp (List.getElem?_eq_some_iff.mp hkey |>.1)).2.2.1
        refine ⟨?_, p, ?_, ?_, ?_⟩
        · simpa [insertPointer, Program.load, hc, hkey, List.append_assoc] using safe_prefix hf _ hb
        · simpa [insertPointer, Program.load, hc, hkey] using hp
        · cases b <;> simpa [insertPointer, Program.load, hc, hkey, Radix.insert] using htree
        · simp only [insertPointer, Program.load, hc, hkey, List.length_cons,
            List.length_append, List.length_nil]
          rw [Radix.insert_steps] at hlen ⊢
          omega

end WeightedMIS.PointerMemory
