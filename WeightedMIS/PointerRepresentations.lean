module

public import WeightedMIS.PointerMemory
public import WeightedMIS.EfficientSearchQueue

/-!
# Shared representations of keys, lists, and radix tries

Payloads are addresses of separately represented immutable values. A list cell
contains its payload address and tail address, so extending a reverse path uses
one allocation and does not copy the old path. The relations record actual RAM
loads and permit shared substructures.
-/

@[expose] public section

namespace WeightedMIS.PointerMemory

open WeightedMIS.EfficientSearch

inductive ListAt (heap : Heap) : Ptr → List Ptr → Prop
  | nil {p : Ptr} (cell : heap[p]? = some .nil) : ListAt heap p []
  | cons {p a tail : Ptr} {xs : List Ptr}
      (cell : heap[p]? = some (.cons a tail)) (rest : ListAt heap tail xs) :
      ListAt heap p (a :: xs)

inductive BitsAt (heap : Heap) : {n : ℕ} → Ptr → Bits n → Prop
  | nil {p : Ptr} (cell : heap[p]? = some .nil) : BitsAt heap p .nil
  | cons {p tail : Ptr} {n : ℕ} {b : Bool} {bits : Bits n}
      (cell : heap[p]? = some (.bit b tail)) (rest : BitsAt heap tail bits) :
      BitsAt heap p (.cons b bits)

inductive TrieAt (heap : Heap) : {n : ℕ} → Ptr → Radix Ptr n → Prop
  | empty {p n} (cell : heap[p]? = some .nil) : TrieAt heap p (.empty (n := n))
  | bucket {p list : Ptr} {xs : List Ptr}
      (cell : heap[p]? = some (.bucket list)) (items : ListAt heap list xs) :
      TrieAt heap p (.bucket xs)
  | fork {p left right : Ptr} {n : ℕ} {l r : Radix Ptr n}
      (cell : heap[p]? = some (.fork left right))
      (leftTree : TrieAt heap left l) (rightTree : TrieAt heap right r) :
      TrieAt heap p (.fork l r)

theorem ListAt.mono {a b : Heap} (hab : Extends a b) {p xs}
    (h : ListAt a p xs) : ListAt b p xs := by
  induction h with
  | nil hc => exact .nil (hab.lookup hc)
  | cons hc ht ih => exact .cons (hab.lookup hc) ih

theorem BitsAt.mono {a b : Heap} (hab : Extends a b) {n p} {bits : Bits n}
    (h : BitsAt a p bits) : BitsAt b p bits := by
  induction h with
  | nil hc => exact .nil (hab.lookup hc)
  | cons hc ht ih => exact .cons (hab.lookup hc) ih

theorem TrieAt.mono {a b : Heap} (hab : Extends a b) {n p} {tree : Radix Ptr n}
    (h : TrieAt a p tree) : TrieAt b p tree := by
  induction h with
  | empty hc => exact .empty (hab.lookup hc)
  | bucket hc hl => exact .bucket (hab.lookup hc) (hl.mono hab)
  | fork hc hl hr ihl ihr => exact .fork (hab.lookup hc) ihl ihr

theorem ListAt.allocated {h : Heap} {p xs} (hp : ListAt h p xs) : p < h.length := by
  cases hp with
  | nil hc => exact List.getElem?_eq_some_iff.mp hc |>.1
  | cons hc _ => exact List.getElem?_eq_some_iff.mp hc |>.1

theorem BitsAt.allocated {h : Heap} {n p} {bits : Bits n} (hp : BitsAt h p bits) : p < h.length := by
  cases hp with
  | nil hc => exact List.getElem?_eq_some_iff.mp hc |>.1
  | cons hc _ => exact List.getElem?_eq_some_iff.mp hc |>.1

theorem TrieAt.allocated {h : Heap} {n p} {tree : Radix Ptr n} (hp : TrieAt h p tree) : p < h.length := by
  cases hp with
  | empty hc => exact List.getElem?_eq_some_iff.mp hc |>.1
  | bucket hc _ => exact List.getElem?_eq_some_iff.mp hc |>.1
  | fork hc _ _ => exact List.getElem?_eq_some_iff.mp hc |>.1

/-- One executed allocation extends a shared list, retaining the old tail. -/
theorem allocate_cons {h : Heap} (hh : Valid h) {a tail : Ptr} {xs : List Ptr}
    (ha : a < h.length) (ht : ListAt h tail xs) :
    SafeRun h (Program.allocate (.cons a tail) h) ∧
      ListAt (Program.allocate (.cons a tail) h).heap
        (Program.allocate (.cons a tail) h).value (a :: xs) := by
  have hs := safe_allocate h hh (.cons a tail) (by
    intro p hp
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ha
    · exact ht.allocated)
  refine ⟨hs, .cons ?_ (ht.mono hs.1)⟩
  simp [Program.allocate]

/-- Appending a key bit also preserves and shares its tail. -/
theorem allocate_bit {h : Heap} (hh : Valid h) {n : ℕ} {tail : Ptr} {bits : Bits n}
    (b : Bool) (ht : BitsAt h tail bits) :
    SafeRun h (Program.allocate (.bit b tail) h) ∧
      BitsAt (Program.allocate (.bit b tail) h).heap
        (Program.allocate (.bit b tail) h).value (.cons b bits) := by
  have hs := safe_allocate h hh (.bit b tail) (by
    intro p hp
    simp only [Cell.references, List.mem_singleton] at hp
    exact hp ▸ ht.allocated)
  refine ⟨hs, .cons ?_ (ht.mono hs.1)⟩
  simp [Program.allocate]

/-- Construct one shared trie branch. -/
theorem allocate_fork {h : Heap} (hh : Valid h) {n : ℕ} {left right : Ptr}
    {l r : Radix Ptr n} (hl : TrieAt h left l) (hr : TrieAt h right r) :
    SafeRun h (Program.allocate (.fork left right) h) ∧
      TrieAt (Program.allocate (.fork left right) h).heap
        (Program.allocate (.fork left right) h).value (.fork l r) := by
  have hs := safe_allocate h hh (.fork left right) (by
    intro p hp
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hl.allocated
    · exact hr.allocated)
  refine ⟨hs, .fork ?_ (hl.mono hs.1) (hr.mono hs.1)⟩
  simp [Program.allocate]

/-- Construct a leaf by one allocation; its item list is shared. -/
theorem allocate_bucket {h : Heap} (hh : Valid h) {list : Ptr} {xs : List Ptr}
    (hl : ListAt h list xs) :
    SafeRun h (Program.allocate (.bucket list) h) ∧
      TrieAt (Program.allocate (.bucket list) h).heap
        (Program.allocate (.bucket list) h).value (.bucket xs) := by
  have hs := safe_allocate h hh (.bucket list) (by
    intro p hp
    simp only [Cell.references, List.mem_singleton] at hp
    exact hp ▸ hl.allocated)
  refine ⟨hs, .bucket ?_ (hl.mono hs.1)⟩
  simp [Program.allocate]

end WeightedMIS.PointerMemory
