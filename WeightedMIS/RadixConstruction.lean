module

public import WeightedMIS.EfficientSearchQueue

/-! # Constructing a sparse radix table from its explicit entries -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Radix

variable {α : Type*} {n : ℕ}

def insertEntries : List (Bits n × α) → Radix α n → Radix α n
  | [], tree => tree
  | entry :: rest, tree => (insert entry.1 entry.2 (insertEntries rest tree)).1

def fromEntries (entries : List (Bits n × α)) : Radix α n :=
  insertEntries entries .empty

@[simp] theorem mem_insertEntries (entries : List (Bits n × α)) (tree : Radix α n)
    (entry : Bits n × α) :
    entry ∈ (insertEntries entries tree).elements ↔ entry ∈ entries ∨ entry ∈ tree.elements := by
  induction entries with
  | nil => simp [insertEntries]
  | cons a rest ih => simp only [insertEntries, mem_insert, ih, List.mem_cons, or_assoc]

@[simp] theorem mem_fromEntries (entries : List (Bits n × α)) (entry : Bits n × α) :
    entry ∈ (fromEntries entries).elements ↔ entry ∈ entries := by
  simp [fromEntries, elements]

theorem insertEntries_size (entries : List (Bits n × α)) (tree : Radix α n) :
    (insertEntries entries tree).elements.length = entries.length + tree.elements.length := by
  induction entries with
  | nil => simp [insertEntries]
  | cons a rest ih => simp [insertEntries, insert_size, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem fromEntries_size (entries : List (Bits n × α)) :
    (fromEntries entries).elements.length = entries.length := by
  simp [fromEntries, insertEntries_size, elements]

theorem insertEntries_canonical (entries : List (Bits n × α)) (tree : Radix α n)
    (ht : tree.canonical) : (insertEntries entries tree).canonical := by
  induction entries with
  | nil => exact ht
  | cons a rest ih => exact insert_canonical _ _ _ ih

theorem fromEntries_canonical (entries : List (Bits n × α)) :
    (fromEntries entries).canonical :=
  insertEntries_canonical entries .empty trivial

end WeightedMIS.EfficientSearch.Radix
