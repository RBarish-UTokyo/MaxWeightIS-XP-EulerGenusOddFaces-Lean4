module

public import WeightedMIS.EfficientSearchQueue

/-!
# Payload refinement for radix operations

The relation preserves the complete trie shape and every priority key while
allowing a stored payload pointer to represent a structured semantic value.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Radix

variable {α β : Type*} (R : α → β → Prop)

inductive Related : {n : ℕ} → Radix α n → Radix β n → Prop
  | empty {n} : Related (.empty (n := n)) .empty
  | bucket {xs ys} (items : List.Forall₂ R xs ys) : Related (.bucket xs) (.bucket ys)
  | fork {n} {l r : Radix α n} {l' r' : Radix β n}
      (left : Related l l') (right : Related r r') : Related (.fork l r) (.fork l' r')

theorem Related.imp {S : α → β → Prop} {n : ℕ} {a : Radix α n} {b : Radix β n}
    (h : Related R a b) (hRS : ∀ x y, R x y → S x y) : Related S a b := by
  induction h with
  | empty => exact .empty
  | bucket hitems =>
    apply Related.bucket
    induction hitems with
    | nil => exact .nil
    | cons hx hs ih => exact .cons (hRS _ _ hx) ih
  | fork hl hr ihl ihr => exact .fork ihl ihr

theorem Related.emptyRoot {n : ℕ} {a : Radix α n} {b : Radix β n} (h : Related R a b) :
    a.emptyRoot = b.emptyRoot := by
  cases h <;> rfl

theorem Related.leaf {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) :
    Related R (Radix.leaf xs) (Radix.leaf ys) := by
  cases h with
  | nil => exact .empty
  | cons hx hxs => exact .bucket (.cons hx hxs)

theorem Related.join {n : ℕ} {l r : Radix α n} {l' r' : Radix β n}
    (hl : Related R l l') (hr : Related R r r') : Related R (Radix.join l r) (Radix.join l' r') := by
  unfold Radix.join
  rw [hl.emptyRoot, hr.emptyRoot]
  split
  · exact .empty
  · exact .fork hl hr

theorem Related.canonical {n : ℕ} {a : Radix α n} {b : Radix β n}
    (h : Related R a b) : a.canonical ↔ b.canonical := by
  induction h with
  | empty => rfl
  | @bucket xs ys hitems =>
    have hlen := hitems.length_eq
    simp only [Radix.canonical, ← List.length_pos_iff_ne_nil]
    omega
  | fork hl hr ihl ihr =>
    simp only [Radix.canonical, ihl, ihr, hl.emptyRoot, hr.emptyRoot]

theorem Related.insert {n : ℕ} {a : Radix α n} {b : Radix β n}
    (h : Related R a b) (key : Bits n) {x : α} {y : β} (hxy : R x y) :
    Related R (Radix.insert key x a).1 (Radix.insert key y b).1 := by
  induction key with
  | nil =>
    cases h with
    | empty => exact .bucket (.cons hxy .nil)
    | bucket hs => exact .bucket (.cons hxy hs)
  | cons bit key ih =>
    cases h with
    | empty =>
      have hi := ih (Related.empty (R := R))
      cases bit
      · exact .fork hi .empty
      · exact .fork .empty hi
    | fork hl hr =>
      cases bit
      · exact .fork (ih hl) hr
      · exact .fork hl (ih hr)

theorem Related.lookup {n : ℕ} {a : Radix α n} {b : Radix β n}
    (h : Related R a b) (key : Bits n) :
    List.Forall₂ R (Radix.lookup key a).1 (Radix.lookup key b).1 ∧
      (Radix.lookup key a).2 = (Radix.lookup key b).2 := by
  induction key with
  | nil =>
    cases h with
    | empty => exact ⟨.nil, rfl⟩
    | bucket hs => exact ⟨hs, rfl⟩
  | cons bit key ih =>
    cases h with
    | empty => exact ⟨.nil, rfl⟩
    | fork hl hr =>
      cases bit
      · have hi := ih hl
        exact ⟨hi.1, congrArg (· + 1) hi.2⟩
      · have hi := ih hr
        exact ⟨hi.1, congrArg (· + 1) hi.2⟩

def PopRelated {n : ℕ} : Option (Bits n × α × Radix α n) →
    Option (Bits n × β × Radix β n) → Prop
  | none, none => True
  | some (ka, xa, a), some (kb, xb, b) => ka = kb ∧ R xa xb ∧ Related R a b
  | _, _ => False

theorem Related.pop {n : ℕ} {a : Radix α n} {b : Radix β n}
    (h : Related R a b) : PopRelated R (Radix.pop a).1 (Radix.pop b).1 ∧ (Radix.pop a).2 = (Radix.pop b).2 := by
  induction h with
  | empty => exact ⟨trivial, rfl⟩
  | bucket hitems =>
    cases hitems with
    | nil => exact ⟨trivial, rfl⟩
    | cons hhead htail => exact ⟨⟨rfl, hhead, Related.leaf R htail⟩, rfl⟩
  | @fork n l r l' r' hl hr ihl ihr =>
    rcases ihl with ⟨hil, hcl⟩
    rcases ihr with ⟨hir, hcr⟩
    cases hpl : (Radix.pop l).1 with
    | none =>
      cases hpl' : (Radix.pop l').1 with
      | some result => simp [hpl, hpl', PopRelated] at hil
      | none =>
        cases hpr : (Radix.pop r).1 with
        | none =>
          cases hpr' : (Radix.pop r').1 with
          | some result => simp [hpr, hpr', PopRelated] at hir
          | none => simp [Radix.pop, hpl, hpl', hpr, hpr', PopRelated, hcl, hcr]
        | some result =>
          obtain ⟨key, value, tail⟩ := result
          cases hpr' : (Radix.pop r').1 with
          | none => simp [hpr, hpr', PopRelated] at hir
          | some result' =>
            obtain ⟨key', value', tail'⟩ := result'
            simp only [hpr, hpr', PopRelated] at hir
            obtain ⟨rfl, hv, ht⟩ := hir
            simp only [Radix.pop, hpl, hpl', hpr, hpr', PopRelated]
            exact ⟨⟨trivial, hv, Related.join R hl ht⟩, by omega⟩
    | some result =>
      obtain ⟨key, value, tail⟩ := result
      cases hpl' : (Radix.pop l').1 with
      | none => simp [hpl, hpl', PopRelated] at hil
      | some result' =>
        obtain ⟨key', value', tail'⟩ := result'
        simp only [hpl, hpl', PopRelated] at hil
        obtain ⟨rfl, hv, ht⟩ := hil
        simp only [Radix.pop, hpl, hpl', PopRelated]
        exact ⟨⟨trivial, hv, Related.join R ht hr⟩, by omega⟩

theorem Related.elements {n : ℕ} {a : Radix α n} {b : Radix β n}
    (h : Related R a b) :
    List.Forall₂ (fun x y => x.1 = y.1 ∧ R x.2 y.2) a.elements b.elements := by
  induction h with
  | empty => exact .nil
  | bucket hitems =>
    induction hitems with
    | nil => exact .nil
    | cons hx hs ih => exact .cons ⟨rfl, hx⟩ ih
  | fork hl hr ihl ihr =>
    apply List.rel_append
    · apply List.rel_map ?_ ihl
      intro x y hxy
      exact ⟨congrArg (Bits.cons false) hxy.1, hxy.2⟩
    · apply List.rel_map ?_ ihr
      intro x y hxy
      exact ⟨congrArg (Bits.cons true) hxy.1, hxy.2⟩

end WeightedMIS.EfficientSearch.Radix
