module

public import WeightedMIS.RegisterPotentialStep
public import WeightedMIS.ExpandedWords

/-! # Shared lists of signed binary integers -/

@[expose] public section

namespace WeightedMIS.SignedWords

open WeightedMIS.PointerMemory WeightedMIS.EfficientSearch WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.RegisterPotentialStep

def SignedAt {n : ℕ} (h : Heap) (p : Ptr) (a : Word n) : Prop :=
  ∃ magnitude, h[p]? = some (.bit a.1 magnitude) ∧ BitsAt h magnitude a.2

def ListAt {n : ℕ} (h : Heap) (p : Ptr) (a : List (Word n)) : Prop :=
  ListRep SignedAt h p a

theorem SignedAt.allocated {n : ℕ} {h : Heap} {p : Ptr} {a : Word n}
    (ha : SignedAt h p a) : p < h.length := by
  obtain ⟨_, hc, _⟩ := ha
  exact List.getElem?_eq_some_iff.mp hc |>.1

theorem SignedAt.mono {n : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr} {a : Word n}
    (ha : SignedAt h p a) : SignedAt h' p a := by
  obtain ⟨mp, hc, hm⟩ := ha
  exact ⟨mp, he.lookup hc, hm.mono he⟩

theorem ListAt.allocated {n : ℕ} {h : Heap} {p : Ptr} {a : List (Word n)}
    (ha : ListAt h p a) : p < h.length := ListRep.allocated ha

theorem ListAt.mono {n : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr} {a : List (Word n)}
    (ha : ListAt h p a) : ListAt h' p a := ListRep.mono he (fun _ _ h => h.mono he) ha

theorem ListAt.nil {n : ℕ} {h : Heap} {p : Ptr} (hc : h[p]? = some .nil) :
    ListAt h p ([] : List (Word n)) := ⟨[], .nil hc, .nil⟩

theorem ListAt.cons {n : ℕ} {h : Heap} {p head tail : Ptr} {a : Word n} {as : List (Word n)}
    (hc : h[p]? = some (.cons head tail)) (hh : SignedAt h head a) (ht : ListAt h tail as) :
    ListAt h p (a :: as) := by
  obtain ⟨ps, hp, hw⟩ := ht
  exact ⟨head :: ps, .cons hc hp, .cons hh hw⟩

theorem ListAt.nil_iff {n : ℕ} {h : Heap} {p : Ptr} :
    ListAt h p ([] : List (Word n)) ↔ h[p]? = some .nil := by
  constructor
  · rintro ⟨ps, hp, hw⟩
    cases hw
    cases hp with
    | nil hc => exact hc
  · exact ListAt.nil

theorem ListAt.cons_iff {n : ℕ} {h : Heap} {p : Ptr} {a : Word n} {as : List (Word n)} :
    ListAt h p (a :: as) ↔ ∃ head tail, h[p]? = some (.cons head tail) ∧
      SignedAt h head a ∧ ListAt h tail as := by
  constructor
  · rintro ⟨ps, hp, hw⟩
    cases hw with
    | cons head rest =>
      cases hp with
      | cons hc ht => exact ⟨_, _, hc, head, _, ht, rest⟩
  · rintro ⟨head, tail, hc, hh, ht⟩
    exact ListAt.cons hc hh ht

end WeightedMIS.SignedWords
