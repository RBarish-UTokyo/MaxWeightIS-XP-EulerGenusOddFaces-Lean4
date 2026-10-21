module

public import WeightedMIS.ExpandedWords
public import WeightedMIS.RegisterComparator

/-!
# Stored nonnegative residual-arc records

Each record stores two binary vertex names and one binary residual capacity.
The list order is retained by scanning and updating the materialized matrix.
-/

@[expose] public section

namespace WeightedMIS.ResidualWords

open WeightedMIS.PointerMemory WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer

structure Arc (n b : ℕ) where
  source : Bits n
  target : Bits n
  capacity : Bits b

def ArcAt {n b : ℕ} (h : Heap) (p : Ptr) (a : Arc n b) : Prop :=
  ∃ sp tail tp cp, h[p]? = some (.pair sp tail) ∧
    h[tail]? = some (.pair tp cp) ∧ BitsAt h sp a.source ∧
    BitsAt h tp a.target ∧ BitsAt h cp a.capacity

def TableAt {n b : ℕ} (h : Heap) (p : Ptr) (xs : List (Arc n b)) : Prop :=
  ListRep ArcAt h p xs

theorem ArcAt.allocated {n b : ℕ} {h : Heap} {p : Ptr} {a : Arc n b}
    (ha : ArcAt h p a) : p < h.length := by
  obtain ⟨sp, tail, tp, cp, hc, _⟩ := ha
  exact List.getElem?_eq_some_iff.mp hc |>.1

theorem ArcAt.mono {n b : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr} {a : Arc n b}
    (ha : ArcAt h p a) : ArcAt h' p a := by
  obtain ⟨sp, tail, tp, cp, hc, ht, hs, hd, hb⟩ := ha
  exact ⟨sp, tail, tp, cp, he.lookup hc, he.lookup ht, hs.mono he, hd.mono he, hb.mono he⟩

theorem TableAt.allocated {n b : ℕ} {h : Heap} {p : Ptr} {xs : List (Arc n b)}
    (hw : TableAt h p xs) : p < h.length := ListRep.allocated hw

theorem TableAt.mono {n b : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr} {xs : List (Arc n b)}
    (hw : TableAt h p xs) : TableAt h' p xs :=
  ListRep.mono he (fun _ _ h => h.mono he) hw

theorem TableAt.nil {n b : ℕ} {h : Heap} {p : Ptr} (hc : h[p]? = some .nil) :
    TableAt h p ([] : List (Arc n b)) := ⟨[], .nil hc, .nil⟩

theorem TableAt.cons {n b : ℕ} {h : Heap} {p head tail : Ptr} {w : Arc n b} {ws : List (Arc n b)}
    (hc : h[p]? = some (.cons head tail)) (hh : ArcAt h head w) (ht : TableAt h tail ws) :
    TableAt h p (w :: ws) := by
  obtain ⟨ps, hp, hw⟩ := ht
  exact ⟨head :: ps, .cons hc hp, .cons hh hw⟩

theorem TableAt.nil_iff {n b : ℕ} {h : Heap} {p : Ptr} :
    TableAt h p ([] : List (Arc n b)) ↔ h[p]? = some .nil := by
  constructor
  · rintro ⟨ps, hp, hw⟩
    cases hw
    cases hp with
    | nil hc => exact hc
  · exact TableAt.nil

theorem TableAt.cons_iff {n b : ℕ} {h : Heap} {p : Ptr} {w : Arc n b} {ws : List (Arc n b)} :
    TableAt h p (w :: ws) ↔ ∃ head tail, h[p]? = some (.cons head tail) ∧
      ArcAt h head w ∧ TableAt h tail ws := by
  constructor
  · rintro ⟨ps, hp, hw⟩
    cases hw with
    | cons head rest =>
      cases hp with
      | cons hc ht => exact ⟨_, _, hc, head, _, ht, rest⟩
  · rintro ⟨head, tail, hc, hh, ht⟩
    exact TableAt.cons hc hh ht

/-- The optional answer shares the two endpoint words already in the table. -/
def AnswerAt {n b : ℕ} (h : Heap) (sp tp : Ptr) : Option (Arc n b) → Prop
  | none => sp = 0 ∧ tp = 0
  | some a => BitsAt h sp a.source ∧ BitsAt h tp a.target

end WeightedMIS.ResidualWords
