module

public import WeightedMIS.EfficientSearchPointerTrie

/-! # Shared fixed-width word lists for expanded-graph construction -/

@[expose] public section

namespace WeightedMIS.ExpandedWords

open WeightedMIS.PointerMemory WeightedMIS.EfficientSearch WeightedMIS.EfficientSearch.Pointer

def WordsAt {n : ℕ} (h : Heap) (p : Ptr) (ws : List (Bits n)) : Prop :=
  ListRep (fun h p w => BitsAt h p w) h p ws

theorem WordsAt.allocated {n : ℕ} {h : Heap} {p : Ptr} {ws : List (Bits n)}
    (hw : WordsAt h p ws) : p < h.length := ListRep.allocated hw

theorem WordsAt.mono {n : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr} {ws : List (Bits n)}
    (hw : WordsAt h p ws) : WordsAt h' p ws :=
  ListRep.mono he (fun _ _ h => h.mono he) hw

theorem WordsAt.nil {n : ℕ} {h : Heap} {p : Ptr} (hc : h[p]? = some .nil) :
    WordsAt h p ([] : List (Bits n)) := ⟨[], .nil hc, .nil⟩

theorem WordsAt.cons {n : ℕ} {h : Heap} {p head tail : Ptr} {w : Bits n} {ws : List (Bits n)}
    (hc : h[p]? = some (.cons head tail)) (hh : BitsAt h head w) (ht : WordsAt h tail ws) :
    WordsAt h p (w :: ws) := by
  obtain ⟨ps, hp, hw⟩ := ht
  exact ⟨head :: ps, .cons hc hp, .cons hh hw⟩

theorem WordsAt.nil_iff {n : ℕ} {h : Heap} {p : Ptr} :
    WordsAt h p ([] : List (Bits n)) ↔ h[p]? = some .nil := by
  constructor
  · rintro ⟨ps, hp, hw⟩
    cases hw
    cases hp with
    | nil hc => exact hc
  · exact WordsAt.nil

theorem WordsAt.cons_iff {n : ℕ} {h : Heap} {p : Ptr} {w : Bits n} {ws : List (Bits n)} :
    WordsAt h p (w :: ws) ↔ ∃ head tail, h[p]? = some (.cons head tail) ∧
      BitsAt h head w ∧ WordsAt h tail ws := by
  constructor
  · rintro ⟨ps, hp, hw⟩
    cases hw with
    | cons head rest =>
      cases hp with
      | cons hc ht => exact ⟨_, _, hc, head, _, ht, rest⟩
  · rintro ⟨head, tail, hc, hh, ht⟩
    exact WordsAt.cons hc hh ht

theorem allocate_word_cons {n : ℕ} {h : Heap} (hh : Valid h) {head tail : Ptr}
    {w : Bits n} {ws : List (Bits n)} (hw : BitsAt h head w) (ht : WordsAt h tail ws) :
    SafeRun h (Program.allocate (.cons head tail) h) ∧
      WordsAt (h ++ [.cons head tail]) h.length (w :: ws) := by
  obtain ⟨ps, hp, hr⟩ := ht
  obtain ⟨hs, hl⟩ := allocate_cons hh hw.allocated hp
  exact ⟨hs, head :: ps, hl, .cons (hw.mono hs.1) (hr.imp (fun _ _ h => h.mono hs.1))⟩

end WeightedMIS.ExpandedWords
