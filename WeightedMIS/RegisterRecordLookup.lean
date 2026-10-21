module

public import WeightedMIS.RegisterFlagKeys
public import WeightedMIS.RegisterListFind
public import WeightedMIS.RegisterComparator

/-!
# Record lookup and corner lookup on stored ribbon tables

The record of an edge word is found by the list search combinator with a
predicate procedure that loads the stored key and runs the compiled
comparator. The returned address is shared with the stored record. Corner
lookup splits the flag key, finds the record of its edge word, and follows
the four record cells selected by the two flag bits; an unknown key is
returned unchanged. The theorems refine `findRecord` and `cornerKey`.
-/

@[expose] public section

namespace WeightedMIS.RegisterRecordLookup

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys

variable {p : ℕ}

/-- Arguments 0 = record, 1 = query word; the result is whether the stored
key equals the query. -/
def keyMatchBody (cmp : Fin p) : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    pair := .call cmp [.register 2, .register 1] [4, 5] (.ret [.register 5]) }

/-- Arguments 0 = table, 1 = flag key; the result is the corner key. -/
def cornerBody (split find : Fin p) : Command p :=
  .call split [.register 1] [2, 3, 4]
    (.call find [.register 0, .register 4] [5, 6]
      (.branch (.register 5)
        (.load (.register 6) 7 8 15 { CompiledTrie.failCases with
          pair := .load (.register 8) 7 9 15 { CompiledTrie.failCases with
            pair := .load (.register 9) 7 10 15 { CompiledTrie.failCases with
              pair := .load (.register 10) 11 12 15 { CompiledTrie.failCases with
                pair := .branch (.register 2)
                  (.load (.register 12) 13 14 15 { CompiledTrie.failCases with
                    pair := .branch (.register 3) (.ret [.register 14]) (.ret [.register 13]) })
                  (.load (.register 11) 13 14 15 { CompiledTrie.failCases with
                    pair := .branch (.register 3) (.ret [.register 14])
                      (.ret [.register 13]) }) } } } })
        (.ret [.register 1])))

structure Procedures (p : ℕ) where
  corner : Fin p
  split : Fin p
  find : Fin p
  keyMatch : Fin p
  cmp : Fin p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.corner = cornerBody ids.split ids.find ∧
  code ids.split = RegisterFlagKeys.splitBody ∧
  code ids.find = RegisterListFind.body ids.find ids.keyMatch ∧
  code ids.keyMatch = keyMatchBody ids.cmp ∧
  code ids.cmp = RegisterComparator.comparatorBody ids.cmp

def keyMatchBudget (W : ℕ) : ℕ := 36 * W + 43

def findBudget (W t : ℕ) : ℕ := (36 * W + 73) * t + 15

def cornerBudget (W t : ℕ) : ℕ := findBudget W t + 100

theorem keyMatch_compiled (code : Code p) (self cmp : Fin p)
    (hself : code self = keyMatchBody cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {W : ℕ} {h : Heap} {rp gp : Ptr} {r : EdgeRec W} {g : Bits W}
    (hr : EdgeRecAt h rp r) (hg : BitsAt h gp g) :
    Within code h (initialRegisters [.pointer rp, .pointer gp]) (code self)
      [.flag (decide (r.key = g))] h (keyMatchBudget W) := by
  obtain ⟨kp, a, _, _, _, _, _, _, _, _, _, _, hp, hk, -⟩ := hr
  have hc := RegisterComparator.compiled code cmp hcmp hk hg
  rw [hself]
  refine (Within.load (pointer := rp) (c := .pair kp a) (by reg_simp) hp
    (call_of (by reg_simp) hc
    (ret_values (by reg_simp) le_rfl))).mono ?_
  simp [keyMatchBudget]; omega

/-- Record search by edge word; the returned address is the stored record. -/
theorem find_compiled (code : Code p) (find keyMatch cmp : Fin p)
    (hfind : code find = RegisterListFind.body find keyMatch)
    (hkey : code keyMatch = keyMatchBody cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {W : ℕ} {h : Heap} (hh : Valid h) {tp gp : Ptr} {T : List (EdgeRec W)} {g : Bits W}
    (hT : RecordsAt h tp T) (hg : BitsAt h gp g) :
    ∃ out q, Extends h out ∧ Valid out ∧
      (∀ r, findRecord T g = some r → EdgeRecAt out q r) ∧
      (findRecord T g = none → q = 0) ∧
      Within code h (initialRegisters [.pointer tp, .pointer gp]) (code find)
        [.flag (findRecord T g).isSome, .pointer q] out (findBudget W T.length) := by
  obtain ⟨out, q, he, ho, hs, hn, hw⟩ := RegisterListFind.compiled_const code find keyMatch
    hfind EdgeRecAt (fun h p (g : Bits W) => BitsAt h p g)
    (fun he _ _ hr => hr.mono he) (fun he _ _ hb => hb.mono he)
    (fun g r => decide (r.key = g)) (keyMatchBudget W) hh hT hg
    (fun {h} hv {xp} {x} _ hx hd =>
      ⟨h, .refl h, hv, keyMatch_compiled code keyMatch cmp hkey hcmp hx hd⟩)
  refine ⟨out, q, he, ho, hs, hn, hw.mono ?_⟩
  simp only [keyMatchBudget, findBudget]
  ring_nf
  omega

theorem corner_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {tp xp : Ptr} {T : List (EdgeRec W)} {x : Bits (W + 2)}
    (hT : RecordsAt h tp T) (hx : BitsAt h xp x) :
    ∃ out q, Extends h out ∧ Valid out ∧ BitsAt out q (cornerKey T x) ∧
      Within code h (initialRegisters [.pointer tp, .pointer xp]) (code ids.corner)
        [.pointer q] out (cornerBudget W T.length) := by
  obtain ⟨hcorner, hsplit, hfind, hkey, hcmp⟩ := hm
  obtain ⟨wp, hw, hsp⟩ := split_compiled code ids.split hsplit hx
  obtain ⟨out, q, he, ho, hs, hn, hf⟩ :=
    find_compiled code ids.find ids.keyMatch ids.cmp hfind hkey hcmp hh hT hw
  rcases x with _ | ⟨s, _ | ⟨t, w⟩⟩
  simp only [edgePart, sideBit, endBit] at hw hsp hs hn hf
  cases hr : findRecord T w with
  | none =>
    have hq := hn hr
    subst hq
    rw [hr] at hf
    refine ⟨out, xp, he, ho, ?_, ?_⟩
    · simpa [cornerKey, edgePart, hr] using hx.mono he
    rw [hcorner]
    refine (call_of (by reg_simp) hsp
        (call_of (by reg_simp) hf
          (Within.branch (b := false) (by reg_simp)
            (ret_values (by reg_simp) le_rfl)))).mono ?_
    simp [cornerBudget]; omega
  | some r =>
    obtain ⟨kp, a, lp, b, rp, c, q0, q1, c00p, c01p, c10p, c11p,
      hp, -, ha, -, hb, -, hc, hq0, h00, h01, hq1, h10, h11⟩ := hs r hr
    rw [hr] at hf
    have hsel : cornerKey T (.cons s (.cons t w)) = r.select s t := by
      simp [cornerKey, edgePart, sideBit, endBit, hr]
    rw [hsel, hcorner]
    -- The shared prefix: split, find, branch, and the four record loads.
    have hpre : ∀ {res : Ptr} {B : ℕ},
        Within code out (loadRegisters (loadRegisters (loadRegisters (loadRegisters
          (bindResults (bindResults (initialRegisters [.pointer tp, .pointer xp]) [2, 3, 4]
            [.flag s, .flag t, .pointer wp]) [5, 6] [.flag true, .pointer q])
            7 8 15 (.pair kp a)) 7 9 15 (.pair lp b)) 7 10 15 (.pair rp c)) 11 12 15 (.pair q0 q1))
          (.branch (.register 2)
            (.load (.register 12) 13 14 15 { CompiledTrie.failCases with
              pair := .branch (.register 3) (.ret [.register 14]) (.ret [.register 13]) })
            (.load (.register 11) 13 14 15 { CompiledTrie.failCases with
              pair := .branch (.register 3) (.ret [.register 14]) (.ret [.register 13]) }))
          [.pointer res] out B → B ≤ 22 →
        Within code h (initialRegisters [.pointer tp, .pointer xp])
          (cornerBody ids.split ids.find) [.pointer res] out (cornerBudget W T.length) := by
      intro res B hB hle
      refine (call_of (by reg_simp) hsp
        (call_of (by reg_simp) hf
          (Within.branch (b := true) (by reg_simp)
            (Within.load (pointer := q) (c := .pair kp a)
              (by reg_simp) hp
            (Within.load (pointer := a) (c := .pair lp b)
              (by reg_simp) ha
            (Within.load (pointer := b) (c := .pair rp c)
              (by reg_simp) hb
            (Within.load (pointer := c) (c := .pair q0 q1)
              (by reg_simp) hc hB))))))).mono ?_
      simp [cornerBudget]; omega
    cases s <;> cases t
    · exact ⟨out, c00p, he, ho, h00, hpre (Within.branch (b := false) (by reg_simp)
        (Within.load (pointer := q0) (c := .pair c00p c01p)
          (by reg_simp) hq0
          (Within.branch (b := false) (by reg_simp)
            (ret_values (by reg_simp) le_rfl)))) (by norm_num)⟩
    · exact ⟨out, c01p, he, ho, h01, hpre (Within.branch (b := false) (by reg_simp)
        (Within.load (pointer := q0) (c := .pair c00p c01p)
          (by reg_simp) hq0
          (Within.branch (b := true) (by reg_simp)
            (ret_values (by reg_simp) le_rfl)))) (by norm_num)⟩
    · exact ⟨out, c10p, he, ho, h10, hpre (Within.branch (b := true) (by reg_simp)
        (Within.load (pointer := q1) (c := .pair c10p c11p)
          (by reg_simp) hq1
          (Within.branch (b := false) (by reg_simp)
            (ret_values (by reg_simp) le_rfl)))) (by norm_num)⟩
    · exact ⟨out, c11p, he, ho, h11, hpre (Within.branch (b := true) (by reg_simp)
        (Within.load (pointer := q1) (c := .pair c10p c11p)
          (by reg_simp) hq1
          (Within.branch (b := true) (by reg_simp)
            (ret_values (by reg_simp) le_rfl)))) (by norm_num)⟩

end WeightedMIS.RegisterRecordLookup
