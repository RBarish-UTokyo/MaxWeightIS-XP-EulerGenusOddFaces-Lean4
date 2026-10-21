module

public import WeightedMIS.RegisterFlagKeys
public import WeightedMIS.RegisterComparator
public import WeightedMIS.RibbonTableRestrict
public import WeightedMIS.ExpandedWords

/-!
# Association lookup on two stored word lists

The association list `xs.zip ys` is never materialized: the procedure walks
both stored lists in lockstep, compares each key word with the query by the
compiled comparator, and returns the shared value word of the first match or
the default word. Renumbering a flag key splits it, looks up its edge word,
and reassembles the key with two bit allocations. Zipping with a longer range
list gives the same association list as zipping with the exact range.
-/

@[expose] public section

namespace WeightedMIS.RegisterWordAssoc

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys
open WeightedMIS.ExpandedWords

variable {p : ℕ}

/-! ## Range lists -/

/-- Zipping with a range list longer than the keys gives the exact zip. -/
theorem zip_rangeWords {α : Type*} {W M : ℕ} (xs : List α) (hM : xs.length ≤ M) :
    xs.zip (rangeWords W M) = xs.zip (rangeWords W xs.length) := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hM]
  · intro i h1 h2
    simp [List.getElem_zip]

/-- `zipWith` against a longer range list is the map over the exact zip. -/
theorem zipWith_rangeWords {α β : Type*} {W M : ℕ} (f : α → Bits W → β) (xs : List α)
    (hM : xs.length ≤ M) :
    List.zipWith f xs (rangeWords W M) =
      (xs.zip (rangeWords W xs.length)).map (fun q => f q.1 q.2) := by
  rw [← zip_rangeWords xs hM, List.zip, List.map_zipWith]

/-! ## Lookup -/

/-- Arguments 0 = keys, 1 = values, 2 = query, 3 = default. -/
def assocBody (self cmp : Fin p) : Command p :=
  .load (.register 0) 4 5 15 { CompiledTrie.failCases with
    nil := .ret [.register 3]
    cons := .load (.register 1) 6 7 15 { CompiledTrie.failCases with
      nil := .ret [.register 3]
      cons := .call cmp [.register 4, .register 2] [8, 9]
        (.branch (.register 9) (.ret [.register 6])
          (.call self [.register 5, .register 7, .register 2, .register 3] [10]
            (.ret [.register 10]))) } }

def assocBudget (n length : ℕ) : ℕ := (36 * n + 65) * length + 23

theorem assoc_compiled (code : Code p) (self cmp : Fin p)
    (hself : code self = assocBody self cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {n m : ℕ} {h : Heap} {xp yp kp dp : Ptr} {xs : List (Bits n)} {ys : List (Bits m)}
    {k : Bits n} {d : Bits m}
    (hx : WordsAt h xp xs) (hy : WordsAt h yp ys) (hk : BitsAt h kp k) (hd : BitsAt h dp d) :
    ∃ q, BitsAt h q (assoc d (xs.zip ys) k) ∧
      Within code h (initialRegisters [.pointer xp, .pointer yp, .pointer kp, .pointer dp])
        (code self) [.pointer q] h (assocBudget n xs.length) := by
  induction xs generalizing xp ys yp with
  | nil =>
    have cell := WordsAt.nil_iff.mp hx
    refine ⟨dp, by simpa [assoc] using hd, ?_⟩
    rw [hself]
    refine (Within.load (pointer := xp) (c := .nil) (by reg_simp) cell
      (ret_values (by reg_simp) le_rfl)).mono ?_
    simp [assocBudget]
  | cons x xs ih =>
    obtain ⟨xh, xt, xcell, hxh, hxt⟩ := WordsAt.cons_iff.mp hx
    cases ys with
    | nil =>
      have cell := WordsAt.nil_iff.mp hy
      refine ⟨dp, by simpa [assoc] using hd, ?_⟩
      rw [hself]
      refine (Within.load (pointer := xp) (c := .cons xh xt) (by reg_simp) xcell
        (Within.load (pointer := yp) (c := .nil) (by reg_simp) cell
        (ret_values (by reg_simp) le_rfl))).mono ?_
      simp [assocBudget]
    | cons y ys =>
      obtain ⟨yh, yt, ycell, hyh, hyt⟩ := WordsAt.cons_iff.mp hy
      have hc := RegisterComparator.compiled code cmp hcmp hxh hk
      by_cases hxk : x = k
      · refine ⟨yh, by simpa [assoc, hxk] using hyh, ?_⟩
        rw [hself]
        refine (Within.load (pointer := xp) (c := .cons xh xt) (by reg_simp) xcell
          (Within.load (pointer := yp) (c := .cons yh yt) (by reg_simp) ycell
          (call_of (by reg_simp) hc
          (Within.branch (b := true)
            (by reg_simp; simp [hxk])
            (ret_values (by reg_simp) le_rfl))))).mono ?_
        simp [assocBudget]; nlinarith
      · obtain ⟨q, hq, hw⟩ := ih hxt hyt
        refine ⟨q, by simpa [assoc, hxk] using hq, ?_⟩
        rw [hself]
        refine (Within.load (pointer := xp) (c := .cons xh xt) (by reg_simp) xcell
          (Within.load (pointer := yp) (c := .cons yh yt) (by reg_simp) ycell
          (call_of (by reg_simp) hc
          (Within.branch (b := false)
            (by reg_simp; simp [hxk])
            (call_of (by reg_simp) hw (ret_values (by reg_simp) le_rfl)))))).mono ?_
        simp [assocBudget]; nlinarith

/-! ## Renumbering flag keys -/

/-- Arguments 0 = key, 1 = old edge words, 2 = new edge words. -/
def relabelBody (split assoc mk : Fin p) : Command p :=
  .call split [.register 0] [3, 4, 5]
    (.call assoc [.register 1, .register 2, .register 5, .register 5] [6]
      (.call mk [.register 3, .register 4, .register 6] [7] (.ret [.register 7])))

structure Procedures (p : ℕ) where
  relabel : Fin p
  split : Fin p
  assoc : Fin p
  mkKey : Fin p
  cmp : Fin p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.relabel = relabelBody ids.split ids.assoc ids.mkKey ∧
  code ids.split = RegisterFlagKeys.splitBody ∧
  code ids.assoc = assocBody ids.assoc ids.cmp ∧
  code ids.mkKey = RegisterFlagKeys.mkBody ∧
  code ids.cmp = RegisterComparator.comparatorBody ids.cmp

def relabelBudget (W length : ℕ) : ℕ := assocBudget W length + 80

theorem relabel_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {kp xp yp : Ptr} {k : Bits (W + 2)}
    {xs ys : List (Bits W)}
    (hk : BitsAt h kp k) (hx : WordsAt h xp xs) (hy : WordsAt h yp ys) :
    ∃ out q, Extends h out ∧ Valid out ∧ BitsAt out q (relabelKey (xs.zip ys) k) ∧
      Within code h (initialRegisters [.pointer kp, .pointer xp, .pointer yp])
        (code ids.relabel) [.pointer q] out (relabelBudget W xs.length) := by
  obtain ⟨hrel, hsplit, hassoc, hmk, hcmp⟩ := hm
  obtain ⟨wp, hw, hs⟩ := split_compiled code ids.split hsplit hk
  obtain ⟨ap, ha, hav⟩ := assoc_compiled code ids.assoc ids.cmp hassoc hcmp hx hy hw hw
  obtain ⟨out, q, he, ho, hq, hmkw⟩ :=
    mk_compiled code ids.mkKey hmk hh ha (sideBit k) (endBit k)
  refine ⟨out, q, he, ho, hq, ?_⟩
  rw [hrel]
  refine (call_of (by reg_simp) hs (call_of (by reg_simp) hav
    (call_of (by reg_simp) hmkw (ret_values (by reg_simp) le_rfl)))).mono ?_
  simp [relabelBudget]; omega

end WeightedMIS.RegisterWordAssoc
