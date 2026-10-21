module

public import WeightedMIS.RegisterFirstReturn
public import WeightedMIS.RegisterListFilter
public import WeightedMIS.RegisterListMap
public import WeightedMIS.InducedTable
public import WeightedMIS.ComponentTable

/-!
# Retained edge words of stored ribbon tables

The records whose endpoint words are retained are selected by the list
filter with a predicate procedure that reads the stored endpoint words and
runs the compiled membership procedure; the selected records share their
cells. Their key words are then read off by the list map without copying.
The theorems refine `inducedEdgeWords`, `componentEdgeWords`, and the list
of record keys.
-/

@[expose] public section

namespace WeightedMIS.RegisterEdgeWords

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys
open WeightedMIS.ExpandedWords WeightedMIS.RegisterFirstReturn

variable {p : ℕ}

/-! ## Procedures -/

/-- Arguments 0 = record, 1 = vertex words; both endpoint words are members. -/
def bothBody (mem : Fin p) : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    pair := .load (.register 3) 4 5 15 { CompiledTrie.failCases with
      pair := .load (.register 5) 6 7 15 { CompiledTrie.failCases with
        pair := .call mem [.register 4, .register 1] [8]
          (.branch (.register 8)
            (.call mem [.register 6, .register 1] [9] (.ret [.register 9]))
            (.ret [.flag false])) } } }

/-- Arguments 0 = record, 1 = vertex words; the left endpoint word is a member. -/
def leftEndBody (mem : Fin p) : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    pair := .load (.register 3) 4 5 15 { CompiledTrie.failCases with
      pair := .call mem [.register 4, .register 1] [8] (.ret [.register 8]) } }

/-- Argument 0 = record; the result is its shared key word. -/
def keyBody : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with pair := .ret [.register 2] }

/-- Arguments 0 = table, 1 = vertex words. -/
def edgesBody (filter keys : Fin p) : Command p :=
  .call filter [.register 0, .register 1] [2]
    (.call keys [.register 2, .null] [3] (.ret [.register 3]))

structure Procedures (p : ℕ) where
  inducedEdges : Fin p
  componentEdges : Fin p
  bothFilter : Fin p
  leftFilter : Fin p
  both : Fin p
  leftEnd : Fin p
  keys : Fin p
  key : Fin p
  mem : Fin p
  cmp : Fin p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.inducedEdges = edgesBody ids.bothFilter ids.keys ∧
  code ids.componentEdges = edgesBody ids.leftFilter ids.keys ∧
  code ids.bothFilter = RegisterListFilter.body ids.bothFilter ids.both ∧
  code ids.leftFilter = RegisterListFilter.body ids.leftFilter ids.leftEnd ∧
  code ids.both = bothBody ids.mem ∧
  code ids.leftEnd = leftEndBody ids.mem ∧
  code ids.keys = RegisterListMap.body ids.keys ids.key ∧
  code ids.key = keyBody ∧
  code ids.mem = RegisterMembership.membershipBody ids.mem ids.cmp ∧
  code ids.cmp = RegisterComparator.comparatorBody ids.cmp

def keysBudget (t : ℕ) : ℕ := 48 * t + 13

def inducedBudget (W t kv : ℕ) : ℕ :=
  (2 * RegisterMembership.budget W kv + 85) * t + keysBudget t + 40

def componentBudget (W t kv : ℕ) : ℕ :=
  (RegisterMembership.budget W kv + 65) * t + keysBudget t + 40

/-! ## Correctness -/

theorem keys_compiled (code : Code p) (keys key : Fin p)
    (hkeys : code keys = RegisterListMap.body keys key) (hkey : code key = keyBody)
    {W : ℕ} {h : Heap} (hh : Valid h) {tp : Ptr} {T : List (EdgeRec W)}
    (hT : RecordsAt h tp T) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q (T.map EdgeRec.key) ∧
      Within code h (initialRegisters [.pointer tp, .pointer 0]) (code keys) [.pointer q] out
        (keysBudget T.length) := by
  obtain ⟨out, q, he, ho, hq, hw⟩ := RegisterListMap.compiled_const code keys key hkeys
    EdgeRecAt (fun _ _ (_ : Unit) => True) (fun h p (w : Bits W) => BitsAt h p w)
    (fun he _ _ hr => hr.mono he) (fun _ _ _ _ => trivial) (fun he _ _ hb => hb.mono he)
    (fun _ hb => hb.allocated) (fun _ r => r.key) 13 (data := ()) (dataPtr := 0) hh hT trivial
    (fun {h} hv {xp} {x} _ hx _ => by
      obtain ⟨kp, a, _, _, _, _, _, _, _, _, _, _, hp, hk, -⟩ := hx
      refine ⟨h, kp, .refl h, hv, hk, ?_⟩
      rw [hkey]
      refine (Within.load (pointer := xp) (c := .pair kp a) (by reg_simp) hp
        (ret_values (by reg_simp) le_rfl)).mono ?_
      norm_num)
  exact ⟨out, q, he, ho, hq, hw.mono (by simp [keysBudget])⟩

/-- Keys of the selected records, for any record predicate computed by a
filter procedure. -/
theorem edges_generic (code : Code p) (self filter item keys key : Fin p)
    (hself : code self = edgesBody filter keys)
    (hfilter : code filter = RegisterListFilter.body filter item)
    (hkeys : code keys = RegisterListMap.body keys key) (hkey : code key = keyBody)
    {W : ℕ} (pred : List (Bits W) → EdgeRec W → Bool) (itemBudget : ℕ)
    {h : Heap} (hh : Valid h) {tp vp : Ptr} {T : List (EdgeRec W)} {vs : List (Bits W)}
    (hT : RecordsAt h tp T) (hv : WordsAt h vp vs)
    (itemCompiled : ∀ {h : Heap}, Valid h → ∀ {rp : Ptr} {r : EdgeRec W},
      EdgeRecAt h rp r → WordsAt h vp vs →
      Within code h (initialRegisters [.pointer rp, .pointer vp]) (code item)
        [.flag (pred vs r)] h itemBudget) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q ((T.filter (pred vs)).map EdgeRec.key) ∧
      Within code h (initialRegisters [.pointer tp, .pointer vp]) (code self) [.pointer q] out
        ((itemBudget + 35) * T.length + keysBudget T.length + 40) := by
  obtain ⟨o1, f, e1, v1, hf, w1⟩ := RegisterListFilter.compiled_const code filter item hfilter
    EdgeRecAt WordsAt (fun he _ _ hr => hr.mono he) (fun he _ _ hw => hw.mono he) pred itemBudget
    hh hT hv (fun {h} hv' _ _ _ hx hd => ⟨h, .refl h, hv', itemCompiled hv' hx hd⟩)
  obtain ⟨o2, q, e2, v2, hq, w2⟩ := keys_compiled code keys key hkeys hkey v1 hf
  refine ⟨o2, q, e1.trans e2, v2, hq, ?_⟩
  rw [hself]
  have hlen : (T.filter (pred vs)).length ≤ T.length := List.length_filter_le _ _
  refine (call_of (by reg_simp) w1 (call_of (by reg_simp) w2
    (ret_values (by reg_simp) le_rfl))).mono ?_
  simp [keysBudget]; omega

theorem both_compiled (code : Code p) (self mem cmp : Fin p) (hself : code self = bothBody mem)
    (hmem : code mem = RegisterMembership.membershipBody mem cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {W : ℕ} {h : Heap} {rp vp : Ptr} {r : EdgeRec W} {vs : List (Bits W)}
    (hr : EdgeRecAt h rp r) (hv : WordsAt h vp vs) :
    Within code h (initialRegisters [.pointer rp, .pointer vp]) (code self)
      [.flag (decide (r.left ∈ vs ∧ r.right ∈ vs))] h
      (2 * RegisterMembership.budget W vs.length + 50) := by
  obtain ⟨kp, a, lp, b, rp', c, _, _, _, _, _, _, hp, -, ha, hl, hb, hrr, -⟩ := hr
  have m1 := RegisterMembership.compiled code mem cmp hmem hcmp hl hv
  have m2 := RegisterMembership.compiled code mem cmp hmem hcmp hrr hv
  rw [found_eq_decide] at m1 m2
  rw [hself]
  by_cases h1 : r.left ∈ vs
  · refine (Within.load (pointer := rp) (c := .pair kp a) (by reg_simp) hp
      (Within.load (pointer := a) (c := .pair lp b) (by reg_simp) ha
      (Within.load (pointer := b) (c := .pair rp' c) (by reg_simp) hb
      (call_of (by reg_simp) m1 (Within.branch (b := true) (by reg_simp; simpa using h1)
      (call_of (by reg_simp) m2 (ret_values (by reg_simp; simp [h1]) le_rfl))))))).mono ?_
    simp; omega
  · refine (Within.load (pointer := rp) (c := .pair kp a) (by reg_simp) hp
      (Within.load (pointer := a) (c := .pair lp b) (by reg_simp) ha
      (Within.load (pointer := b) (c := .pair rp' c) (by reg_simp) hb
      (call_of (by reg_simp) m1 (Within.branch (b := false) (by reg_simp; simpa using h1)
      (ret_values (by reg_simp; simp [h1]) le_rfl)))))).mono ?_
    simp; omega

theorem leftEnd_compiled (code : Code p) (self mem cmp : Fin p)
    (hself : code self = leftEndBody mem)
    (hmem : code mem = RegisterMembership.membershipBody mem cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {W : ℕ} {h : Heap} {rp vp : Ptr} {r : EdgeRec W} {vs : List (Bits W)}
    (hr : EdgeRecAt h rp r) (hv : WordsAt h vp vs) :
    Within code h (initialRegisters [.pointer rp, .pointer vp]) (code self)
      [.flag (decide (r.left ∈ vs))] h (RegisterMembership.budget W vs.length + 30) := by
  obtain ⟨kp, a, lp, b, _, _, _, _, _, _, _, _, hp, -, ha, hl, -⟩ := hr
  have m1 := RegisterMembership.compiled code mem cmp hmem hcmp hl hv
  rw [found_eq_decide] at m1
  rw [hself]
  refine (Within.load (pointer := rp) (c := .pair kp a) (by reg_simp) hp
    (Within.load (pointer := a) (c := .pair lp b) (by reg_simp) ha
    (call_of (by reg_simp) m1 (ret_values (by reg_simp) le_rfl)))).mono ?_
  simp; omega

theorem inducedEdges_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {tp vp : Ptr} {T : List (EdgeRec W)} {vs : List (Bits W)}
    (hT : RecordsAt h tp T) (hv : WordsAt h vp vs) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q (InducedTable.inducedEdgeWords T vs) ∧
      Within code h (initialRegisters [.pointer tp, .pointer vp]) (code ids.inducedEdges)
        [.pointer q] out (inducedBudget W T.length vs.length) := by
  obtain ⟨hind, -, hbf, -, hboth, -, hkeys, hkey, hmem, hcmp⟩ := hm
  obtain ⟨out, q, he, ho, hq, hw⟩ := edges_generic code ids.inducedEdges ids.bothFilter ids.both
    ids.keys ids.key hind hbf hkeys hkey (fun vs r => decide (r.left ∈ vs ∧ r.right ∈ vs))
    (2 * RegisterMembership.budget W vs.length + 50) hh hT hv
    (fun _ _ _ hx hd => both_compiled code ids.both ids.mem ids.cmp hboth hmem hcmp hx hd)
  refine ⟨out, q, he, ho, ?_, hw.mono ?_⟩
  · have hfm :=
      filterMap_ite_eq (fun r : EdgeRec W => r.left ∈ vs ∧ r.right ∈ vs) EdgeRec.key T
    rw [InducedTable.inducedEdgeWords, hfm]
    exact hq
  · simp only [inducedBudget]; ring_nf; omega

theorem componentEdges_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {tp vp : Ptr} {T : List (EdgeRec W)} {vs : List (Bits W)}
    (hT : RecordsAt h tp T) (hv : WordsAt h vp vs) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q (ComponentTable.componentEdgeWords T vs) ∧
      Within code h (initialRegisters [.pointer tp, .pointer vp]) (code ids.componentEdges)
        [.pointer q] out (componentBudget W T.length vs.length) := by
  obtain ⟨-, hcomp, -, hlf, -, hleft, hkeys, hkey, hmem, hcmp⟩ := hm
  obtain ⟨out, q, he, ho, hq, hw⟩ := edges_generic code ids.componentEdges ids.leftFilter
    ids.leftEnd ids.keys ids.key hcomp hlf hkeys hkey (fun vs r => decide (r.left ∈ vs))
    (RegisterMembership.budget W vs.length + 30) hh hT hv
    (fun _ _ _ hx hd => leftEnd_compiled code ids.leftEnd ids.mem ids.cmp hleft hmem hcmp hx hd)
  refine ⟨out, q, he, ho, ?_, hw.mono ?_⟩
  · have hfm := filterMap_ite_eq (fun r : EdgeRec W => r.left ∈ vs) EdgeRec.key T
    rw [ComponentTable.componentEdgeWords, hfm]
    exact hq
  · simp only [componentBudget]; ring_nf; omega

end WeightedMIS.RegisterEdgeWords
