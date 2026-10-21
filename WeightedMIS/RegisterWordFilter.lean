module

public import WeightedMIS.RegisterFirstReturn
public import WeightedMIS.RegisterListFilter
public import WeightedMIS.RegisterListZip
public import WeightedMIS.InducedTable
public import WeightedMIS.ComponentTable

/-!
# Selecting stored words by masks and by membership

A per-vertex mask is a chain of bit cells. The mask procedure walks a word
list and the mask in lockstep and keeps the shared words whose mask bit is
set; the selection procedure walks a range list and an item list in lockstep
and keeps the shared items whose range word is a member of a stored word
list. Member words are a filter of the range list with the compiled
membership procedure, and a prefix of a range list is a zip that returns its
left item. The theorems refine `maskWords`, `selectBy`, and `memberWords`.
-/

@[expose] public section

namespace WeightedMIS.RegisterWordFilter

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys
open WeightedMIS.ExpandedWords WeightedMIS.RegisterFirstReturn

variable {p : ℕ}

/-! ## Stored masks -/

/-- A list of flags stored as a chain of bit cells ending in a null cell. -/
def MaskAt (h : Heap) : Ptr → List Bool → Prop
  | p, [] => h[p]? = some .nil
  | p, b :: bs => ∃ t, h[p]? = some (.bit b t) ∧ MaskAt h t bs

theorem MaskAt.mono {h h' : Heap} (he : Extends h h') {p : Ptr} {bs : List Bool}
    (hm : MaskAt h p bs) : MaskAt h' p bs := by
  induction bs generalizing p with
  | nil => exact he.lookup hm
  | cons b bs ih =>
    obtain ⟨t, hc, ht⟩ := hm
    exact ⟨t, he.lookup hc, ih ht⟩

/-! ## Reference functions on arbitrary lists -/

/-- Items whose paired flag is set. -/
def maskFilter {α : Type*} (xs : List α) (bs : List Bool) : List α :=
  (xs.zip bs).filterMap (fun q => if q.2 then some q.1 else none)

/-- Items whose paired word is a member of `ks`. -/
def selectFilter {α : Type*} {W : ℕ} (rs : List (Bits W)) (ws : List α) (ks : List (Bits W)) :
    List α :=
  (rs.zip ws).filterMap (fun q => if q.1 ∈ ks then some q.2 else none)

theorem zip_rangeWords_left {α : Type*} {W M : ℕ} (xs : List α) (hM : xs.length ≤ M) :
    (rangeWords W M).zip xs = (rangeWords W xs.length).zip xs := by
  apply List.ext_getElem
  · simp [Nat.min_eq_right hM]
  · intro i h1 h2
    simp [List.getElem_zip]

theorem maskWords_eq {W M : ℕ} (mask : List Bool) (hM : mask.length ≤ M) :
    InducedTable.maskWords W mask = maskFilter (rangeWords W M) mask := by
  rw [InducedTable.maskWords, maskFilter, zip_rangeWords_left mask hM]

theorem selectBy_eq_filter {α : Type*} {W M : ℕ} (ks : List (Bits W)) (ws : List α)
    (hM : ws.length ≤ M) : selectBy ks ws = selectFilter (rangeWords W M) ws ks := by
  rw [selectBy, selectFilter, zip_rangeWords_left ws hM]

theorem zipWith_left_rangeWords {α : Type*} {W M : ℕ} (xs : List α) (hM : xs.length ≤ M) :
    List.zipWith (fun a _ => a) (rangeWords W M) xs = rangeWords W xs.length := by
  apply List.ext_getElem
  · simp [Nat.min_eq_right hM]
  · intro i h1 h2
    simp

/-! ## Procedures -/

/-- Arguments 0 = items, 1 = mask. -/
def maskBody (self : Fin p) : Command p :=
  .load (.register 1) 2 3 4 { CompiledTrie.failCases with
    nil := .ret [.null]
    bit := .load (.register 0) 5 6 15 { CompiledTrie.failCases with
      nil := .ret [.null]
      cons := .call self [.register 6, .register 2] [7]
        (.branch (.register 4)
          (.allocate 8 (.cons (.register 5) (.register 7)) (.ret [.register 8]))
          (.ret [.register 7])) } }

/-- Arguments 0 = words, 1 = items, 2 = member words. -/
def selectBody (self mem : Fin p) : Command p :=
  .load (.register 1) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := .load (.register 0) 5 6 15 { CompiledTrie.failCases with
      nil := .ret [.null]
      cons := .call self [.register 6, .register 4, .register 2] [7]
        (.call mem [.register 5, .register 2] [8]
          (.branch (.register 8)
            (.allocate 9 (.cons (.register 3) (.register 7)) (.ret [.register 9]))
            (.ret [.register 7]))) } }

/-- Arguments 0 = left item, 1 = right item; returns the left item. -/
def leftBody : Command p := .ret [.register 0]

structure Procedures (p : ℕ) where
  mask : Fin p
  select : Fin p
  members : Fin p
  take : Fin p
  left : Fin p
  mem : Fin p
  cmp : Fin p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.mask = maskBody ids.mask ∧
  code ids.select = selectBody ids.select ids.mem ∧
  code ids.members = RegisterListFilter.body ids.members ids.mem ∧
  code ids.take = RegisterListZip.body ids.take ids.left ∧
  code ids.left = leftBody ∧
  code ids.mem = RegisterMembership.membershipBody ids.mem ids.cmp ∧
  code ids.cmp = RegisterComparator.comparatorBody ids.cmp

def maskBudget (length : ℕ) : ℕ := 40 * length + 23

def selectBudget (W k length : ℕ) : ℕ := (RegisterMembership.budget W k + 50) * length + 23

def membersBudget (W k length : ℕ) : ℕ := (RegisterMembership.budget W k + 35) * length + 13

def takeBudget (length : ℕ) : ℕ := 48 * length + 23

/-! ## Correctness -/

theorem mask_compiled {α : Type*} (code : Code p) (self : Fin p)
    (hself : code self = maskBody self) (R : Heap → Ptr → α → Prop)
    (mono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, R h ptr x → R h' ptr x)
    {h : Heap} (hh : Valid h) {xp mp : Ptr} {xs : List α} {mask : List Bool}
    (hx : ListRep R h xp xs) (hmask : MaskAt h mp mask) :
    ∃ out q, Extends h out ∧ Valid out ∧ ListRep R out q (maskFilter xs mask) ∧
      Within code h (initialRegisters [.pointer xp, .pointer mp]) (code self) [.pointer q] out
        (maskBudget mask.length) := by
  induction mask generalizing h xp mp xs with
  | nil =>
    refine ⟨h, 0, .refl h, hh,
      by simpa [maskFilter] using RegisterListCommon.listRep_null hh, ?_⟩
    rw [hself]
    refine (Within.load (pointer := mp) (c := .nil) (by reg_simp) hmask
      (ret_values (by reg_simp) le_rfl)).mono ?_
    simp [maskBudget]
  | cons b mask ih =>
    obtain ⟨t, hc, ht⟩ := hmask
    obtain ⟨ps, hl, hrel⟩ := hx
    cases hrel with
    | nil =>
      cases hl with
      | nil cell =>
      refine ⟨h, 0, .refl h, hh,
        by simpa [maskFilter] using RegisterListCommon.listRep_null hh, ?_⟩
      rw [hself]
      refine (Within.load (pointer := mp) (c := .bit b t) (by reg_simp) hc
        (Within.load (pointer := xp) (c := .nil) (by reg_simp) cell
        (ret_values (by reg_simp) le_rfl))).mono ?_
      simp [maskBudget]
    | @cons a x ps' xs' ha hrest =>
      cases hl with
      | @cons _ _ rest _ cell hrl =>
      obtain ⟨out, q, he, ho, hq, hw⟩ := ih hh ⟨ps', hrl, hrest⟩ ht
      have hal : a < out.length :=
        lt_of_lt_of_le (RegisterListCommon.ListAt.head_allocated hh cell) he.length_le
      cases b with
      | true =>
        obtain ⟨e2, v2, hr2⟩ :=
          RegisterListCommon.allocate_consRep mono ho (mono he a x ha) hal hq
        refine ⟨_, _, he.trans e2, v2, by simpa [maskFilter] using hr2, ?_⟩
        rw [hself]
        refine (Within.load (pointer := mp) (c := .bit true t) (by reg_simp) hc
          (Within.load (pointer := xp) (c := .cons a rest) (by reg_simp) cell
          (call_of (by reg_simp) hw (Within.branch (b := true) (by reg_simp)
          (Within.allocate (c := Cell.cons a q) (by reg_simp)
          (ret_values (by reg_simp) le_rfl)))))).mono ?_
        simp [maskBudget, CellExpr.args]; omega
      | false =>
        refine ⟨out, q, he, ho, by simpa [maskFilter] using hq, ?_⟩
        rw [hself]
        refine (Within.load (pointer := mp) (c := .bit false t) (by reg_simp) hc
          (Within.load (pointer := xp) (c := .cons a rest) (by reg_simp) cell
          (call_of (by reg_simp) hw (Within.branch (b := false) (by reg_simp)
          (ret_values (by reg_simp) le_rfl))))).mono ?_
        simp [maskBudget]; omega

theorem select_compiled {α : Type*} (code : Code p) (self mem cmp : Fin p)
    (hself : code self = selectBody self mem)
    (hmem : code mem = RegisterMembership.membershipBody mem cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (R : Heap → Ptr → α → Prop)
    (mono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, R h ptr x → R h' ptr x)
    {W : ℕ} {h : Heap} (hh : Valid h) {rp wp kp : Ptr} {rs : List (Bits W)} {ws : List α}
    {ks : List (Bits W)}
    (hr : WordsAt h rp rs) (hw : ListRep R h wp ws) (hk : WordsAt h kp ks) :
    ∃ out q, Extends h out ∧ Valid out ∧ ListRep R out q (selectFilter rs ws ks) ∧
      Within code h (initialRegisters [.pointer rp, .pointer wp, .pointer kp]) (code self)
        [.pointer q] out (selectBudget W ks.length ws.length) := by
  induction ws generalizing h rp wp rs with
  | nil =>
    obtain ⟨ps, hl, hrel⟩ := hw
    cases hrel
    cases hl with
    | nil cell =>
    refine ⟨h, 0, .refl h, hh,
      by simpa [selectFilter] using RegisterListCommon.listRep_null hh, ?_⟩
    rw [hself]
    refine (Within.load (pointer := wp) (c := .nil) (by reg_simp) cell
      (ret_values (by reg_simp) le_rfl)).mono ?_
    simp [selectBudget]
  | cons x xs' ih =>
    obtain ⟨ps, hl, hrel⟩ := hw
    cases hrel with
    | @cons a _ ps' _ ha hrest =>
    cases hl with
    | @cons _ _ rest _ cell hrl =>
    cases rs with
    | nil =>
      have rcell := WordsAt.nil_iff.mp hr
      refine ⟨h, 0, .refl h, hh,
        by simpa [selectFilter] using RegisterListCommon.listRep_null hh, ?_⟩
      rw [hself]
      refine (Within.load (pointer := wp) (c := .cons a rest) (by reg_simp) cell
        (Within.load (pointer := rp) (c := .nil) (by reg_simp) rcell
        (ret_values (by reg_simp) le_rfl))).mono ?_
      simp [selectBudget]
    | cons r rs =>
      obtain ⟨rh, rt, rcell, hrh, hrt⟩ := WordsAt.cons_iff.mp hr
      obtain ⟨out, q, he, ho, hq, hw⟩ := ih hh hrt ⟨ps', hrl, hrest⟩ hk
      have hm := RegisterMembership.compiled code mem cmp hmem hcmp (hrh.mono he) (hk.mono he)
      rw [found_eq_decide] at hm
      have hal : a < out.length :=
        lt_of_lt_of_le (RegisterListCommon.ListAt.head_allocated hh cell) he.length_le
      by_cases hin : r ∈ ks
      · obtain ⟨e2, v2, hr2⟩ :=
          RegisterListCommon.allocate_consRep mono ho (mono he a x ha) hal hq
        refine ⟨_, _, he.trans e2, v2, by simpa [selectFilter, hin] using hr2, ?_⟩
        rw [hself]
        refine (Within.load (pointer := wp) (c := .cons a rest) (by reg_simp) cell
          (Within.load (pointer := rp) (c := .cons rh rt) (by reg_simp) rcell
          (call_of (by reg_simp) hw (call_of (by reg_simp) hm
          (Within.branch (b := true) (by reg_simp; simpa using hin)
          (Within.allocate (c := Cell.cons a q) (by reg_simp)
          (ret_values (by reg_simp) le_rfl))))))).mono ?_
        simp [selectBudget, CellExpr.args]; nlinarith
      · refine ⟨out, q, he, ho, by simpa [selectFilter, hin] using hq, ?_⟩
        rw [hself]
        refine (Within.load (pointer := wp) (c := .cons a rest) (by reg_simp) cell
          (Within.load (pointer := rp) (c := .cons rh rt) (by reg_simp) rcell
          (call_of (by reg_simp) hw (call_of (by reg_simp) hm
          (Within.branch (b := false) (by reg_simp; simpa using hin)
          (ret_values (by reg_simp) le_rfl)))))).mono ?_
        simp [selectBudget]; nlinarith

theorem members_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {rp sp : Ptr} {rs S : List (Bits W)}
    (hr : WordsAt h rp rs) (hs : WordsAt h sp S) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q (rs.filter (fun w => decide (w ∈ S))) ∧
      Within code h (initialRegisters [.pointer rp, .pointer sp]) (code ids.members)
        [.pointer q] out (membersBudget W S.length rs.length) := by
  obtain ⟨-, -, hmembers, -, -, hmem, hcmp⟩ := hm
  obtain ⟨out, q, he, ho, hq, hw⟩ := RegisterListFilter.compiled_const code ids.members ids.mem
    hmembers (fun h p (w : Bits W) => BitsAt h p w) WordsAt (fun he _ _ hb => hb.mono he)
    (fun he _ _ hb => hb.mono he) (fun S w => decide (w ∈ S))
    (RegisterMembership.budget W S.length) hh hr hs
    (fun {h} _ _ _ _ hx hd => ⟨h, .refl h, ‹Valid h›, by
      simpa [found_eq_decide] using
        RegisterMembership.compiled code ids.mem ids.cmp hmem hcmp hx hd⟩)
  exact ⟨out, q, he, ho, hq, hw.mono (by simp [membersBudget])⟩

/-- The member words of a range are the range words occurring in `S`. -/
theorem members_memberWords (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W k : ℕ} {h : Heap} (hh : Valid h) {rp sp : Ptr} {S : List (Bits W)}
    (hr : WordsAt h rp (rangeWords W k)) (hs : WordsAt h sp S) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (ComponentTable.memberWords W k S) ∧
      Within code h (initialRegisters [.pointer rp, .pointer sp]) (code ids.members)
        [.pointer q] out (membersBudget W S.length k) := by
  simpa [ComponentTable.memberWords] using members_compiled ids code hm hh hr hs

theorem take_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {α : Type*} (R : Heap → Ptr → α → Prop)
    (mono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, R h ptr x → R h' ptr x)
    {W M : ℕ} {h : Heap} (hh : Valid h) {rp xp : Ptr} {xs : List α}
    (hr : WordsAt h rp (rangeWords W M)) (hx : ListRep R h xp xs) (hM : xs.length ≤ M) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (rangeWords W xs.length) ∧
      Within code h (initialRegisters [.pointer rp, .pointer xp, .pointer 0]) (code ids.take)
        [.pointer q] out (takeBudget xs.length) := by
  obtain ⟨-, -, -, htake, hleft, -, -⟩ := hm
  obtain ⟨out, q, he, ho, hq, hw⟩ := RegisterListZip.compiled_const code ids.take ids.left htake
    (fun h p (w : Bits W) => BitsAt h p w) R (fun _ _ (_ : Unit) => True)
    (fun h p (w : Bits W) => BitsAt h p w) (fun he _ _ hb => hb.mono he) mono
    (fun _ _ _ _ => trivial) (fun he _ _ hb => hb.mono he) (fun _ hb => hb.allocated)
    (fun _ a _ => a) 3 (data := ()) hh hr hx trivial
    (fun {h} hv {ap} _ _ _ _ ha _ _ => ⟨h, ap, .refl h, hv, ha, by
      rw [hleft]; exact ret_values (by reg_simp) le_rfl⟩)
  refine ⟨out, q, he, ho, ?_, hw.mono ?_⟩
  · rw [zipWith_left_rangeWords xs hM] at hq
    exact hq
  · simp [takeBudget, Nat.min_eq_right hM]

end WeightedMIS.RegisterWordFilter
