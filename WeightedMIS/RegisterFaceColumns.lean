module

public import WeightedMIS.FaceColumnSemantics
public import WeightedMIS.RegisterRowRecords
public import WeightedMIS.RegisterFaceRow
public import WeightedMIS.RegisterListZip
public import WeightedMIS.CompiledTemplatePrimitives
public import WeightedMIS.NodeEncoding

/-!
# Signed columns in the compiled template ABI

Every column starts as an empty stub list. Rows are processed from the last to
the first; a row prepends, column by column, the copies of its signed stub,
which is a sign cell pointing to the shared row record. A stored magnitude is
compared with zero and one, and two copies are prepended otherwise, so the
procedure is exact for entries of absolute value at most two. Finally the
first two stubs of each list form the column cell `nil`, `bucket`, or `pair`.
The results refine `colsW` and `fromStubs`.
-/

@[expose] public section

namespace WeightedMIS.RegisterFaceColumns

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys
open WeightedMIS.RegisterPotentialStep WeightedMIS.SignedWords WeightedMIS.RegisterFaceRow
open WeightedMIS.RegisterRowRecords WeightedMIS.FaceColumnSemantics WeightedMIS.Walks
open WeightedMIS.CompiledTemplates WeightedMIS.ColumnEncoding

variable {p : ℕ}

/-! ## State keys -/

/-- Signed state keys: `none ↦ 0`, `(i, false) ↦ 2 i + 1`, `(i, true) ↦ 2 i + 2`. -/
def stateKey (wk R : ℕ) (s : State (Fin R)) : Bits wk := word wk (NodeEncoding.stateEquiv R s).val

theorem stateKey_some (wk R : ℕ) (i : Fin R) (b : Bool) :
    stateKey wk R (some (i, b)) = word wk (2 * i.val + (if b then 1 else 0) + 1) := by
  unfold stateKey
  congr 1
  cases b <;> simp [NodeEncoding.stateEquiv, NodeEncoding.boolEquiv, finProdFinEquiv, Nat.mul_comm,
    Nat.add_comm]

theorem stubAt_alloc {wk R : ℕ} {h : Heap} (hh : Valid h) (sgn : Bool) {rec : Ptr} (i : Fin R)
    (hr : PairKeysAt wk h rec i.val) :
    Extends h (h ++ [.bit sgn rec]) ∧ Valid (h ++ [.bit sgn rec]) ∧
      StubAt (stateKey wk R) (h ++ [.bit sgn rec]) h.length (i, sgn) := by
  have hs := safe_allocate h hh (.bit sgn rec) (by
    intro q hq
    simp only [Cell.references, List.mem_singleton] at hq
    exact hq ▸ hr.allocated)
  have he : Extends h (h ++ [.bit sgn rec]) := hs.1
  obtain ⟨mp, pp, hc, hm, hp⟩ := hr
  refine ⟨he, hs.2.1, rec, mp, pp, ?_, he.lookup hc, ?_, ?_⟩
  · rw [List.getElem?_append_right (Nat.le_refl _)]
    simp
  · rw [stateKey_some]; simpa using hm.mono he
  · rw [stateKey_some]; simpa using hp.mono he

theorem StubAt.allocated' {wk R : ℕ} {h : Heap} {ptr : Ptr} {s : Stub (Fin R)}
    (hs : StubAt (stateKey wk R) h ptr s) : ptr < h.length := by
  obtain ⟨_, _, _, hc, _⟩ := hs
  exact (List.getElem?_eq_some_iff.mp hc).1

/-- A list of stubs. -/
def StubsAt (wk R : ℕ) (h : Heap) (ptr : Ptr) (l : List (Stub (Fin R))) : Prop :=
  ListRep (StubAt (stateKey wk R)) h ptr l

theorem StubsAt.mono {wk R : ℕ} {h h' : Heap} (he : Extends h h') {ptr : Ptr}
    {l : List (Stub (Fin R))} (hs : StubsAt wk R h ptr l) : StubsAt wk R h' ptr l :=
  ListRep.mono he (fun _ _ hs => hs.mono he) hs

theorem stubs_cons {wk R : ℕ} {h : Heap} (hh : Valid h) {a tail : Ptr} {s : Stub (Fin R)}
    {l : List (Stub (Fin R))} (ha : StubAt (stateKey wk R) h a s) (ht : StubsAt wk R h tail l) :
    Extends h (h ++ [.cons a tail]) ∧ Valid (h ++ [.cons a tail]) ∧
      StubsAt wk R (h ++ [.cons a tail]) h.length (s :: l) :=
  RegisterListCommon.allocate_consRep (fun he _ _ hs => hs.mono he) hh ha (StubAt.allocated' ha) ht

/-! ## One entry -/

/-- Row context: `pair rowRecord constants`. -/
def CtxAt {wk R b : ℕ} (one zero : Bits b) (h : Heap) (ptr : Ptr) (i : Fin R) : Prop :=
  ∃ rec cst, h[ptr]? = some (.pair rec cst) ∧ PairKeysAt wk h rec i.val ∧ ConstsAt one zero h cst

theorem CtxAt.mono {wk R b : ℕ} {one zero : Bits b} {h h' : Heap} (he : Extends h h') {ptr : Ptr}
    {i : Fin R} (hc : CtxAt (wk := wk) one zero h ptr i) : CtxAt (wk := wk) one zero h' ptr i := by
  obtain ⟨rec, cst, hp, hr, hk⟩ := hc
  exact ⟨rec, cst, he.lookup hp, hr.mono he, hk.mono he⟩

def moreBody (cmp : Fin p) : Command p :=
  .call cmp [.register 3, .register 8] [10, 11]
    (.allocate 13 (.cons (.register 12) (.register 1))
      (.branch (.register 11) (.ret [.register 13])
        (.allocate 14 (.cons (.register 12) (.register 13)) (.ret [.register 14]))))

/-- Arguments 0 = signed entry, 1 = stub list, 2 = row context; prepends the
copies of the entry's stub. -/
def stubItemBody (cmp : Fin p) : Command p :=
  .load (.register 0) 3 4 5 { CompiledTrie.failCases with
    bit := .load (.register 2) 6 7 15 { CompiledTrie.failCases with
      pair := .load (.register 7) 8 9 15 { CompiledTrie.failCases with
        pair := .call cmp [.register 3, .register 9] [10, 11]
          (.branch (.register 11) (.ret [.register 1])
            (.branch (.register 5)
              (.allocate 12 (.bit (.flag false) (.register 6)) (moreBody cmp))
              (.allocate 12 (.bit (.flag true) (.register 6)) (moreBody cmp)))) } } }

def stubItemBudget (b : ℕ) : ℕ := 72 * b + 140

theorem more_within (code : Code p) (cmp : Fin p)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {wk R b : ℕ} {h : Heap} (hh : Valid h) {regs : Registers} {mp op sp acc : Ptr}
    {mag one : Bits b} {s : Stub (Fin R)} {l : List (Stub (Fin R))}
    (hm : BitsAt h mp mag) (ho : BitsAt h op one) (hone : one.value = 1)
    (h3 : regs 3 = .pointer mp) (h8 : regs 8 = .pointer op) (h12 : regs 12 = .pointer sp)
    (h1 : regs 1 = .pointer acc) (hs : StubAt (stateKey wk R) h sp s) (hl : StubsAt wk R h acc l)
    (hmag : mag.value = 1 ∨ mag.value = 2) :
    ∃ out q, Extends h out ∧ Valid out ∧ StubsAt wk R out q (List.replicate mag.value s ++ l) ∧
      Within code h regs (moreBody cmp) [.pointer q] out (36 * b + 60) := by
  have w1 := RegisterComparator.compiled code cmp hcmp hm ho
  obtain ⟨e1, v1, l1⟩ := stubs_cons hh hs hl
  let r1 := bindResults regs [10, 11] (RegisterComparator.flags (Bits.compare mag one).1)
  have h11 : r1 11 = .flag (decide (mag.value = 1)) := by
    simp [r1, bindResults, RegisterComparator.flags, (Bits.compare_correct mag one).2.1, hone]
  rcases hmag with hv | hv
  · refine ⟨_, _, e1, v1, by simpa [hv] using l1, ?_⟩
    refine (call_of (by simp [values, Atom.eval, h3, h8]) w1
      (Within.allocate (c := Cell.cons sp acc)
        (by simp [CellExpr.eval, Atom.eval, bindResults, h12, h1, Value.asPointer,
          RegisterComparator.flags])
        (Within.branch (b := true) (by simp [Atom.eval, bindResults, RegisterComparator.flags,
          (Bits.compare_correct mag one).2.1, hone, hv])
          (ret_values (by simp [values, Atom.eval]) le_rfl)))).mono ?_
    simp [CellExpr.args]
    omega
  · obtain ⟨e2, v2, l2⟩ := stubs_cons v1 (hs.mono e1) l1
    refine ⟨_, _, e1.trans e2, v2, by simpa [hv] using l2, ?_⟩
    refine (call_of (by simp [values, Atom.eval, h3, h8]) w1
      (Within.allocate (c := Cell.cons sp acc)
        (by simp [CellExpr.eval, Atom.eval, bindResults, h12, h1, Value.asPointer,
          RegisterComparator.flags])
        (Within.branch (b := false) (by simp [Atom.eval, bindResults, RegisterComparator.flags,
          (Bits.compare_correct mag one).2.1, hone, hv])
          (Within.allocate (c := Cell.cons sp h.length)
            (by simp [CellExpr.eval, Atom.eval, bindResults, h12, Value.asPointer,
              RegisterComparator.flags])
            (ret_values (by simp [values, Atom.eval]) le_rfl))))).mono ?_
    simp [CellExpr.args]
    omega

theorem stubItem_compiled (code : Code p) (self cmp : Fin p) (hself : code self = stubItemBody cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {wk R b : ℕ} (one zero : Bits b) (hone : one.value = 1) (hzero : zero.value = 0)
    {h : Heap} (hh : Valid h) {wp acc cp : Ptr} {w : Word b} {l : List (Stub (Fin R))} {i : Fin R}
    (hw : SignedAt h wp w) (hb : w.2.value ≤ 2) (hl : StubsAt wk R h acc l)
    (hc : CtxAt (wk := wk) one zero h cp i) :
    ∃ out q, Extends h out ∧ Valid out ∧ StubsAt wk R out q (stubsW i w ++ l) ∧
      Within code h (initialRegisters [.pointer wp, .pointer acc, .pointer cp]) (code self)
        [.pointer q] out (stubItemBudget b) := by
  rcases w with ⟨s, mag⟩
  obtain ⟨mp, hwc, hm⟩ := hw
  obtain ⟨rec, cst, hcc, hr, op, zp, hcst, ho, hz⟩ := hc
  have w1 := RegisterComparator.compiled code cmp hcmp hm hz
  let regs := initialRegisters [Value.pointer wp, .pointer acc, .pointer cp]
  let r1 := loadRegisters regs 3 4 5 (.bit s mp)
  let r2 := loadRegisters r1 6 7 15 (.pair rec cst)
  let r3 := loadRegisters r2 8 9 15 (.pair op zp)
  let r4 := bindResults r3 [10, 11] (RegisterComparator.flags (Bits.compare mag zero).1)
  have h11 : r4 11 = .flag (decide (mag.value = 0)) := by
    simp [r4, bindResults, RegisterComparator.flags, (Bits.compare_correct mag zero).2.1, hzero]
  have h5 : r4 5 = .flag s := by
    simp [r4, r3, r2, r1, bindResults, loadRegisters, decoded, RegisterComparator.flags]
  have pre : ∀ {out : Heap} {q : Ptr} {B : ℕ},
      Within code h r4
        (.branch (.register 11) (.ret [.register 1])
          (.branch (.register 5)
            (.allocate 12 (.bit (.flag false) (.register 6)) (moreBody cmp))
            (.allocate 12 (.bit (.flag true) (.register 6)) (moreBody cmp)))) [.pointer q] out B →
      B ≤ 36 * b + 77 →
      Within code h regs (stubItemBody cmp) [.pointer q] out (stubItemBudget b) := by
    intro out q B hB hle
    refine (Within.load (pointer := wp) (c := Cell.bit s mp) (by simp [Atom.eval, regs,
      initialRegisters]) hwc
      (Within.load (pointer := cp) (c := Cell.pair rec cst)
        (by simp [Atom.eval, regs, loadRegisters, decoded, initialRegisters]) hcc
        (Within.load (pointer := cst) (c := Cell.pair op zp)
          (by simp [Atom.eval, loadRegisters, decoded]) hcst
          (call_of (by simp [values, Atom.eval, r3, r2, r1, regs, loadRegisters,
            decoded]) w1 hB)))).mono ?_
    simp [stubItemBudget]
    omega
  rw [hself]
  by_cases h0 : mag.value = 0
  · refine ⟨h, acc, .refl h, hh, by simpa [stubsW, h0] using hl, pre ?_ (le_refl _)⟩
    refine (Within.branch (b := true) (by simp [Atom.eval, h11, h0])
      (ret_values (by simp [values, Atom.eval, r4, r3, r2, r1, regs, bindResults, loadRegisters,
        decoded, initialRegisters, RegisterComparator.flags]) le_rfl)).mono ?_
    simp
  · have hmag : mag.value = 1 ∨ mag.value = 2 := by simp at hb; omega
    obtain ⟨e1, v1, s1⟩ := stubAt_alloc hh (!s) i hr
    have hrest := more_within code cmp hcmp v1 (regs := Function.update r4 12 (.pointer h.length))
      (hm.mono e1) (ho.mono e1) hone
      (by simp [r4, r3, r2, r1, bindResults, loadRegisters, decoded, RegisterComparator.flags])
      (by simp [r4, r3, bindResults, loadRegisters, decoded, RegisterComparator.flags])
      (by simp) (by simp [r4, r3, r2, r1, regs, bindResults, loadRegisters, decoded, initialRegisters,
        RegisterComparator.flags]) s1 (hl.mono e1) hmag
    obtain ⟨out, q, e2, v2, l2, w2⟩ := hrest
    refine ⟨out, q, e1.trans e2, v2, by simpa [stubsW] using l2, pre ?_ (le_refl _)⟩
    cases s
    · refine (Within.branch (b := false) (by simp [Atom.eval, h11, h0])
        (Within.branch (b := false) (by simp [Atom.eval, h5])
          (Within.allocate (c := Cell.bit true rec)
            (by simp [CellExpr.eval, Atom.eval, r4, r3, r2, bindResults, loadRegisters, decoded,
              RegisterComparator.flags, Value.asFlag, Value.asPointer]) w2))).mono ?_
      simp [CellExpr.args]
      omega
    · refine (Within.branch (b := false) (by simp [Atom.eval, h11, h0])
        (Within.branch (b := true) (by simp [Atom.eval, h5])
          (Within.allocate (c := Cell.bit false rec)
            (by simp [CellExpr.eval, Atom.eval, r4, r3, r2, bindResults, loadRegisters, decoded,
              RegisterComparator.flags, Value.asFlag, Value.asPointer]) w2))).mono ?_
      simp [CellExpr.args]
      omega

end WeightedMIS.RegisterFaceColumns
