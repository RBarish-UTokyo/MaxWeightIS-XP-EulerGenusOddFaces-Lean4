module

public import WeightedMIS.RegisterFaceColumns
public import WeightedMIS.RegisterEvenMatrix

/-!
# Accumulating and reading off signed columns

The zip combinator applies the stub procedure to the entries of one row and
the current stub lists. The column procedure processes the rows from the last
to the first, pairing each with its row record. The initial stub lists are
one empty list per table record, and each final stub list is turned into its
column cell. The composition refines `(colsW (replicate m []) is rows).map
fromStubs`.
-/

@[expose] public section

namespace WeightedMIS.RegisterFaceColumnStage

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys
open WeightedMIS.RegisterPotentialStep WeightedMIS.SignedWords WeightedMIS.RegisterFaceRow
open WeightedMIS.RegisterRowRecords WeightedMIS.FaceColumnSemantics WeightedMIS.Walks
open WeightedMIS.CompiledTemplates WeightedMIS.ColumnEncoding WeightedMIS.RegisterFaceColumns
open WeightedMIS.RegisterEvenMatrix

variable {p : ℕ}

/-- Stub lists of all columns. -/
def AccsAt (wk R : ℕ) (h : Heap) (ptr : Ptr) (accs : List (List (Stub (Fin R)))) : Prop :=
  ListRep (StubsAt wk R) h ptr accs

theorem AccsAt.mono {wk R : ℕ} {h h' : Heap} (he : Extends h h') {ptr : Ptr}
    {accs : List (List (Stub (Fin R)))} (ha : AccsAt wk R h ptr accs) : AccsAt wk R h' ptr accs :=
  ListRep.mono he (fun _ _ hs => hs.mono he) ha

/-- Row records indexed by finite row numbers. -/
def RecsAt (wk R : ℕ) (h : Heap) (ptr : Ptr) (is : List (Fin R)) : Prop :=
  ListRep (fun h p (i : Fin R) => PairKeysAt wk h p i.val) h ptr is

theorem RecsAt.mono {wk R : ℕ} {h h' : Heap} (he : Extends h h') {ptr : Ptr}
    {is : List (Fin R)} (hr : RecsAt wk R h ptr is) : RecsAt wk R h' ptr is :=
  ListRep.mono he (fun _ _ hp => hp.mono he) hr

/-- Records of `0, ..., R - 1` give the finite row records. -/
theorem recsAt_of_range {wk R : ℕ} {h : Heap} {ptr : Ptr}
    (hr : ListRep (PairKeysAt wk) h ptr (List.range' 0 R)) : RecsAt wk R h ptr (List.finRange R) := by
  obtain ⟨ps, hl, hf⟩ := hr
  refine ⟨ps, hl, ?_⟩
  have he : List.range' 0 R = (List.finRange R).map Fin.val := by
    apply List.ext_getElem <;> simp
  rw [he, List.forall₂_map_right_iff] at hf
  exact hf

/-! ## One row -/

def zipBudget (b m : ℕ) : ℕ := (stubItemBudget b + 45) * m + 23

theorem zip_compiled (code : Code p) (zip item cmp : Fin p)
    (hzip : code zip = RegisterListZip.body zip item) (hitem : code item = stubItemBody cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {wk R b m : ℕ} (one zero : Bits b) (hone : one.value = 1) (hzero : zero.value = 0)
    {h : Heap} (hh : Valid h) {rp ap cp : Ptr} {row : List (Word b)}
    {accs : List (List (Stub (Fin R)))} {i : Fin R}
    (hrow : SignedWords.ListAt h rp row) (hb : ∀ w ∈ row, w.2.value ≤ 2) (hlen : row.length ≤ m)
    (ha : AccsAt wk R h ap accs) (hc : CtxAt (wk := wk) one zero h cp i) :
    ∃ out q, Extends h out ∧ Valid out ∧
      AccsAt wk R out q (List.zipWith (fun w acc => stubsW i w ++ acc) row accs) ∧
      Within code h (initialRegisters [.pointer rp, .pointer ap, .pointer cp]) (code zip)
        [.pointer q] out (zipBudget b m) := by
  obtain ⟨out, q, e, v, hq, w⟩ := RegisterListZip.compiled_const code zip item hzip SignedAt
    (StubsAt wk R) (CtxAt (wk := wk) one zero) (StubsAt wk R) (fun he _ _ hs => hs.mono he)
    (fun he _ _ hs => hs.mono he) (fun he _ _ hc => hc.mono he) (fun he _ _ hs => hs.mono he)
    (fun _ hs => ListRep.allocated hs) (fun i w acc => stubsW i w ++ acc) (stubItemBudget b)
    hh hrow ha hc (fun {_} hv {_ _} {_ _} hmem hw hs hc' =>
      stubItem_compiled code item cmp hitem hcmp one zero hone hzero hv hw
        (hb _ (List.of_mem_zip hmem).1) hs hc')
  refine ⟨out, q, e, v, hq, w.mono ?_⟩
  unfold zipBudget
  have := Nat.mul_le_mul_left (stubItemBudget b + 45) (le_trans (Nat.min_le_left row.length accs.length) hlen)
  omega

/-! ## All rows -/

/-- Arguments 0 = rows, 1 = row records, 2 = initial stub lists, 3 = constants. -/
def colsBody (self zip : Fin p) : Command p :=
  .load (.register 0) 4 5 15 { CompiledTrie.failCases with
    nil := .ret [.register 2]
    cons := .load (.register 1) 6 7 15 { CompiledTrie.failCases with
      cons := .call self [.register 5, .register 7, .register 2, .register 3] [8]
        (.allocate 9 (.pair (.register 6) (.register 3))
          (.call zip [.register 4, .register 8, .register 9] [10] (.ret [.register 10]))) } }

def colsBudget (b m len : ℕ) : ℕ := (zipBudget b m + 47) * len + 13

theorem cols_compiled (code : Code p) (self zip item cmp : Fin p)
    (hself : code self = colsBody self zip)
    (hzip : code zip = RegisterListZip.body zip item) (hitem : code item = stubItemBody cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {wk R b m : ℕ} (one zero : Bits b) (hone : one.value = 1) (hzero : zero.value = 0)
    (init : List (List (Stub (Fin R)))) :
    ∀ (rows : List (List (Word b))) (is : List (Fin R)) {h : Heap}, Valid h →
      ∀ {rp kp ip cp : Ptr}, is.length = rows.length →
      RowsAt h rp rows → RecsAt wk R h kp is → AccsAt wk R h ip init →
      ConstsAt one zero h cp → (∀ row ∈ rows, ∀ w ∈ row, w.2.value ≤ 2) →
      (∀ row ∈ rows, row.length ≤ m) →
      ∃ out q, Extends h out ∧ Valid out ∧ AccsAt wk R out q (colsW init is rows) ∧
        Within code h (initialRegisters [.pointer rp, .pointer kp, .pointer ip, .pointer cp])
          (code self) [.pointer q] out (colsBudget b m rows.length) := by
  intro rows
  induction rows with
  | nil =>
    intro is h hh rp kp ip cp _ hr _ hi _ _ _
    obtain ⟨ps, hl, hf⟩ := hr
    cases hf
    cases hl with
    | nil cell =>
    refine ⟨h, ip, .refl h, hh, by cases is <;> simpa [colsW] using hi, ?_⟩
    rw [hself]
    refine (Within.load (pointer := rp) (c := Cell.nil) (by simp [Atom.eval, initialRegisters]) cell
      (ret_values (by simp [values, Atom.eval, loadRegisters, decoded, initialRegisters])
        le_rfl)).mono ?_
    simp [colsBudget]
  | cons row rows ih =>
    intro is h hh rp kp ip cp hlen hr hk hi hc hb hm
    cases is with
    | nil => simp at hlen
    | cons i is =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    obtain ⟨ps, hl, hf⟩ := hr
    cases hf with
    | @cons rowp _ ps' _ hrow hrows =>
    cases hl with
    | @cons _ _ rest _ cell hrest =>
    obtain ⟨qs, hkl, hkf⟩ := hk
    cases hkf with
    | @cons recp _ qs' _ hrec hrecs =>
    cases hkl with
    | @cons _ _ krest _ kcell hkrest =>
    obtain ⟨m1, q1, e1, v1, a1, w1⟩ := ih is hh hlen ⟨ps', hrest, hrows⟩ ⟨qs', hkrest, hrecs⟩ hi hc
      (fun r hr' => hb r (List.mem_cons_of_mem _ hr')) (fun r hr' => hm r (List.mem_cons_of_mem _ hr'))
    have hcl : cp < m1.length := by
      obtain ⟨_, _, hc', _⟩ := hc.mono e1
      exact (List.getElem?_eq_some_iff.mp hc').1
    obtain ⟨e2, v2, c2⟩ := alloc_pair v1 (hrec.mono e1).allocated hcl
    have hctx : CtxAt (wk := wk) one zero (m1 ++ [.pair recp cp]) m1.length i :=
      ⟨recp, cp, c2, (hrec.mono e1).mono e2, (hc.mono e1).mono e2⟩
    obtain ⟨m3, q3, e3, v3, a3, w3⟩ := zip_compiled code zip item cmp hzip hitem hcmp one zero hone
      hzero v2 ((hrow.mono e1).mono e2) (hb row List.mem_cons_self) (hm row List.mem_cons_self)
      (a1.mono e2) hctx
    refine ⟨m3, q3, e1.trans (e2.trans e3), v3, by simpa [colsW] using a3, ?_⟩
    rw [hself]
    refine (Within.load (pointer := rp) (c := Cell.cons rowp rest)
      (by simp [Atom.eval, initialRegisters]) cell
      (Within.load (pointer := kp) (c := Cell.cons recp krest)
        (by simp [Atom.eval, loadRegisters, decoded, initialRegisters]) kcell
        (call_of (by simp [values, Atom.eval, loadRegisters, decoded, initialRegisters]) w1
          (Within.allocate (c := Cell.pair recp cp)
            (by simp [CellExpr.eval, Atom.eval, bindResults, loadRegisters, decoded,
              initialRegisters, Value.asPointer])
            (call_of (by simp [values, Atom.eval, bindResults, loadRegisters,
              decoded]) w3 (ret_values (by simp [values, Atom.eval, bindResults]) le_rfl)))))).mono ?_
    simp [colsBudget, CellExpr.args]
    ring_nf
    omega

/-! ## Initial lists and column cells -/

def initItemBody : Command p := .ret [.null]

theorem init_compiled (code : Code p) (self item : Fin p)
    (hself : code self = RegisterListMap.body self item) (hitem : code item = initItemBody)
    {wk R W : ℕ} {h : Heap} (hh : Valid h) {tp : Ptr} {T : List (EdgeRec W)}
    (hT : RecordsAt h tp T) :
    ∃ out q, Extends h out ∧ Valid out ∧
      AccsAt wk R out q (List.replicate T.length ([] : List (Stub (Fin R)))) ∧
      Within code h (initialRegisters [.pointer tp, .pointer 0]) (code self) [.pointer q] out
        (38 * T.length + 13) := by
  obtain ⟨out, q, e, v, hq, w⟩ := RegisterListMap.compiled_const code self item hself EdgeRecAt
    (fun _ _ (_ : Unit) => True) (StubsAt wk R) (fun he _ _ hr => hr.mono he)
    (fun _ _ _ _ => trivial) (fun he _ _ hs => hs.mono he) (fun _ hs => ListRep.allocated hs)
    (fun _ _ => ([] : List (Stub (Fin R)))) 3 hh hT (data := ()) trivial
    (fun {h'} hv {_} {_} _ _ _ => ⟨h', 0, .refl h', hv, RegisterListCommon.listRep_null hv, by
      rw [hitem]; exact ret_values (by simp [values, Atom.eval]) (by simp)⟩)
  refine ⟨out, q, e, v, by simpa [AccsAt] using hq, w.mono (by omega)⟩

/-- Argument 0 = stub list; the result is the column cell of its first two stubs. -/
def convItemBody : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := .load (.register 3) 4 5 15 { CompiledTrie.failCases with
      nil := .allocate 6 (.bucket (.register 2)) (.ret [.register 6])
      cons := .allocate 6 (.pair (.register 2) (.register 4)) (.ret [.register 6]) } }

theorem ColumnAt.allocated' {wk R : ℕ} {h : Heap} {ptr : Ptr} {c : Column (Fin R)}
    (hc : ColumnAt (stateKey wk R) h ptr c) : ptr < h.length := by
  cases hc with
  | zero cell => exact (List.getElem?_eq_some_iff.mp cell).1
  | one cell _ => exact (List.getElem?_eq_some_iff.mp cell).1
  | two cell _ _ => exact (List.getElem?_eq_some_iff.mp cell).1

theorem alloc_cell {h : Heap} (hh : Valid h) (c : Cell) (hc : ∀ q ∈ c.references, q < h.length) :
    Extends h (h ++ [c]) ∧ Valid (h ++ [c]) ∧ (h ++ [c])[h.length]? = some c := by
  have safe := safe_allocate h hh c hc
  exact ⟨safe.1, safe.2.1, by simp⟩

theorem convItem_compiled (code : Code p) (self : Fin p) (hself : code self = convItemBody)
    {wk R : ℕ} {h : Heap} (hh : Valid h) {ap dp : Ptr} {l : List (Stub (Fin R))}
    (hl : StubsAt wk R h ap l) :
    ∃ out q, Extends h out ∧ Valid out ∧ ColumnAt (stateKey wk R) out q (fromStubs l) ∧
      Within code h (initialRegisters [.pointer ap, .pointer dp]) (code self) [.pointer q] out 31 := by
  obtain ⟨ps, hlist, hf⟩ := hl
  rw [hself]
  cases hf with
  | nil =>
    cases hlist with
    | nil cell =>
    refine ⟨h, 0, .refl h, hh, .zero hh.1, ?_⟩
    exact (Within.load (pointer := ap) (c := Cell.nil) (by simp [Atom.eval, initialRegisters]) cell
      (ret_values (by simp [values, Atom.eval]) le_rfl)).mono (by simp)
  | @cons sp s ps' l hs hrest =>
    cases hlist with
    | @cons _ _ tail _ cell htail =>
    cases hrest with
    | nil =>
      cases htail with
      | nil tcell =>
      obtain ⟨e1, v1, c1⟩ := alloc_cell hh (.bucket sp) (by
        intro q hq
        simp only [Cell.references, List.mem_singleton] at hq
        exact hq ▸ StubAt.allocated' hs)
      refine ⟨_, h.length, e1, v1, .one c1 (hs.mono e1), ?_⟩
      exact (Within.load (pointer := ap) (c := Cell.cons sp tail)
        (by simp [Atom.eval, initialRegisters]) cell
        (Within.load (pointer := tail) (c := Cell.nil)
          (by simp [Atom.eval, loadRegisters, decoded]) tcell
          (Within.allocate (c := Cell.bucket sp)
            (by simp [CellExpr.eval, Atom.eval, loadRegisters, decoded, Value.asPointer])
            (ret_values (by simp [values, Atom.eval]) le_rfl)))).mono (by simp [CellExpr.args])
    | @cons tp t ps'' l' ht _ =>
      cases htail with
      | @cons _ _ tail2 _ tcell _ =>
      obtain ⟨e1, v1, c1⟩ := alloc_cell hh (.pair sp tp) (by
        intro q hq
        simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact StubAt.allocated' hs
        · exact StubAt.allocated' ht)
      refine ⟨_, h.length, e1, v1, .two c1 (hs.mono e1) (ht.mono e1), ?_⟩
      exact (Within.load (pointer := ap) (c := Cell.cons sp tail)
        (by simp [Atom.eval, initialRegisters]) cell
        (Within.load (pointer := tail) (c := Cell.cons tp tail2)
          (by simp [Atom.eval, loadRegisters, decoded]) tcell
          (Within.allocate (c := Cell.pair sp tp)
            (by simp [CellExpr.eval, Atom.eval, loadRegisters, decoded, Value.asPointer])
            (ret_values (by simp [values, Atom.eval]) le_rfl)))).mono (by simp [CellExpr.args])

end WeightedMIS.RegisterFaceColumnStage
