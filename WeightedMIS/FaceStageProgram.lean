module

public import WeightedMIS.RegisterRibbonCycles
public import WeightedMIS.RegisterFaceColumnStage

/-!
# The face stage of the hard solver

From a stored ribbon table the stage computes, with fixed register code,

* the signed columns `R.computedColumn (Flag.canonicalOrder m)` of every
  original edge, in the column ABI of `CompiledTemplates` with state keys
  `stateKey wk r`, where `r` is the number of even faces;
* the integer rows of `R.storedEvenMatrix` as lists of signed words;
* the word `2 r + 1` of the key width, the number of signed states.

The event bound is an explicit polynomial in the table width `W`, the entry
width `b`, the key width `wk`, and the number of edges `m`.
-/

@[expose] public section

namespace WeightedMIS.FaceStageProgram

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys
open WeightedMIS.RegisterPotentialStep WeightedMIS.SignedWords WeightedMIS.RegisterFaceRow
open WeightedMIS.RegisterRowRecords WeightedMIS.FaceColumnSemantics WeightedMIS.Walks
open WeightedMIS.CompiledTemplates WeightedMIS.RegisterFaceColumns WeightedMIS.RegisterEvenMatrix
open WeightedMIS.RegisterFaceColumnStage WeightedMIS.RegisterRibbonCycles WeightedMIS.FlagKeyFaces
open WeightedMIS.RegisterKeyFaceEnumeration WeightedMIS.EmbeddingFaces WeightedMIS.FaceRowSemantics
open WeightedMIS.FiniteCycleEnumeration WeightedMIS.ColumnEncoding WeightedMIS.RegisterKeyTrace

variable {p : ℕ}

theorem conv_compiled (code : Code p) (self item : Fin p)
    (hself : code self = RegisterListMap.body self item) (hitem : code item = convItemBody)
    {wk R : ℕ} {h : Heap} (hh : Valid h) {ap : Ptr} {accs : List (List (Stub (Fin R)))}
    (ha : AccsAt wk R h ap accs) :
    ∃ out q, Extends h out ∧ Valid out ∧
      ListRep (ColumnAt (stateKey wk R)) out q (accs.map fromStubs) ∧
      Within code h (initialRegisters [.pointer ap, .pointer 0]) (code self) [.pointer q] out
        (66 * accs.length + 13) := by
  obtain ⟨out, q, e, v, hq, w⟩ := RegisterListMap.compiled_const code self item hself
    (StubsAt wk R) (fun _ _ (_ : Unit) => True) (ColumnAt (stateKey wk R))
    (fun he _ _ hs => hs.mono he) (fun _ _ _ _ => trivial) (fun he _ _ hc => hc.mono he)
    (fun _ hc => ColumnAt.allocated' hc) (fun _ l => fromStubs l) 31 hh ha (data := ()) trivial
    (fun {_} hv {_} {_} _ hl _ => convItem_compiled code item hitem hv hl)
  exact ⟨out, q, e, v, hq, w.mono (by omega)⟩

/-- Arguments 0 = table, 1 = entry constants, 2 = the key-width word one.
Results: the columns, the signed rows, and the counter `2 r + 1`. -/
def stageBody (cycles rows records init cols conv : Fin p) : Command p :=
  .call cycles [.register 0] [3]
    (.allocate 4 (.pair (.register 0) (.register 1))
      (.call rows [.register 3, .register 4] [5]
        (.call records [.register 5, .register 2, .register 2] [6, 7]
          (.call init [.register 0, .null] [8]
            (.call cols [.register 5, .register 6, .register 8, .register 1] [9]
              (.call conv [.register 9, .null] [10]
                (.ret [.register 10, .register 5, .register 7])))))))

structure Procedures (p : ℕ) where
  top : Fin p
  cyc : RegisterRibbonCycles.Procedures p
  rowsIds : RegisterEvenMatrix.Procedures p
  records : Fin p
  init : Fin p
  initItem : Fin p
  cols : Fin p
  zip : Fin p
  stubItem : Fin p
  conv : Fin p
  convItem : Fin p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.top = stageBody ids.cyc.top ids.rowsIds.rows ids.records ids.init ids.cols ids.conv ∧
  ids.cyc.Matches code ∧ ids.rowsIds.Matches code ∧
  code ids.records = recordsBody ids.records ids.rowsIds.ar.add ∧
  code ids.init = RegisterListMap.body ids.init ids.initItem ∧
  code ids.initItem = initItemBody ∧
  code ids.cols = colsBody ids.cols ids.zip ∧
  code ids.zip = RegisterListZip.body ids.zip ids.stubItem ∧
  code ids.stubItem = stubItemBody ids.rowsIds.ar.cmp ∧
  code ids.conv = RegisterListMap.body ids.conv ids.convItem ∧
  code ids.convItem = convItemBody

/-- Explicit event bound of the face stage. -/
def stageBudget (W b wk m : ℕ) : ℕ :=
  cyclesBudget W m + rowsBudget W b (4 * m) m (4 * m) + recordsBudget wk (4 * m) +
    (38 * m + 13) + colsBudget b m (4 * m) + (66 * m + 13) + 60

/-- A closed polynomial bound: degree three in the number of edges and linear
in the widths. -/
theorem stageBudget_le (W b wk m : ℕ) :
    stageBudget W b wk m ≤ 2 ^ 20 * (W + b + wk + 1) * (m + 1) ^ 3 := by
  simp only [stageBudget, cyclesBudget, keysBudget, scanBudget, cycleBudget, loopBudget, rotBudget,
    RegisterRecordLookup.cornerBudget, RegisterRecordLookup.findBudget, rowsBudget, rowBudget,
    entryBudget, recordsBudget, colsBudget, zipBudget, stubItemBudget]
  ring_nf
  nlinarith [Nat.zero_le W, Nat.zero_le b, Nat.zero_le wk, Nat.zero_le m, Nat.zero_le (W * m),
    Nat.zero_le (W * m * m), Nat.zero_le (W * m * m * m), Nat.zero_le (b * m * m * m),
    Nat.zero_le (m * m * m), Nat.zero_le (b * m * m), Nat.zero_le (wk * m), Nat.zero_le (m * m),
    Nat.zero_le (b * m)]

theorem cycle_length_le {n m W : ℕ} {left right : Fin m → Fin n} (R : Ribbon left right)
    (c : List (Bits (W + 2)))
    (hc : c ∈ (evenRoots R (Flag.canonicalOrder m)).map
      (fun x => (cycleList R.rotation x).map (flagKey W))) : c.length ≤ 4 * m := by
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hc
  rw [List.length_map, cycleList_length]
  have h := Function.minimalPeriod_le_card (f := R.rotation) (x := x)
  simpa [Flag.card] using h

/-- The face stage computes the even-face columns, the stored even rows, and
the number of signed states of a stored ribbon. -/
theorem stage_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W b wk n m : ℕ} {left right : Fin m → Fin n} (R : Ribbon left right)
    (hW : m < 2 ^ W) (hb : 4 * m < 2 ^ b) (hwk : 8 * m + 1 < 2 ^ wk)
    (one zero : Bits b) (hone : one.value = 1) (hzero : zero.value = 0)
    {h : Heap} (hh : Valid h) {tp cp op : Ptr} (hT : RecordsAt h tp (encodeRibbon W R))
    (hc : ConstsAt one zero h cp) (ho : BitsAt h op (word wk 1)) :
    ∃ out colsPtr rowsPtr cntPtr, ∃ ws : List (List (Word b)), Extends h out ∧ Valid out ∧
      ListRep (ColumnAt (stateKey wk (R.evenRootIndices (Flag.canonicalOrder m)).length)) out colsPtr
        ((List.finRange m).map (R.computedColumn (Flag.canonicalOrder m))) ∧
      RowsAt out rowsPtr ws ∧
      List.Forall₂ (List.Forall₂ (fun w z => value w = z)) ws R.storedEvenMatrix ∧
      BitsAt out cntPtr (word wk (2 * (R.evenRootIndices (Flag.canonicalOrder m)).length + 1)) ∧
      Within code h (initialRegisters [.pointer tp, .pointer cp, .pointer op]) (code ids.top)
        [.pointer colsPtr, .pointer rowsPtr, .pointer cntPtr] out (stageBudget W b wk m) := by
  obtain ⟨htop, hcyc, hrows, hrec, hinit, hinitItem, hcols, hzip, hstub, hconv, hconvItem⟩ := hm
  have hcmp := hrows.2.2.2.2.2.2.2.2.1
  set r := (R.evenRootIndices (Flag.canonicalOrder m)).length with hrdef
  have hr4 : r ≤ 4 * m := by
    have := R.evenRow_count_le (Flag.canonicalOrder m)
    simpa using this
  set cs := (evenRoots R (Flag.canonicalOrder m)).map
    (fun x => (cycleList R.rotation x).map (flagKey W)) with hcs
  have hcsl : cs.length = r := by rw [hcs, List.length_map, hrdef, evenRow_count]
  -- cycles
  obtain ⟨m1, q1, e1, v1, c1, w1⟩ := cycles_compiled ids.cyc code hcyc R hW hh hT
  -- row data
  have hcl : cp < m1.length := by
    obtain ⟨_, _, hc', _⟩ := hc.mono e1
    exact (List.getElem?_eq_some_iff.mp hc').1
  obtain ⟨e2, v2, c2⟩ := alloc_pair v1 (hT.mono e1).allocated hcl
  have hdata : RowsDataAt one zero (m1 ++ [.pair tp cp]) m1.length (encodeRibbon W R) :=
    ⟨tp, cp, c2, (hT.mono e1).mono e2, (hc.mono e1).mono e2⟩
  -- rows
  obtain ⟨m3, q3, e3, v3, r3, w3⟩ := rows_compiled ids.rowsIds code hrows one zero v2 (4 * m)
    (fun c hc' => cycle_length_le R c hc') (c1.mono e2) hdata
  set ws := rowsW one zero (encodeRibbon W R) cs with hws
  have hwsl : ws.length = r := by rw [hws, rowsW, List.length_map, hcsl]
  have hden : List.Forall₂ (List.Forall₂ (fun w z => value w = z)) ws R.storedEvenMatrix :=
    rows_denote R hW hb one zero hone hzero
  -- records
  have hone' : (word wk 1).value = 1 := word_value (by omega)
  obtain ⟨m4, q4, f4, e4, v4, k4, b4, w4⟩ := records_compiled code ids.records ids.rowsIds.ar.add hrec
    hrows.2.2.2.2.2.2.2.1 (fun h p row => SignedWords.ListAt h p row) (fun he _ _ hl => hl.mono he)
    (word wk 1) hone' ws 0 v3 r3 (((ho.mono e1).mono e2).mono e3)
    (((ho.mono e1).mono e2).mono e3) (by rw [hwsl]; omega)
  rw [hwsl] at k4 b4
  rw [Nat.zero_add] at b4
  have hrecs : RecsAt wk r m4 q4 (List.finRange r) := recsAt_of_range k4
  -- initial stub lists
  obtain ⟨m5, q5, e5, v5, a5, w5⟩ := init_compiled (wk := wk) (R := r) code ids.init ids.initItem
    hinit hinitItem v4 ((((hT.mono e1).mono e2).mono e3).mono e4)
  rw [encodeRibbon_length] at a5
  -- columns
  have hbound : ∀ row ∈ ws, ∀ w ∈ row, w.2.value ≤ 2 :=
    forall₂_bound ws _ hden (storedEvenMatrix_bound R)
  have hrowlen : ∀ row ∈ ws, row.length ≤ m := by
    intro row hrow
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hrow
    simp [rowW]
  obtain ⟨m6, q6, e6, v6, a6, w6⟩ := cols_compiled code ids.cols ids.zip ids.stubItem
    ids.rowsIds.ar.cmp hcols hzip hstub hcmp one zero hone hzero (List.replicate m []) ws
    (List.finRange r) v5 (by simp [hwsl]) ((r3.mono e4).mono e5) (hrecs.mono e5) a5
    (((((hc.mono e1).mono e2).mono e3).mono e4).mono e5) hbound hrowlen
  obtain ⟨m7, q7, e7, v7, l7, w7⟩ := conv_compiled code ids.conv ids.convItem hconv hconvItem v6 a6
  rw [colsW_columns R ws hden] at l7
  refine ⟨m7, q7, q3, f4, ws, e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7))))), v7,
    l7, ((((r3.mono e4).mono e5).mono e6).mono e7), hden,
    (((b4.mono e5).mono e6).mono e7), ?_⟩
  rw [htop]
  refine (call_of (by simp [values, Atom.eval, initialRegisters]) w1
    (Within.allocate (c := Cell.pair tp cp)
      (by simp [CellExpr.eval, Atom.eval, bindResults, initialRegisters, Value.asPointer])
      (call_of (by simp [values, Atom.eval, bindResults]) w3
        (call_of (by simp [values, Atom.eval, bindResults, initialRegisters]) w4
          (call_of (by simp [values, Atom.eval, bindResults, initialRegisters]) w5
            (call_of (by simp [values, Atom.eval, bindResults, initialRegisters]) w6
              (call_of (by simp [values, Atom.eval, bindResults]) w7
                (ret_values (by simp [values, Atom.eval, bindResults]) le_rfl)))))))).mono ?_
  -- budget
  have hrows' : rowsBudget W b (4 * m) (encodeRibbon W R).length cs.length ≤
      rowsBudget W b (4 * m) m (4 * m) := by
    rw [encodeRibbon_length, hcsl]
    unfold rowsBudget
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hr4) _
  have hrecB : recordsBudget wk ws.length ≤ recordsBudget wk (4 * m) := by
    rw [hwsl]; unfold recordsBudget; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hr4) _
  have hcolB : colsBudget b m ws.length ≤ colsBudget b m (4 * m) := by
    rw [hwsl]; unfold colsBudget; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hr4) _
  have hconvB : 66 * (colsW (List.replicate m []) (List.finRange r) ws).length + 13 ≤ 66 * m + 13 := by
    have hl := congrArg List.length (colsW_columns R ws hden)
    simp only [List.length_map, List.length_finRange] at hl
    rw [hl]
  rw [encodeRibbon_length] at hrows'
  simp only [stageBudget, CellExpr.args, List.length_cons, List.length_nil, encodeRibbon_length]
  rw [← hcs]
  omega

end WeightedMIS.FaceStageProgram
