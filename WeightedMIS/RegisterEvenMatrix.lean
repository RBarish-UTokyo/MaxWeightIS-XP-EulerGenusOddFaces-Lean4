module

public import WeightedMIS.RegisterFaceRow

/-!
# The stored even-face matrix as signed word rows

The rows procedure maps the row procedure over a stored list of key cycles,
pairing each cycle with the shared constants. For the even facial key cycles
of a stored ribbon the resulting signed rows denote `storedEvenMatrix`.
-/

@[expose] public section

namespace WeightedMIS.RegisterEvenMatrix

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.RibbonTable
open WeightedMIS.RegisterFlagKeys WeightedMIS.FaceRowSemantics WeightedMIS.RegisterFaceRow
open WeightedMIS.RegisterPotentialStep WeightedMIS.SignedWords WeightedMIS.RegisterKeyFaceEnumeration

variable {p : ℕ}

/-- Data of the rows: `pair table constants`. -/
def RowsDataAt {W b : ℕ} (one zero : Bits b) (h : Heap) (ptr : Ptr) (T : List (EdgeRec W)) : Prop :=
  ∃ tp kp, h[ptr]? = some (.pair tp kp) ∧ RecordsAt h tp T ∧ ConstsAt one zero h kp

theorem RowsDataAt.mono {W b : ℕ} {one zero : Bits b} {h h' : Heap} (he : Extends h h')
    {ptr : Ptr} {T : List (EdgeRec W)} (hd : RowsDataAt one zero h ptr T) :
    RowsDataAt one zero h' ptr T := by
  obtain ⟨tp, kp, hp, hT, hk⟩ := hd
  exact ⟨tp, kp, he.lookup hp, hT.mono he, hk.mono he⟩

/-- A list of signed rows. -/
def RowsAt {b : ℕ} (h : Heap) (ptr : Ptr) (rows : List (List (Word b))) : Prop :=
  ListRep (fun h p row => SignedWords.ListAt h p row) h ptr rows

theorem RowsAt.mono {b : ℕ} {h h' : Heap} (he : Extends h h') {ptr : Ptr}
    {rows : List (List (Word b))} (hr : RowsAt h ptr rows) : RowsAt h' ptr rows :=
  ListRep.mono he (fun _ _ hl => hl.mono he) hr

/-- Arguments 0 = cycle, 1 = rows data; the result is the row of the cycle. -/
def rowsItemBody (row : Fin p) : Command p :=
  .load (.register 1) 2 3 15 { CompiledTrie.failCases with
    pair := .allocate 4 (.pair (.register 0) (.register 3))
      (.call row [.register 2, .register 4] [5] (.ret [.register 5])) }

/-- Procedure identifiers of the rows stage. -/
structure Procedures (p : ℕ) where
  rows : Fin p
  rowsItem : Fin p
  row : Fin p
  rowItem : Fin p
  entry : Fin p
  edge : Fin p
  ar : Arith p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.rows = RegisterListMap.body ids.rows ids.rowsItem ∧
  code ids.rowsItem = rowsItemBody ids.row ∧
  code ids.row = RegisterListMap.body ids.row ids.rowItem ∧
  code ids.rowItem = rowItemBody ids.entry ∧
  code ids.entry = entryBody ids.entry ids.edge ids.ar.cmp ids.ar.sadd ∧
  code ids.edge = edgePartBody ∧
  ids.ar.Matches code

def rowsBudget (W b L m len : ℕ) : ℕ := (rowBudget W b L m + 66) * len + 13

theorem rowsItem_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W b : ℕ} (one zero : Bits b) {h : Heap} (hh : Valid h) {cp dp : Ptr}
    {c : List (Bits (W + 2))} {T : List (EdgeRec W)} (L : ℕ) (hL : c.length ≤ L)
    (hc : WordsAt h cp c) (hd : RowsDataAt one zero h dp T) :
    ∃ out q, Extends h out ∧ Valid out ∧ SignedWords.ListAt out q (rowW one zero T c) ∧
      Within code h (initialRegisters [.pointer cp, .pointer dp]) (code ids.rowsItem)
        [.pointer q] out (rowBudget W b L T.length + 26) := by
  obtain ⟨hrows, hitem, hrow, hrowItem, hentry, hedge, har⟩ := hm
  obtain ⟨tp, kp, hdp, hT, hk⟩ := hd
  have hkl : kp < h.length := by
    obtain ⟨_, _, hc', _⟩ := hk
    exact (List.getElem?_eq_some_iff.mp hc').1
  obtain ⟨e1, v1, c1⟩ := alloc_pair hh hc.allocated hkl
  have hrd : RowDataAt one zero (h ++ [.pair cp kp]) h.length c :=
    ⟨cp, kp, c1, hc.mono e1, hk.mono e1⟩
  obtain ⟨out, q, e2, v2, s2, w2⟩ := row_compiled code ids.row ids.rowItem ids.entry ids.edge ids.ar
    hrow hrowItem hentry hedge har one zero v1 (hT.mono e1) hrd
  refine ⟨out, q, e1.trans e2, v2, s2, ?_⟩
  rw [hitem]
  refine (Within.load (pointer := dp) (c := Cell.pair tp kp) (by simp [Atom.eval, initialRegisters])
    hdp (Within.allocate (c := Cell.pair cp kp)
      (by simp [CellExpr.eval, Atom.eval, loadRegisters, decoded, initialRegisters, Value.asPointer])
      (call_of (by simp [values, Atom.eval, loadRegisters, decoded]) w2
        (ret_values (by simp [values, Atom.eval, bindResults]) le_rfl)))).mono ?_
  have hmono : rowBudget W b c.length T.length ≤ rowBudget W b L T.length := by
    unfold rowBudget entryBudget
    have := Nat.mul_le_mul_left (36 * W + 180 * b + 250) hL
    have := Nat.mul_le_mul_right T.length (show (36 * W + 180 * b + 250) * c.length + 31 + 65 ≤
      (36 * W + 180 * b + 250) * L + 31 + 65 by omega)
    omega
  simp [CellExpr.args]
  omega

theorem rows_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W b : ℕ} (one zero : Bits b) {h : Heap} (hh : Valid h) {sp dp : Ptr}
    {cs : List (List (Bits (W + 2)))} {T : List (EdgeRec W)} (L : ℕ)
    (hL : ∀ c ∈ cs, c.length ≤ L) (hc : CyclesAt h sp cs) (hd : RowsDataAt one zero h dp T) :
    ∃ out q, Extends h out ∧ Valid out ∧ RowsAt out q (rowsW one zero T cs) ∧
      Within code h (initialRegisters [.pointer sp, .pointer dp]) (code ids.rows) [.pointer q] out
        (rowsBudget W b L T.length cs.length) := by
  obtain ⟨out, q, e, v, hq, w⟩ := RegisterListMap.compiled_const code ids.rows ids.rowsItem hm.1
    (fun h p (c : List (Bits (W + 2))) => WordsAt h p c) (RowsDataAt one zero)
    (fun h p row => SignedWords.ListAt h p row) (fun he _ _ hw => hw.mono he)
    (fun he _ _ hd => hd.mono he) (fun he _ _ hl => hl.mono he) (fun _ hl => hl.allocated)
    (fun T c => rowW one zero T c) (rowBudget W b L T.length + 26) hh hc hd
    (fun {_} hv {_} {_} hmem hw hd' => rowsItem_compiled ids code hm one zero hv L (hL _ hmem) hw hd')
  exact ⟨out, q, e, v, hq, w.mono (by simp only [rowsBudget]; exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _)⟩

/-- For the even facial key cycles of a stored ribbon the signed rows denote
the stored even-face matrix. -/
theorem rows_denote {W b n m : ℕ} {left right : Fin m → Fin n} (R : EmbeddingFaces.Ribbon left right)
    (hm : m < 2 ^ W) (hb : 4 * m < 2 ^ b) (one zero : Bits b) (hone : one.value = 1)
    (hzero : zero.value = 0) :
    List.Forall₂ (List.Forall₂ (fun w z => value w = z))
      (rowsW one zero (encodeRibbon W R)
        ((FlagKeyFaces.evenRoots R (EmbeddingFaces.Flag.canonicalOrder m)).map
          (fun x => (FiniteCycleEnumeration.cycleList R.rotation x).map (flagKey W))))
      R.storedEvenMatrix :=
  rowsW_encode hm hb one zero hone hzero R

end WeightedMIS.RegisterEvenMatrix
