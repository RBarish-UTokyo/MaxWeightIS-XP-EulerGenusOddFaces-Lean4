module

public import WeightedMIS.RegisterEliminateRows
public import WeightedMIS.GraphReachEncoded
public import WeightedMIS.RegisterComparator

/-!
# Compiled incidence equations and coordinate vectors

Inputs are the vertex words `word W v` in vertex order, the edge list of
endpoint-word pairs `.pair leftWord rightWord`, and three shared stored
rationals denoting `0`, `1` and `2`. For each vertex word, an inner map over
the edges compares the vertex with both endpoints using the compiled binary
comparator and selects the shared record `0`, `1` or `2`; the resulting rows
are the unsigned incidence equations. A second recursive procedure builds the
`m` coordinate vectors of length `m` with shared suffixes, using the edge list
only as its length witness. Both outputs are exact word lists.
-/

@[expose] public section

namespace WeightedMIS.RegisterIncidenceRows

open PointerMemory RegisterMachine EfficientSearch EfficientSearch.Pointer StoredRational
open RegisterRationalRow (RowAt)
open RegisterRationalCut (RowsAt)

variable {p N W : ℕ}

/-! ## Representations and reference functions -/

abbrev Consts (N : ℕ) := BinaryRational.Word N × BinaryRational.Word N × BinaryRational.Word N

/-- An edge record `.pair leftWord rightWord`. -/
def EdgeAt (h : Heap) (ptr : Ptr) (e : Bits W × Bits W) : Prop :=
  ∃ lp rp, h[ptr]? = some (.pair lp rp) ∧ BitsAt h lp e.1 ∧ BitsAt h rp e.2

theorem EdgeAt.mono {h out : Heap} (ext : Extends h out) {ptr : Ptr} {e : Bits W × Bits W}
    (he : EdgeAt h ptr e) : EdgeAt out ptr e := by
  obtain ⟨lp, rp, cell, hl, hr⟩ := he
  exact ⟨lp, rp, ext.lookup cell, hl.mono ext, hr.mono ext⟩

/-- The constants record `.pair zero (.pair one two)`. -/
def ConstsAt (h : Heap) (ptr : Ptr) (k : Consts N) : Prop :=
  ∃ zp r op tp, h[ptr]? = some (.pair zp r) ∧ h[r]? = some (.pair op tp) ∧
    At h zp k.1 ∧ At h op k.2.1 ∧ At h tp k.2.2

theorem ConstsAt.mono {h out : Heap} (ext : Extends h out) {ptr : Ptr} {k : Consts N}
    (hk : ConstsAt h ptr k) : ConstsAt out ptr k := by
  obtain ⟨zp, r, op, tp, c1, c2, hz, ho, ht⟩ := hk
  exact ⟨zp, r, op, tp, ext.lookup c1, ext.lookup c2, hz.mono ext, ho.mono ext, ht.mono ext⟩

/-- Entry data `.pair vertexWord consts`. -/
def EntryDataAt (h : Heap) (ptr : Ptr) (d : Bits W × Consts N) : Prop :=
  ∃ vp cp, h[ptr]? = some (.pair vp cp) ∧ BitsAt h vp d.1 ∧ ConstsAt h cp d.2

theorem EntryDataAt.mono {h out : Heap} (ext : Extends h out) {ptr : Ptr}
    {d : Bits W × Consts N} (hd : EntryDataAt h ptr d) : EntryDataAt out ptr d := by
  obtain ⟨vp, cp, cell, hv, hc⟩ := hd
  exact ⟨vp, cp, ext.lookup cell, hv.mono ext, hc.mono ext⟩

/-- Row data `.pair edgeList consts`. -/
def RowDataAt (h : Heap) (ptr : Ptr) (d : List (Bits W × Bits W) × Consts N) : Prop :=
  ∃ ep cp, h[ptr]? = some (.pair ep cp) ∧ ListRep EdgeAt h ep d.1 ∧ ConstsAt h cp d.2

theorem RowDataAt.mono {h out : Heap} (ext : Extends h out) {ptr : Ptr}
    {d : List (Bits W × Bits W) × Consts N} (hd : RowDataAt h ptr d) : RowDataAt out ptr d := by
  obtain ⟨ep, cp, cell, he, hc⟩ := hd
  exact ⟨ep, cp, ext.lookup cell, he.mono ext (fun _ _ h => h.mono ext), hc.mono ext⟩

/-- Word equality as decided by the binary comparator. -/
def eqb (a b : Bits W) : Bool := decide ((Bits.compare a b).1 = .eq)

/-- The selected incidence coefficient of vertex word `vw` on edge `e`. -/
def entryW (k : Consts N) (vw : Bits W) (e : Bits W × Bits W) : BinaryRational.Word N :=
  if eqb vw e.1 then (if eqb vw e.2 then k.2.2 else k.2.1) else (if eqb vw e.2 then k.2.1 else k.1)

/-- One incidence row per vertex word. -/
def incidenceRowsW (k : Consts N) (verts : List (Bits W)) (edges : List (Bits W × Bits W)) :
    List (List (BinaryRational.Word N)) :=
  verts.map fun vw => edges.map (entryW k vw)

theorem eqb_word {n : ℕ} (hn : n < 2 ^ W) (v w : Fin n) :
    eqb (GraphReachEncoded.word W v.val) (GraphReachEncoded.word W w.val) = decide (v = w) := by
  have hv : v.val < 2 ^ W := by omega
  have hw : w.val < 2 ^ W := by omega
  unfold eqb
  rw [decide_eq_decide, (Bits.compare_correct _ _).2.1, GraphReachEncoded.word_value hv,
    GraphReachEncoded.word_value hw, Fin.val_inj]

/-- The incidence word rows denote the unsigned incidence equations. -/
theorem incidenceRowsW_correct {n m : ℕ} (left right : Fin m → Fin n) (hn : n < 2 ^ W)
    (k : Consts N) (hz : RationalWordRows.Rep k.1 0) (ho : RationalWordRows.Rep k.2.1 1)
    (ht : RationalWordRows.Rep k.2.2 2) :
    List.Forall₂ RationalWordRows.RowRep
      (incidenceRowsW k (GraphReachEncoded.rangeWords W n)
        (GraphReachEncoded.edgeWords W left right))
      (List.ofFn fun v e => Incidence.unsigned left right e v) := by
  unfold incidenceRowsW GraphReachEncoded.rangeWords
  rw [List.ofFn_eq_map, List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff,
    List.forall₂_same]
  intro v _
  unfold RationalWordRows.RowRep GraphReachEncoded.edgeWords
  simp only [Function.comp_apply, List.map_map, List.forall₂_map_left_iff]
  rw [List.ofFn_eq_map, List.forall₂_map_right_iff, List.forall₂_same]
  intro e _
  have rep_eq : ∀ {w : BinaryRational.Word N} {a b : ℚ}, RationalWordRows.Rep w a → a = b →
      RationalWordRows.Rep w b := fun h hab => hab ▸ h
  simp only [entryW, eqb_word hn, Incidence.unsigned, decide_eq_true_eq]
  split_ifs <;> first
    | exact rep_eq ht (by norm_num) | exact rep_eq ho (by norm_num) | exact rep_eq hz (by norm_num)

/-- Coordinate vectors indexed by the length of an arbitrary list. -/
theorem coordinateVectorsW_cons (zero one : BinaryRational.Word N) (k : ℕ) :
    RationalWordRows.coordinateVectorsW zero one (k + 1) =
      (one :: List.replicate k zero) ::
        (RationalWordRows.coordinateVectorsW zero one k).map (zero :: ·) := rfl

/-! ## Fixed bodies -/

def selectBody : Command p :=
  .branch (.register 11)
    (.branch (.register 13) (.ret [.register 9]) (.ret [.register 8]))
    (.branch (.register 13) (.ret [.register 8]) (.ret [.register 6]))

/-- Arguments 0=edge record, 1=entry data; result is the selected constant record. -/
def entryBody (cmp : Fin p) : Command p :=
  RegisterPairReads.readPairs [(0, 2, 3), (1, 4, 5), (5, 6, 7), (7, 8, 9)]
    (.call cmp [.register 4, .register 2] [10, 11]
      (.call cmp [.register 4, .register 3] [12, 13] selectBody))

/-- Arguments 0=vertex word, 1=row data; result is the incidence row. -/
def rowBody (rowMap : Fin p) : Command p :=
  RegisterPairReads.readPairs [(1, 2, 3)]
    (.allocate 4 (.pair (.register 0) (.register 3))
      (.call rowMap [.register 2, .register 4] [5] (.ret [.register 5])))

/-- Arguments 0=vertex words, 1=edges, 2=zero, 3=one, 4=two; result is the row list. -/
def incidenceBody (rowsMap : Fin p) : Command p :=
  .allocate 5 (.pair (.register 3) (.register 4))
    (.allocate 6 (.pair (.register 2) (.register 5))
      (.allocate 7 (.pair (.register 1) (.register 6))
        (.call rowsMap [.register 0, .register 7] [8] (.ret [.register 8]))))

/-- Arguments 0=item, 1=data; returns the data pointer. -/
def constBody : Command p := .ret [.register 1]

/-- Arguments 0=row, 1=zero; returns `zero :: row`. -/
def consZeroBody : Command p :=
  .allocate 2 (.cons (.register 1) (.register 0)) (.ret [.register 2])

/-- Arguments 0=length witness list, 1=zero, 2=one; result is the coordinate vectors. -/
def coordsBody (self shift zeros : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := .call self [.register 4, .register 1, .register 2] [5]
      (.call shift [.register 5, .register 1] [6]
        (.call zeros [.register 4, .register 1] [7]
          (.allocate 8 (.cons (.register 2) (.register 7))
            (.allocate 9 (.cons (.register 8) (.register 6)) (.ret [.register 9]))))) }

structure Procedures (p : ℕ) where
  cmp : Fin p
  entry : Fin p
  rowMap : Fin p
  row : Fin p
  rowsMap : Fin p
  incidence : Fin p
  constItem : Fin p
  consZero : Fin p
  zeros : Fin p
  shift : Fin p
  coords : Fin p

structure Procedures.Matches (ids : Procedures p) (code : Code p) : Prop where
  cmp : code ids.cmp = RegisterComparator.comparatorBody ids.cmp
  entry : code ids.entry = entryBody ids.cmp
  rowMap : code ids.rowMap = RegisterListMap.body ids.rowMap ids.entry
  row : code ids.row = rowBody ids.rowMap
  rowsMap : code ids.rowsMap = RegisterListMap.body ids.rowsMap ids.row
  incidence : code ids.incidence = incidenceBody ids.rowsMap
  constItem : code ids.constItem = constBody
  consZero : code ids.consZero = consZeroBody
  zeros : code ids.zeros = RegisterListMap.body ids.zeros ids.constItem
  shift : code ids.shift = RegisterListMap.body ids.shift ids.consZero
  coords : code ids.coords = coordsBody ids.coords ids.shift ids.zeros

/-! ## Incidence rows -/

theorem select_compiled (code : Code p) (h : Heap) (regs : Registers) (bL bR : Bool)
    {zp op tp : Ptr} (hL : regs 11 = .flag bL) (hR : regs 13 = .flag bR)
    (h6 : regs 6 = .pointer zp) (h8 : regs 8 = .pointer op) (h9 : regs 9 = .pointer tp) :
    Within code h regs selectBody
      [.pointer (if bL then (if bR then tp else op) else (if bR then op else zp))] h 9 := by
  have eL : (Atom.register 11).eval regs = .flag bL := hL
  have eR : (Atom.register 13).eval regs = .flag bR := hR
  have ret6 : Within code h regs (.ret [.register 6]) [.pointer zp] h 3 := by
    simpa [values, Atom.eval, h6] using Within.ret code h regs [.register 6]
  have ret8 : Within code h regs (.ret [.register 8]) [.pointer op] h 3 := by
    simpa [values, Atom.eval, h8] using Within.ret code h regs [.register 8]
  have ret9 : Within code h regs (.ret [.register 9]) [.pointer tp] h 3 := by
    simpa [values, Atom.eval, h9] using Within.ret code h regs [.register 9]
  unfold selectBody
  cases bL <;> cases bR
  · exact Within.branch eL (Within.branch eR (by simpa using ret6))
  · exact Within.branch eL (Within.branch eR (by simpa using ret8))
  · exact Within.branch eL (Within.branch eR (by simpa using ret8))
  · exact Within.branch eL (Within.branch eR (by simpa using ret9))

def entryBudget (W : ℕ) : ℕ := 72 * W + 120

theorem entry_compiled (code : Code p) (ids : Procedures p) (hcode : ids.Matches code)
    {h : Heap} {ep dp : Ptr} {e : Bits W × Bits W} {vw : Bits W} {k : Consts N}
    (he : EdgeAt h ep e) (hd : EntryDataAt h dp (vw, k)) :
    ∃ q, At h q (entryW k vw e) ∧
      Within code h (initialRegisters [.pointer ep, .pointer dp]) (code ids.entry)
        [.pointer q] h (entryBudget W) := by
  obtain ⟨lp, rp, ecell, hl, hr⟩ := he
  obtain ⟨vp, cp, dcell, hv, zp, q2, op, tp, c1, c2, hz, ho, ht⟩ := hd
  let r0 := initialRegisters [Value.pointer ep, .pointer dp]
  let r1 := loadRegisters r0 2 3 15 (.pair lp rp)
  let r2 := loadRegisters r1 4 5 15 (.pair vp cp)
  let r3 := loadRegisters r2 6 7 15 (.pair zp q2)
  let r4 := loadRegisters r3 8 9 15 (.pair op tp)
  have reads : RegisterPairReads.Reads h r0 [(0, 2, 3), (1, 4, 5), (5, 6, 7), (7, 8, 9)] r4 := by
    refine .cons (ptr := ep) (by simp [r0, initialRegisters]) ecell ?_
    refine .cons (ptr := dp) (by simp [r0, loadRegisters, decoded, initialRegisters]) dcell ?_
    refine .cons (ptr := cp) (by simp [loadRegisters, decoded]) c1 ?_
    refine .cons (ptr := q2) (by simp [loadRegisters, decoded]) c2 ?_
    exact .nil _
  let r5 := bindResults r4 [10, 11] (RegisterComparator.flags (Bits.compare vw e.1).1)
  let r6 := bindResults r5 [12, 13] (RegisterComparator.flags (Bits.compare vw e.2).1)
  have sel := select_compiled code h r6 (eqb vw e.1) (eqb vw e.2) (zp := zp) (op := op) (tp := tp)
    (by simp [r6, r5, bindResults, RegisterComparator.flags, eqb])
    (by simp [r6, bindResults, RegisterComparator.flags, eqb])
    (by simp [r6, r5, r4, r3, bindResults, RegisterComparator.flags, loadRegisters, decoded])
    (by simp [r6, r5, r4, bindResults, RegisterComparator.flags, loadRegisters, decoded])
    (by simp [r6, r5, r4, bindResults, RegisterComparator.flags, loadRegisters, decoded])
  have cmp2 := RegisterComparator.compiled code ids.cmp hcode.cmp hv hr
  have c2Args : values r5 [.register 4, .register 3] = [.pointer vp, .pointer rp] := by
    simp [r5, r4, r3, r2, r1, bindResults, RegisterComparator.flags, loadRegisters, decoded,
      values, Atom.eval]
  have call2 := Within.call (procedure := ids.cmp) (arguments := [.register 4, .register 3])
    (results := [12, 13]) (regs := r5) (by simpa only [c2Args] using cmp2) sel
  have cmp1 := RegisterComparator.compiled code ids.cmp hcode.cmp hv hl
  have c1Args : values r4 [.register 4, .register 2] = [.pointer vp, .pointer lp] := by
    simp [r4, r3, r2, r1, loadRegisters, decoded, values, Atom.eval]
  have call1 := Within.call (procedure := ids.cmp) (arguments := [.register 4, .register 2])
    (results := [10, 11]) (regs := r4) (by simpa only [c1Args] using cmp1) call2
  have whole := reads.within call1
  refine ⟨if eqb vw e.1 then (if eqb vw e.2 then tp else op) else (if eqb vw e.2 then op else zp),
    ?_, ?_⟩
  · unfold entryW
    split_ifs <;> assumption
  · rw [hcode.entry]
    refine whole.mono ?_
    simp only [entryBudget, List.length_cons, List.length_nil]
    omega

def rowBudget (W m : ℕ) : ℕ := (entryBudget W + 35) * m + 50

theorem row_compiled (code : Code p) (ids : Procedures p) (hcode : ids.Matches code)
    {h : Heap} (hh : Valid h) {vp dp : Ptr} {vw : Bits W}
    {edges : List (Bits W × Bits W)} {k : Consts N}
    (hv : BitsAt h vp vw) (hd : RowDataAt h dp (edges, k)) :
    ∃ out q, Extends h out ∧ Valid out ∧ RowAt out q (edges.map (entryW k vw)) ∧
      Within code h (initialRegisters [.pointer vp, .pointer dp]) (code ids.row)
        [.pointer q] out (rowBudget W edges.length) := by
  obtain ⟨ep, cp, cell, hes, hk⟩ := hd
  have hcp : cp < h.length := by
    obtain ⟨_, _, _, _, c, _⟩ := hk
    exact (List.getElem?_eq_some_iff.mp c).1
  obtain ⟨e1, v1, c1⟩ := RegisterRationalCut.allocate_pair hh hv.allocated hcp
  let h1 := h ++ [.pair vp cp]
  have hdata : EntryDataAt h1 h.length (vw, k) := ⟨vp, cp, c1, hv.mono e1, hk.mono e1⟩
  obtain ⟨out, q, e2, v2, hq, mapped⟩ := RegisterListMap.compiled_const code ids.rowMap ids.entry
    hcode.rowMap EdgeAt EntryDataAt
    (fun heap ptr (w : BinaryRational.Word N) => At heap ptr w)
    (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext)
    (fun ext _ _ hx => hx.mono ext) (fun _ hx => hx.allocated)
    (fun d e => entryW d.2 d.1 e) (entryBudget W) v1 (hes.mono e1 (fun _ _ h => h.mono e1)) hdata
    (fun {h'} hv' {_} {_} _ hx hd' => by
      obtain ⟨q, hq, w⟩ := entry_compiled code ids hcode hx hd'
      exact ⟨h', q, .refl h', hv', hq, w⟩)
  refine ⟨out, q, e1.trans e2, v2, hq, ?_⟩
  let r0 := initialRegisters [Value.pointer vp, .pointer dp]
  let r1 := loadRegisters r0 2 3 15 (.pair ep cp)
  have reads : RegisterPairReads.Reads h r0 [(1, 2, 3)] r1 :=
    .cons (ptr := dp) (by simp [r0, initialRegisters]) cell (.nil _)
  let r2 := Function.update r1 4 (Value.pointer h.length)
  let r3 := bindResults r2 [5] [Value.pointer q]
  have last : Within code out r3 (.ret [.register 5]) [.pointer q] out 3 := by
    simpa [r3, bindResults, values, Atom.eval] using Within.ret code out r3 [.register 5]
  have mArgs : values r2 [.register 2, .register 4] = [.pointer ep, .pointer h.length] := by
    simp [r2, r1, loadRegisters, decoded, values, Atom.eval]
  have mCall := Within.call (procedure := ids.rowMap) (arguments := [.register 2, .register 4])
    (results := [5]) (regs := r2) (by simpa only [mArgs] using mapped) last
  have alloc := Within.allocate (h := h) (regs := r1) (dst := 4)
    (expr := .pair (.register 0) (.register 3)) (c := .pair vp cp)
    (by simp [CellExpr.eval, Atom.eval, r1, r0, loadRegisters, decoded, initialRegisters,
      Value.asPointer]) mCall
  have whole := reads.within alloc
  rw [hcode.row]
  refine whole.mono ?_
  simp only [rowBudget, CellExpr.args, List.length_cons, List.length_nil]
  omega

def incidenceBudget (W m n : ℕ) : ℕ := (rowBudget W m + 35) * n + 60

theorem incidence_compiled (code : Code p) (ids : Procedures p) (hcode : ids.Matches code)
    {h : Heap} (hh : Valid h) {vlp ep zp op tp : Ptr} {verts : List (Bits W)}
    {edges : List (Bits W × Bits W)} {zero one two : BinaryRational.Word N}
    (hvs : ListRep (fun heap ptr (w : Bits W) => BitsAt heap ptr w) h vlp verts)
    (hes : ListRep EdgeAt h ep edges) (hz : At h zp zero) (ho : At h op one) (ht : At h tp two) :
    ∃ out q, Extends h out ∧ Valid out ∧
      RowsAt out q (incidenceRowsW (zero, one, two) verts edges) ∧
      Within code h (initialRegisters [.pointer vlp, .pointer ep, .pointer zp, .pointer op,
        .pointer tp]) (code ids.incidence) [.pointer q] out
        (incidenceBudget W edges.length verts.length) := by
  obtain ⟨e1, v1, c1⟩ := RegisterRationalCut.allocate_pair hh ho.allocated ht.allocated
  let h1 := h ++ [.pair op tp]
  obtain ⟨e2, v2, c2⟩ := RegisterRationalCut.allocate_pair (a := zp) (b := h.length) v1
    (lt_of_lt_of_le hz.allocated e1.length_le) (by simp)
  let h2 := h1 ++ [.pair zp h.length]
  obtain ⟨e3, v3, c3⟩ := RegisterRationalCut.allocate_pair (a := ep) (b := h1.length) v2
    (lt_of_lt_of_le hes.allocated (e1.trans e2).length_le) (by simp [h1])
  let h3 := h2 ++ [.pair ep h1.length]
  have e13 : Extends h h3 := e1.trans (e2.trans e3)
  have hk : ConstsAt h3 h1.length (zero, one, two) :=
    ⟨zp, h.length, op, tp, e3.lookup c2, (e2.trans e3).lookup c1,
      hz.mono e13, ho.mono e13, ht.mono e13⟩
  have hdata : RowDataAt h3 h2.length (edges, (zero, one, two)) :=
    ⟨ep, h1.length, c3, hes.mono e13 (fun _ _ h => h.mono e13), hk⟩
  obtain ⟨out, q, e4, v4, hq, mapped⟩ := RegisterListMap.compiled_const code ids.rowsMap ids.row
    hcode.rowsMap (fun heap ptr (w : Bits W) => BitsAt heap ptr w) RowDataAt RowAt
    (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext)
    (fun ext _ _ hx => hx.mono ext) (fun _ hx => hx.allocated)
    (fun d vw => d.1.map (entryW d.2 vw)) (rowBudget W edges.length) v3
    (hvs.mono e13 (fun _ _ h => h.mono e13)) hdata
    (fun {_} hv' {_} {_} _ hx hd' => row_compiled code ids hcode hv' hx hd')
  refine ⟨out, q, e13.trans e4, v4, hq, ?_⟩
  let r0 := initialRegisters [Value.pointer vlp, .pointer ep, .pointer zp, .pointer op,
    .pointer tp]
  let r1 := Function.update r0 5 (Value.pointer h.length)
  let r2 := Function.update r1 6 (Value.pointer h1.length)
  let r3 := Function.update r2 7 (Value.pointer h2.length)
  let r4 := bindResults r3 [8] [Value.pointer q]
  have last : Within code out r4 (.ret [.register 8]) [.pointer q] out 3 := by
    simpa [r4, bindResults, values, Atom.eval] using Within.ret code out r4 [.register 8]
  have mArgs : values r3 [.register 0, .register 7] = [.pointer vlp, .pointer h2.length] := by
    simp [r3, r2, r1, r0, initialRegisters, values, Atom.eval]
  have mCall := Within.call (procedure := ids.rowsMap) (arguments := [.register 0, .register 7])
    (results := [8]) (regs := r3) (by simpa only [mArgs] using mapped) last
  have a7 := Within.allocate (h := h2) (regs := r2) (dst := 7)
    (expr := .pair (.register 1) (.register 6)) (c := .pair ep h1.length)
    (by simp [CellExpr.eval, Atom.eval, r2, r1, r0, initialRegisters, Value.asPointer]) mCall
  have a6 := Within.allocate (h := h1) (regs := r1) (dst := 6)
    (expr := .pair (.register 2) (.register 5)) (c := .pair zp h.length)
    (by simp [CellExpr.eval, Atom.eval, r1, r0, initialRegisters, Value.asPointer]) a7
  have a5 := Within.allocate (h := h) (regs := r0) (dst := 5)
    (expr := .pair (.register 3) (.register 4)) (c := .pair op tp)
    (by simp [CellExpr.eval, Atom.eval, r0, initialRegisters, Value.asPointer]) a6
  rw [hcode.incidence]
  refine a5.mono ?_
  simp only [incidenceBudget, CellExpr.args, List.length_cons, List.length_nil]
  omega

/-! ## Coordinate vectors -/

def coordsBudget (m : ℕ) : ℕ := (84 * m + 80) * m + 13

theorem coords_compiled {α : Type*} (code : Code p) (ids : Procedures p)
    (hcode : ids.Matches code) (InputAt : Heap → Ptr → α → Prop)
    (inputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, InputAt h ptr x → InputAt h' ptr x)
    {h : Heap} (hh : Valid h) {lp zp op : Ptr} {L : List α}
    {zero one : BinaryRational.Word N}
    (hl : ListRep InputAt h lp L) (hz : At h zp zero) (ho : At h op one) :
    ∃ out q, Extends h out ∧ Valid out ∧
      RowsAt out q (RationalWordRows.coordinateVectorsW zero one L.length) ∧
      Within code h (initialRegisters [.pointer lp, .pointer zp, .pointer op])
        (code ids.coords) [.pointer q] out (coordsBudget L.length) := by
  obtain ⟨ps, hlist, hrel⟩ := hl
  induction hlist generalizing L with
  | @nil lp cell =>
    cases hrel
    refine ⟨h, 0, .refl h, hh, RegisterListCommon.listRep_null hh, ?_⟩
    let regs := initialRegisters [Value.pointer lp, .pointer zp, .pointer op]
    let loaded := loadRegisters regs 3 4 15 .nil
    have last : Within code h loaded (.ret [.null]) [.pointer 0] h 3 := by
      simpa [values, Atom.eval] using Within.ret code h loaded [.null]
    rw [hcode.coords]
    apply Within.mono (a := 13) ?_ (by simp [coordsBudget])
    exact Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
      (branches := {CompiledTrie.failCases with
        nil := .ret [.null],
        cons := .call ids.coords [.register 4, .register 1, .register 2] [5]
          (.call ids.shift [.register 5, .register 1] [6]
            (.call ids.zeros [.register 4, .register 1] [7]
              (.allocate 8 (.cons (.register 2) (.register 7))
                (.allocate 9 (.cons (.register 8) (.register 6)) (.ret [.register 9])))))})
      (by simp [Atom.eval, regs, initialRegisters]) cell last
  | @cons lp ap tl tps cell tail ih =>
    cases hrel with
    | @cons _ x _ xs hx hxs =>
    obtain ⟨m1, rec, e1, v1, hrec, recursed⟩ := ih hxs
    obtain ⟨m2, sh, e2, v2, hsh, shifted⟩ := RegisterListMap.compiled_const code ids.shift
      ids.consZero hcode.shift RowAt (fun heap ptr (w : BinaryRational.Word N) => At heap ptr w)
      RowAt (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext)
      (fun ext _ _ hx => hx.mono ext) (fun _ hx => hx.allocated)
      (fun z v => z :: v) 11 v1 hrec (hz.mono e1)
      (fun {h'} hv' {vp} {v} _ hv hzz => by
        obtain ⟨ext, valid, rep⟩ := RegisterListCommon.allocate_consRep
          (R := fun heap ptr (w : BinaryRational.Word N) => At heap ptr w)
          (fun ext _ _ hq => At.mono ext hq) hv' hzz hzz.allocated hv
        refine ⟨_, _, ext, valid, rep, ?_⟩
        rw [hcode.consZero]
        exact RegisterListCommon.within_consRet code h' (dst := 2) (head := 1) (tail := 0)
          (by simp [initialRegisters]) (by simp [initialRegisters]))
    have e12 := e1.trans e2
    obtain ⟨m3, zs, e3, v3, hzs, zeroed⟩ := RegisterListMap.compiled_const code ids.zeros
      ids.constItem hcode.zeros InputAt (fun heap ptr (w : BinaryRational.Word N) => At heap ptr w)
      (fun heap ptr (w : BinaryRational.Word N) => At heap ptr w)
      inputMono (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext)
      (fun _ hx => hx.allocated) (fun z _ => z) 3 v2
      ⟨tps, tail.mono e12, hxs.imp (fun a b hab => inputMono e12 a b hab)⟩ (hz.mono e12)
      (fun {h'} hv' {_} {_} _ _ hzz => by
        refine ⟨h', zp, .refl h', hv', hzz, ?_⟩
        rw [hcode.constItem]
        simpa [constBody, values, Atom.eval, initialRegisters] using
          Within.ret code h' (initialRegisters [.pointer _, .pointer zp]) [.register 1])
    have e13 := e12.trans e3
    have hzs' : RowAt m3 zs (List.replicate xs.length zero) := by
      have h0 := hzs
      rw [List.map_const'] at h0
      exact h0
    obtain ⟨e4, v4, hunit⟩ := RegisterListCommon.allocate_consRep
      (R := fun heap ptr (w : BinaryRational.Word N) => At heap ptr w)
      (fun ext _ _ hq => At.mono ext hq) v3 (ho.mono e13) (ho.mono e13).allocated hzs'
    let m4 := m3 ++ [.cons op zs]
    obtain ⟨e5, v5, hall⟩ := RegisterListCommon.allocate_consRep
      (R := fun heap q (row : List (BinaryRational.Word N)) => RowAt heap q row)
      (fun ext _ _ hq => RowAt.mono ext hq) v4 hunit hunit.allocated
      (RowsAt.mono (e3.trans e4) hsh)
    refine ⟨m4 ++ [.cons m3.length sh], m4.length, e13.trans (e4.trans e5), v5,
      by rw [List.length_cons, RationalWordRows.coordinateVectorsW]; exact hall, ?_⟩
    let r0 := initialRegisters [Value.pointer lp, .pointer zp, .pointer op]
    let r1 := loadRegisters r0 3 4 15 (.cons ap tl)
    let r2 := bindResults r1 [5] [Value.pointer rec]
    let r3 := bindResults r2 [6] [Value.pointer sh]
    let r4 := bindResults r3 [7] [Value.pointer zs]
    let r5 := Function.update r4 8 (Value.pointer m3.length)
    have last := RegisterListCommon.within_consRet code m4 (regs := r5) (dst := 9)
      (head := 8) (tail := 6) (a := m3.length) (t := sh)
      (by simp [r5]) (by simp [r5, r4, r3, bindResults])
    have a8 := Within.allocate (h := m3) (regs := r4) (dst := 8)
      (expr := .cons (.register 2) (.register 7)) (c := .cons op zs)
      (by simp [CellExpr.eval, Atom.eval, r4, r3, r2, r1, r0, bindResults, loadRegisters,
        decoded, initialRegisters, Value.asPointer]) last
    have zArgs : values r3 [.register 4, .register 1] = [.pointer tl, .pointer zp] := by
      simp [r3, r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters, values,
        Atom.eval]
    have zCall := Within.call (procedure := ids.zeros) (arguments := [.register 4, .register 1])
      (results := [7]) (regs := r3) (by simpa only [zArgs] using zeroed) a8
    have sArgs : values r2 [.register 5, .register 1] = [.pointer rec, .pointer zp] := by
      simp [r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    have sCall := Within.call (procedure := ids.shift) (arguments := [.register 5, .register 1])
      (results := [6]) (regs := r2) (by simpa only [sArgs] using shifted) zCall
    have rArgs : values r1 [.register 4, .register 1, .register 2] =
        [.pointer tl, .pointer zp, .pointer op] := by
      simp [r1, r0, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    have rCall := Within.call (procedure := ids.coords)
      (arguments := [.register 4, .register 1, .register 2]) (results := [5]) (regs := r1)
      (by simpa only [rArgs] using recursed) sCall
    have loaded := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
      (branches := {CompiledTrie.failCases with
        nil := .ret [.null],
        cons := .call ids.coords [.register 4, .register 1, .register 2] [5]
          (.call ids.shift [.register 5, .register 1] [6]
            (.call ids.zeros [.register 4, .register 1] [7]
              (.allocate 8 (.cons (.register 2) (.register 7))
                (.allocate 9 (.cons (.register 8) (.register 6)) (.ret [.register 9])))))})
      (by simp [Atom.eval, r0, initialRegisters]) cell rCall
    rw [hcode.coords]
    refine loaded.mono ?_
    simp only [coordsBudget, CellExpr.args, List.length_cons, List.length_nil,
      RationalWordRows.coordinateVectorsW_length]
    have hlen : (RationalWordRows.coordinateVectorsW zero one xs.length).length = xs.length :=
      RationalWordRows.coordinateVectorsW_length _ _ _
    nlinarith

end WeightedMIS.RegisterIncidenceRows
