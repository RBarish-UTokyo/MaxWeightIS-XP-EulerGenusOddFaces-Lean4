module

public import WeightedMIS.RegisterFirstEdge
public import WeightedMIS.ResidualReachGeneric
public import WeightedMIS.RegisterListFlatMap

/-!
# Register construction of the adjacency search table

For the stored vertex words and the stored edge-count records, two nested
flat-map traversals visit all ordered pairs of vertex words in
`List.product` order. For each pair the first-edge scan decides whether an
edge joins the two words; if so, one arc record `.pair u (.pair v one)` with
the unit capacity word is prepended to the output. The vertex and unit words
are shared.

On the records of a graph this is exactly `ResidualReachGeneric.adjTable`, the
table whose residual search reproduces the routes of `GraphSearch.search`.
-/

@[expose] public section

namespace WeightedMIS.RegisterAdjacencyTable

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.ResidualWords
open WeightedMIS.GraphReachEncoded
open WeightedMIS.RegisterFirstEdge

variable {W B : ℕ}

/-! ## Reference -/

/-- The table entries contributed by one ordered pair of words. -/
def cell (one : Bits 1) (recs : List (Record W B)) (u v : Bits W) : List (Arc W 1) :=
  if (recs.find? (pred (u, v))).isSome then [⟨u, v, one⟩] else []

/-- All ordered pairs of words joined by a record, with the unit capacity. -/
def tableW (one : Bits 1) (recs : List (Record W B)) (nodes : List (Bits W)) : List (Arc W 1) :=
  nodes.flatMap fun u => nodes.flatMap fun v => cell one recs u v

theorem filter_map_eq_flatMap {α β : Type*} (l : List α) (p : α → Bool) (f : α → β) :
    (l.filter p).map f = l.flatMap fun x => if p x then [f x] else [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : p a = true
    · simp [ha, ih]
    · simp [ha, ih]

theorem tableW_eq {n m : ℕ} (hn : n < 2 ^ W) (left right : Fin m → Fin n) (yw : Fin m → Bits B) :
    tableW one (records W left right yw) (rangeWords W n) =
      ResidualReachGeneric.adjTable left right W := by
  unfold tableW ResidualReachGeneric.adjTable rangeWords List.product
  rw [List.filter_flatMap, List.map_flatMap, List.flatMap_map]
  congr 1
  funext u
  rw [List.flatMap_map, filter_map_eq_flatMap, List.flatMap_map]
  congr 1
  funext v
  simp only [cell, find_records hn, Option.isSome_map, GraphSearch.Adjacent,
    ResidualCrossingRefinement.encodeArc]
  by_cases hb : (GraphSearch.edgeBetween left right (List.finRange m) u v).isSome = true <;>
    simp [hb]

/-! ## Data records -/

/-- Inner data `.pair u (.pair records one)`, with a fixed record count. -/
def CellDataAt (M : ℕ) (h : Heap) (p : Ptr) (d : Bits W × List (Record W B) × Bits 1) : Prop :=
  ∃ up rest rp op, h[p]? = some (.pair up rest) ∧ h[rest]? = some (.pair rp op) ∧
    BitsAt h up d.1 ∧ RecordsAt h rp d.2.1 ∧ BitsAt h op d.2.2 ∧ d.2.1.length = M

theorem CellDataAt.mono {M : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr}
    {d : Bits W × List (Record W B) × Bits 1} (hd : CellDataAt M h p d) : CellDataAt M h' p d := by
  obtain ⟨up, rest, rp, op, c1, c2, hu, hr, ho, hl⟩ := hd
  exact ⟨up, rest, rp, op, he.lookup c1, he.lookup c2, hu.mono he, hr.mono he, ho.mono he, hl⟩

/-- Outer data `.pair nodes (.pair records one)`, with fixed lengths. -/
def RowDataAt (N M : ℕ) (h : Heap) (p : Ptr)
    (d : List (Bits W) × List (Record W B) × Bits 1) : Prop :=
  ∃ np rest rp op, h[p]? = some (.pair np rest) ∧ h[rest]? = some (.pair rp op) ∧
    WordsAt h np d.1 ∧ RecordsAt h rp d.2.1 ∧ BitsAt h op d.2.2 ∧ d.1.length = N ∧
    d.2.1.length = M

theorem RowDataAt.mono {N M : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr}
    {d : List (Bits W) × List (Record W B) × Bits 1} (hd : RowDataAt N M h p d) :
    RowDataAt N M h' p d := by
  obtain ⟨np, rest, rp, op, c1, c2, hn, hr, ho, hl, hm⟩ := hd
  exact ⟨np, rest, rp, op, he.lookup c1, he.lookup c2, hn.mono he, hr.mono he, ho.mono he, hl, hm⟩

/-! ## Procedures -/

variable {p : ℕ}

/-- Arguments: second word, inner data, accumulator. -/
def cellBody (find : Fin p) : Command p :=
  .load (.register 1) 3 4 15 { CompiledTrie.failCases with
    pair := .load (.register 4) 5 6 15 { CompiledTrie.failCases with
      pair := .allocate 7 (.pair (.register 3) (.register 0))
        (.call find [.register 5, .register 7] [8, 9]
          (.branch (.register 8)
            (.allocate 10 (.pair (.register 0) (.register 6))
              (.allocate 11 (.pair (.register 3) (.register 10))
                (.allocate 12 (.cons (.register 11) (.register 2)) (.ret [.register 12]))))
            (.ret [.register 2]))) } }

/-- Arguments: first word, outer data, accumulator. -/
def rowBody (inner : Fin p) : Command p :=
  .load (.register 1) 3 4 15 { CompiledTrie.failCases with
    pair := .allocate 5 (.pair (.register 0) (.register 4))
      (.call inner [.register 3, .register 5, .register 2] [6] (.ret [.register 6])) }

/-- Arguments: vertex words, records, unit word. Result: the table. -/
def tableBody (outer : Fin p) : Command p :=
  .allocate 3 (.pair (.register 1) (.register 2))
    (.allocate 4 (.pair (.register 0) (.register 3))
      (.call outer [.register 0, .register 4, .null] [5] (.ret [.register 5])))

structure Procedures (p : ℕ) where
  edge : RegisterFirstEdge.Procedures p
  cellItem : Fin p
  inner : Fin p
  rowItem : Fin p
  outer : Fin p
  self : Fin p

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  d.edge.Matches code ∧
  code d.cellItem = cellBody d.edge.find ∧
  code d.inner = RegisterListFlatMap.body d.inner d.cellItem ∧
  code d.rowItem = rowBody d.inner ∧
  code d.outer = RegisterListFlatMap.body d.outer d.rowItem ∧
  code d.self = tableBody d.outer

def cellBudget (W M : ℕ) : ℕ := findBudget W M + 80

def rowBudget (W M N : ℕ) : ℕ := (cellBudget W M + 27) * N + 50

def budget (W M N : ℕ) : ℕ := (rowBudget W M N + 27) * N + 40

theorem cell_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code) {M : ℕ}
    {h : Heap} (hh : Valid h) {vp dp acc : Ptr} {v : Bits W}
    {data : Bits W × List (Record W B) × Bits 1} {tail : List (Arc W 1)}
    (hv : BitsAt h vp v) (hd : CellDataAt M h dp data) (ht : TableAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧
      TableAt out q (cell data.2.2 data.2.1 data.1 v ++ tail) ∧
      Within code h (initialRegisters [.pointer vp, .pointer dp, .pointer acc])
        (code d.cellItem) [.pointer q] out (cellBudget W M) := by
  obtain ⟨u, recs, one⟩ := data
  obtain ⟨up, rest, rp, op, c1, c2, hu, hr, ho, hl⟩ := hd
  simp only at hu hr ho hl
  let H1 := h ++ [Cell.pair up vp]
  obtain ⟨e1, v1, q1⟩ := allocate_fits hh (pair_fits hu.allocated hv.allocated)
  have hq : QueryAt H1 h.length (u, v) := ⟨up, vp, q1, hu.mono e1, hv.mono e1⟩
  obtain ⟨H2, fp, e2, v2, hfound, frun⟩ := find_compiled code d.edge hm.1 v1 (hr.mono e1) hq
  let regs := initialRegisters [Value.pointer vp, .pointer dp, .pointer acc]
  let s1 := loadRegisters regs 3 4 15 (.pair up rest)
  let s2 := loadRegisters s1 5 6 15 (.pair rp op)
  let s3 := Function.update s2 7 (.pointer h.length)
  let s4 := bindResults s3 [8, 9]
    [.flag (recs.find? (pred (u, v))).isSome, .pointer fp]
  have fargs : values s3 [.register 5, .register 7] = [.pointer rp, .pointer h.length] := by
    simp [s3, s2, s1, regs, loadRegisters, decoded, values, Atom.eval]
  have tailRun : ∃ out q, Extends H2 out ∧ Valid out ∧
      TableAt out q (cell one recs u v ++ tail) ∧
      Within code H2 s4
        (.branch (.register 8)
          (.allocate 10 (.pair (.register 0) (.register 6))
            (.allocate 11 (.pair (.register 3) (.register 10))
              (.allocate 12 (.cons (.register 11) (.register 2)) (.ret [.register 12]))))
          (.ret [.register 2])) [.pointer q] out 40 := by
    have e12 := e1.trans e2
    by_cases hs : (recs.find? (pred (u, v))).isSome = true
    · let H3 := H2 ++ [Cell.pair vp op]
      let H4 := H3 ++ [Cell.pair up H2.length]
      let H5 := H4 ++ [Cell.cons H3.length acc]
      obtain ⟨e3, v3, q3⟩ := allocate_fits v2 (pair_fits (lt_of_ext e12 hv.allocated)
        (lt_of_ext e12 ho.allocated))
      obtain ⟨e4, v4, q4⟩ := allocate_fits v3 (pair_fits (h := H3) (a := up) (b := H2.length)
        (lt_of_ext (e12.trans e3) hu.allocated) (by simp [H3]))
      obtain ⟨e5, v5, q5⟩ := allocate_fits v4 (cons_fits (h := H4) (a := H3.length) (b := acc)
        (by simp [H4, H3])
        (lt_of_ext (e12.trans (e3.trans e4)) ht.allocated))
      have e25 := e3.trans (e4.trans e5)
      have harc : ArcAt H4 H3.length (⟨u, v, one⟩ : Arc W 1) :=
        ⟨up, H2.length, vp, op, q4, e4.lookup q3, hu.mono (e12.trans (e3.trans e4)),
          hv.mono (e12.trans (e3.trans e4)), ho.mono (e12.trans (e3.trans e4))⟩
      refine ⟨H5, H4.length, e25, v5, ?_, ?_⟩
      · simp only [cell, hs, ite_true, List.singleton_append]
        exact TableAt.cons q5 (harc.mono e5) (ht.mono (e12.trans e25))
      · let t1 := Function.update s4 10 (.pointer H2.length)
        let t2 := Function.update t1 11 (.pointer H3.length)
        let t3 := Function.update t2 12 (.pointer H4.length)
        have last : Within code H5 t3 (.ret [.register 12]) [.pointer H4.length] H5 3 := by
          simpa [t3, values, Atom.eval] using Within.ret code H5 t3 [.register 12]
        have a3 := Within.allocate (regs := t2) (dst := 12) (h := H4)
          (expr := .cons (.register 11) (.register 2)) (c := .cons H3.length acc)
          (by simp [CellExpr.eval, Atom.eval, t2, t1, s4, s3, s2, s1, regs, bindResults,
            loadRegisters, decoded, initialRegisters, Value.asPointer]) last
        have a2 := Within.allocate (regs := t1) (dst := 11) (h := H3)
          (expr := .pair (.register 3) (.register 10)) (c := .pair up H2.length)
          (by simp [CellExpr.eval, Atom.eval, t1, s4, s3, s2, s1, bindResults,
            loadRegisters, decoded, Value.asPointer]) a3
        have a1 := Within.allocate (regs := s4) (dst := 10) (h := H2)
          (expr := .pair (.register 0) (.register 6)) (c := .pair vp op)
          (by simp [CellExpr.eval, Atom.eval, s4, s3, s2, s1, regs, bindResults,
            loadRegisters, decoded, initialRegisters, Value.asPointer]) a2
        have b := Within.branch (b := true) (test := .register 8) (regs := s4)
          (no := .ret [.register 2])
          (by simp [s4, bindResults, Atom.eval, hs]) a1
        exact b.mono (by simp [CellExpr.args])
    · have hf : (recs.find? (pred (u, v))).isSome = false := by simpa using hs
      refine ⟨H2, acc, .refl _, v2, ?_, ?_⟩
      · simp only [cell, hf, Bool.false_eq_true, ite_false, List.nil_append]
        exact ht.mono e12
      · have last : Within code H2 s4 (.ret [.register 2]) [.pointer acc] H2 3 := by
          simpa [s4, s3, s2, s1, regs, bindResults, loadRegisters, decoded, initialRegisters,
            values, Atom.eval] using Within.ret code H2 s4 [.register 2]
        have b := Within.branch (b := false) (test := .register 8) (regs := s4)
          (yes := .allocate 10 (.pair (.register 0) (.register 6))
            (.allocate 11 (.pair (.register 3) (.register 10))
              (.allocate 12 (.cons (.register 11) (.register 2)) (.ret [.register 12]))))
          (by simp [s4, bindResults, Atom.eval, hf]) last
        exact b.mono (by omega)
  obtain ⟨out, q, e3, v3, hout, trun⟩ := tailRun
  refine ⟨out, q, e1.trans (e2.trans e3), v3, hout, ?_⟩
  have fcall := Within.call (procedure := d.edge.find) (regs := s3)
    (arguments := [.register 5, .register 7]) (results := [8, 9])
    (by simpa only [fargs] using frun) trun
  have al := Within.allocate (regs := s2) (dst := 7) (h := h)
    (expr := .pair (.register 3) (.register 0)) (c := .pair up vp)
    (by simp [CellExpr.eval, Atom.eval, s2, s1, regs, loadRegisters, decoded, initialRegisters,
      Value.asPointer]) fcall
  have l2 := Within.load (regs := s1) (address := .register 4) (first := 5) (second := 6)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .allocate 7 (.pair (.register 3) (.register 0))
        (.call d.edge.find [.register 5, .register 7] [8, 9]
          (.branch (.register 8)
            (.allocate 10 (.pair (.register 0) (.register 6))
              (.allocate 11 (.pair (.register 3) (.register 10))
                (.allocate 12 (.cons (.register 11) (.register 2)) (.ret [.register 12]))))
            (.ret [.register 2]))) })
    (by simp [s1, loadRegisters, decoded, Atom.eval]) c2 al
  have l1 := Within.load (regs := regs) (address := .register 1) (first := 3) (second := 4)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 4) 5 6 15 { CompiledTrie.failCases with
        pair := .allocate 7 (.pair (.register 3) (.register 0))
          (.call d.edge.find [.register 5, .register 7] [8, 9]
            (.branch (.register 8)
              (.allocate 10 (.pair (.register 0) (.register 6))
                (.allocate 11 (.pair (.register 3) (.register 10))
                  (.allocate 12 (.cons (.register 11) (.register 2)) (.ret [.register 12]))))
              (.ret [.register 2]))) } })
    (by simp [regs, initialRegisters, Atom.eval]) c1 l2
  rw [hm.2.1]
  exact l1.mono (by simp [cellBudget, CellExpr.args, hl]; omega)

theorem row_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code) {N M : ℕ}
    {h : Heap} (hh : Valid h) {up dp acc : Ptr} {u : Bits W}
    {data : List (Bits W) × List (Record W B) × Bits 1} {tail : List (Arc W 1)}
    (hu : BitsAt h up u) (hd : RowDataAt N M h dp data) (ht : TableAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧
      TableAt out q (data.1.flatMap (cell data.2.2 data.2.1 u) ++ tail) ∧
      Within code h (initialRegisters [.pointer up, .pointer dp, .pointer acc])
        (code d.rowItem) [.pointer q] out (rowBudget W M N) := by
  obtain ⟨nodes, recs, one⟩ := data
  obtain ⟨np, rest, rp, op, c1, c2, hn, hr, ho, hln, hlm⟩ := hd
  simp only at hn hr ho hln hlm
  let H1 := h ++ [Cell.pair up rest]
  have hrest : rest < h.length := (List.getElem?_eq_some_iff.mp c2).1
  obtain ⟨e1, v1, q1⟩ := allocate_fits hh (pair_fits hu.allocated hrest)
  have hcd : CellDataAt M H1 h.length (u, recs, one) :=
    ⟨up, rest, rp, op, q1, e1.lookup c2, hu.mono e1, hr.mono e1, ho.mono e1, hlm⟩
  obtain ⟨out, q, e2, v2, hout, irun⟩ := RegisterListFlatMap.compiled code d.inner d.cellItem
    hm.2.2.1 (fun h p (x : Bits W) => BitsAt h p x) (CellDataAt M) (fun h p l => TableAt h p l)
    (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he)
    (fun data x => cell data.2.2 data.2.1 data.1 x) (cellBudget W M)
    (fun hv _ _ _ _ _ _ hx hd ht => cell_compiled code d hm hv hx hd ht)
    v1 (hn.mono e1) hcd (ht.mono e1)
  refine ⟨out, q, e1.trans e2, v2, hout, ?_⟩
  let regs := initialRegisters [Value.pointer up, .pointer dp, .pointer acc]
  let s1 := loadRegisters regs 3 4 15 (.pair np rest)
  let s2 := Function.update s1 5 (.pointer h.length)
  let s3 := bindResults s2 [6] [.pointer q]
  have last : Within code out s3 (.ret [.register 6]) [.pointer q] out 3 := by
    simpa [s3, bindResults, values, Atom.eval] using Within.ret code out s3 [.register 6]
  have iargs : values s2 [.register 3, .register 5, .register 2] =
      [.pointer np, .pointer h.length, .pointer acc] := by
    simp [s2, s1, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
  have icall := Within.call (procedure := d.inner) (regs := s2)
    (arguments := [.register 3, .register 5, .register 2]) (results := [6])
    (by simpa only [iargs] using irun) last
  have al := Within.allocate (regs := s1) (dst := 5) (h := h)
    (expr := .pair (.register 0) (.register 4)) (c := .pair up rest)
    (by simp [CellExpr.eval, Atom.eval, s1, regs, loadRegisters, decoded, initialRegisters,
      Value.asPointer]) icall
  have l1 := Within.load (regs := regs) (address := .register 1) (first := 3) (second := 4)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .allocate 5 (.pair (.register 0) (.register 4))
        (.call d.inner [.register 3, .register 5, .register 2] [6] (.ret [.register 6])) })
    (by simp [regs, initialRegisters, Atom.eval]) c1 al
  rw [hm.2.2.2.1]
  exact l1.mono (by simp [rowBudget, CellExpr.args, hln]; omega)

/-- The table of all ordered pairs of stored words joined by a stored record. -/
theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {h : Heap} (hh : Valid h) {np rp op : Ptr} {nodes : List (Bits W)}
    {recs : List (Record W B)} {one : Bits 1}
    (hn : WordsAt h np nodes) (hr : RecordsAt h rp recs) (ho : BitsAt h op one) :
    ∃ out q, Extends h out ∧ Valid out ∧ TableAt out q (tableW one recs nodes) ∧
      Within code h (initialRegisters [.pointer np, .pointer rp, .pointer op])
        (code d.self) [.pointer q] out (budget W recs.length nodes.length) := by
  let H1 := h ++ [Cell.pair rp op]
  let H2 := H1 ++ [Cell.pair np h.length]
  obtain ⟨e1, v1, q1⟩ := allocate_fits hh (pair_fits (ListRep.allocated hr) ho.allocated)
  obtain ⟨e2, v2, q2⟩ := allocate_fits v1 (pair_fits (h := H1) (a := np) (b := h.length)
    (lt_of_ext e1 (ListRep.allocated hn)) (by simp [H1]))
  have hrd : RowDataAt nodes.length recs.length H2 H1.length (nodes, recs, one) :=
    ⟨np, h.length, rp, op, q2, e2.lookup q1, (hn.mono e1).mono e2, (hr.mono e1).mono e2,
      (ho.mono e1).mono e2, rfl, rfl⟩
  obtain ⟨out, q, e3, v3, hout, orun⟩ := RegisterListFlatMap.compiled code d.outer d.rowItem
    hm.2.2.2.2.1 (fun h p (x : Bits W) => BitsAt h p x) (RowDataAt nodes.length recs.length)
    (fun h p l => TableAt h p l) (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he)
    (fun data x => data.1.flatMap (cell data.2.2 data.2.1 x))
    (rowBudget W recs.length nodes.length)
    (fun hv _ _ _ _ _ _ hx hd ht => row_compiled code d hm hv hx hd ht)
    v2 ((hn.mono e1).mono e2) hrd (TableAt.nil v2.1)
  refine ⟨out, q, e1.trans (e2.trans e3), v3, by rw [List.append_nil] at hout; exact hout, ?_⟩
  let regs := initialRegisters [Value.pointer np, .pointer rp, .pointer op]
  let s1 := Function.update regs 3 (.pointer h.length)
  let s2 := Function.update s1 4 (.pointer H1.length)
  let s3 := bindResults s2 [5] [.pointer q]
  have last : Within code out s3 (.ret [.register 5]) [.pointer q] out 3 := by
    simpa [s3, bindResults, values, Atom.eval] using Within.ret code out s3 [.register 5]
  have oargs : values s2 [.register 0, .register 4, .null] =
      [.pointer np, .pointer H1.length, .pointer 0] := by
    simp [s2, s1, regs, initialRegisters, values, Atom.eval]
  have ocall := Within.call (procedure := d.outer) (regs := s2)
    (arguments := [.register 0, .register 4, .null]) (results := [5])
    (by simpa only [oargs] using orun) last
  have a2 := Within.allocate (regs := s1) (dst := 4) (h := H1)
    (expr := .pair (.register 0) (.register 3)) (c := .pair np h.length)
    (by simp [CellExpr.eval, Atom.eval, s1, regs, initialRegisters, Value.asPointer]) ocall
  have a1 := Within.allocate (regs := regs) (dst := 3) (h := h)
    (expr := .pair (.register 1) (.register 2)) (c := .pair rp op)
    (by simp [CellExpr.eval, Atom.eval, regs, initialRegisters, Value.asPointer]) a2
  rw [hm.2.2.2.2.2]
  exact a1.mono (by simp [budget, CellExpr.args]; omega)

end WeightedMIS.RegisterAdjacencyTable
