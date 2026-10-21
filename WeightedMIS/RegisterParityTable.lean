module

public import WeightedMIS.ParityReachRefinement

/-!
# Register construction of the parity search table

From the stored edge endpoint words and the stored edge index words, the
procedure zips edge-index records, expands every record `((l, r), i)` into the
two parity records `((l⁰, r¹), i)` and `((l¹, r⁰), i)`, expands every vertex
word `v` into its two parity copies `v⁰, v¹`, and builds the adjacency table of
`RegisterAdjacencyTable` on the parity copies and parity records. A parity copy
is one `bit` cell in front of the shared vertex word.

The result is `ParityReachRefinement.parityTableW`; the edge-index records and
the parity copies are also returned.
-/

@[expose] public section

namespace WeightedMIS.RegisterParityTable

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.ResidualWords
open WeightedMIS.GraphReachEncoded WeightedMIS.RegisterFirstEdge WeightedMIS.ParityReachRefinement
open WeightedMIS.RegisterIncidenceRows (EdgeAt)

variable {W K : ℕ}

theorem listRep_cons {α : Type*} {R : Heap → Ptr → α → Prop} {h : Heap} {p a t : Ptr}
    {x : α} {xs : List α} (hc : h[p]? = some (.cons a t)) (ha : R h a x)
    (ht : ListRep R h t xs) : ListRep R h p (x :: xs) := by
  obtain ⟨ps, hp, hw⟩ := ht
  exact ⟨a :: ps, .cons hc hp, .cons ha hw⟩

theorem lt_app {h : Heap} {a : Ptr} (ha : a < h.length) (c : Cell) :
    a < (h ++ [c]).length := lt_of_lt_of_le ha (by simp)

/-! ## Procedures -/

variable {p : ℕ}

/-- Arguments: edge-index record, unused data, accumulator. -/
def pairItemBody : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    pair := .load (.register 3) 5 6 15 { CompiledTrie.failCases with
      pair :=
        .allocate 7 (.bit (.flag false) (.register 5))
        (.allocate 8 (.bit (.flag true) (.register 6))
        (.allocate 9 (.pair (.register 7) (.register 8))
        (.allocate 10 (.pair (.register 9) (.register 4))
        (.allocate 7 (.bit (.flag true) (.register 5))
        (.allocate 8 (.bit (.flag false) (.register 6))
        (.allocate 9 (.pair (.register 7) (.register 8))
        (.allocate 11 (.pair (.register 9) (.register 4))
        (.allocate 12 (.cons (.register 11) (.register 2))
        (.allocate 13 (.cons (.register 10) (.register 12))
        (.ret [.register 13])))))))))) } }

/-- Arguments: vertex word, unused data, accumulator. -/
def nodeItemBody : Command p :=
  .allocate 3 (.bit (.flag false) (.register 0))
  (.allocate 4 (.bit (.flag true) (.register 0))
  (.allocate 5 (.cons (.register 4) (.register 2))
  (.allocate 6 (.cons (.register 3) (.register 5))
  (.ret [.register 6]))))

/-- Arguments: edges, index words, vertex words, unit word of width one.
Results: the parity table, the edge-index records, the parity copies. -/
def tableBody (zip pairs nodes table : Fin p) : Command p :=
  .call zip [.register 0, .register 1, .null] [4]
    (.call pairs [.register 4, .null, .null] [5]
      (.call nodes [.register 2, .null, .null] [6]
        (.call table [.register 6, .register 5, .register 3] [7]
          (.ret [.register 7, .register 4, .register 6]))))

structure Procedures (p : ℕ) where
  table : RegisterAdjacencyTable.Procedures p
  pairItem : Fin p
  pairs : Fin p
  nodeItem : Fin p
  nodes : Fin p
  self : Fin p

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  d.table.Matches code ∧
  code d.pairItem = pairItemBody ∧
  code d.pairs = RegisterListFlatMap.body d.pairs d.pairItem ∧
  code d.nodeItem = nodeItemBody ∧
  code d.nodes = RegisterListFlatMap.body d.nodes d.nodeItem ∧
  code d.self = tableBody d.table.edge.zip d.pairs d.nodes d.table.self

theorem pairItem_compiled (code : Code p) (item : Fin p) (hitem : code item = pairItemBody)
    {h : Heap} (hh : Valid h) {rp dp acc : Ptr} {r : Record W K}
    {tail : List (Record (W + 1) K)}
    (hr : RecordAt h rp r) (ht : RecordsAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧ RecordsAt out q (parityPair r ++ tail) ∧
      Within code h (initialRegisters [.pointer rp, .pointer dp, .pointer acc])
        (code item) [.pointer q] out 110 := by
  obtain ⟨⟨l, rr⟩, c⟩ := r
  obtain ⟨ep, cp, c1, ⟨lp, rrp, c2, hl, hrr⟩, hc⟩ := hr
  have hlp := hl.allocated
  have hrp := hrr.allocated
  have hcp := hc.allocated
  have hacc := ListRep.allocated ht
  let H1 := h ++ [Cell.bit false lp]
  let H2 := H1 ++ [Cell.bit true rrp]
  let H3 := H2 ++ [Cell.pair h.length H1.length]
  let H4 := H3 ++ [Cell.pair H2.length cp]
  let H5 := H4 ++ [Cell.bit true lp]
  let H6 := H5 ++ [Cell.bit false rrp]
  let H7 := H6 ++ [Cell.pair H4.length H5.length]
  let H8 := H7 ++ [Cell.pair H6.length cp]
  let H9 := H8 ++ [Cell.cons H7.length acc]
  let H10 := H9 ++ [Cell.cons H3.length H8.length]
  obtain ⟨e1, v1, q1⟩ := allocate_fits hh (bit_fits (b := false) hlp)
  obtain ⟨e2, v2, q2⟩ := allocate_fits v1 (bit_fits (h := H1) (b := true) (a := rrp)
    (lt_app hrp _))
  obtain ⟨e3, v3, q3⟩ := allocate_fits v2 (pair_fits (h := H2) (a := h.length) (b := H1.length)
    (by simp [H2, H1]) (by simp [H2, H1]))
  obtain ⟨e4, v4, q4⟩ := allocate_fits v3 (pair_fits (h := H3) (a := H2.length) (b := cp)
    (by simp [H3, H2, H1]) (lt_app (lt_app (lt_app hcp _) _) _))
  obtain ⟨e5, v5, q5⟩ := allocate_fits v4 (bit_fits (h := H4) (b := true) (a := lp)
    (lt_app (lt_app (lt_app (lt_app hlp _) _) _) _))
  obtain ⟨e6, v6, q6⟩ := allocate_fits v5 (bit_fits (h := H5) (b := false) (a := rrp)
    (lt_app (lt_app (lt_app (lt_app (lt_app hrp _) _) _) _) _))
  obtain ⟨e7, v7, q7⟩ := allocate_fits v6 (pair_fits (h := H6) (a := H4.length) (b := H5.length)
    (by simp [H6, H5, H4, H3, H2, H1]) (by simp [H6, H5, H4, H3, H2, H1]))
  obtain ⟨e8, v8, q8⟩ := allocate_fits v7 (pair_fits (h := H7) (a := H6.length) (b := cp)
    (by simp [H7, H6, H5, H4, H3, H2, H1])
      (lt_app (lt_app (lt_app (lt_app (lt_app (lt_app (lt_app hcp _) _) _) _) _) _) _))
  obtain ⟨e9, v9, q9⟩ := allocate_fits v8 (cons_fits (h := H8) (a := H7.length) (b := acc)
    (by simp [H8, H7, H6, H5, H4, H3, H2, H1])
      (lt_app (lt_app (lt_app (lt_app (lt_app (lt_app (lt_app (lt_app hacc _) _) _) _) _) _) _) _))
  obtain ⟨e10, v10, q10⟩ := allocate_fits v9 (cons_fits (h := H9) (a := H3.length)
    (b := H8.length) (by simp [H9, H8, H7, H6, H5, H4, H3, H2, H1])
    (by simp [H9, H8, H7, H6, H5, H4, H3, H2, H1]))
  have x9 : Extends H9 H10 := e10
  have x8 : Extends H8 H10 := e9.trans x9
  have x7 : Extends H7 H10 := e8.trans x8
  have x6 : Extends H6 H10 := e7.trans x7
  have x5 : Extends H5 H10 := e6.trans x6
  have x4 : Extends H4 H10 := e5.trans x5
  have x3 : Extends H3 H10 := e4.trans x4
  have x2 : Extends H2 H10 := e3.trans x3
  have x1 : Extends H1 H10 := e2.trans x2
  have x0 : Extends h H10 := e1.trans x1
  have hl' := hl.mono x0
  have hrr' := hrr.mono x0
  have hc' := hc.mono x0
  have r1 : RecordAt H10 H3.length
      (((parityWord false l, parityWord true rr), c) : Record (W + 1) K) :=
    ⟨H2.length, cp, x4.lookup q4, ⟨h.length, H1.length, x3.lookup q3,
      BitsAt.cons (x1.lookup q1) hl', BitsAt.cons (x2.lookup q2) hrr'⟩, hc'⟩
  have r2 : RecordAt H10 H7.length
      (((parityWord true l, parityWord false rr), c) : Record (W + 1) K) :=
    ⟨H6.length, cp, x8.lookup q8, ⟨H4.length, H5.length, x7.lookup q7,
      BitsAt.cons (x5.lookup q5) hl', BitsAt.cons (x6.lookup q6) hrr'⟩, hc'⟩
  have hout : RecordsAt H10 H9.length (parityPair ((l, rr), c) ++ tail) :=
    listRep_cons q10 r1 (listRep_cons (x9.lookup q9) r2 (ht.mono x0))
  refine ⟨H10, H9.length, x0, v10, hout, ?_⟩
  let regs := initialRegisters [Value.pointer rp, .pointer dp, .pointer acc]
  let s1 := loadRegisters regs 3 4 15 (.pair ep cp)
  let s2 := loadRegisters s1 5 6 15 (.pair lp rrp)
  let t1 := Function.update s2 7 (.pointer h.length)
  let t2 := Function.update t1 8 (.pointer H1.length)
  let t3 := Function.update t2 9 (.pointer H2.length)
  let t4 := Function.update t3 10 (.pointer H3.length)
  let t5 := Function.update t4 7 (.pointer H4.length)
  let t6 := Function.update t5 8 (.pointer H5.length)
  let t7 := Function.update t6 9 (.pointer H6.length)
  let t8 := Function.update t7 11 (.pointer H7.length)
  let t9 := Function.update t8 12 (.pointer H8.length)
  let t10 := Function.update t9 13 (.pointer H9.length)
  have last : Within code H10 t10 (.ret [.register 13]) [.pointer H9.length] H10 3 := by
    simpa [t10, values, Atom.eval] using Within.ret code H10 t10 [.register 13]
  have a10 := Within.allocate (regs := t9) (dst := 13) (h := H9)
    (expr := .cons (.register 10) (.register 12)) (c := .cons H3.length H8.length)
    (by simp [CellExpr.eval, Atom.eval, t9, t8, t7, t6, t5, t4, Value.asPointer]) last
  have a9 := Within.allocate (regs := t8) (dst := 12) (h := H8)
    (expr := .cons (.register 11) (.register 2)) (c := .cons H7.length acc)
    (by simp [CellExpr.eval, Atom.eval, t8, t7, t6, t5, t4, t3, t2, t1, s2, s1, regs,
      loadRegisters, decoded, initialRegisters, Value.asPointer]) a10
  have a8 := Within.allocate (regs := t7) (dst := 11) (h := H7)
    (expr := .pair (.register 9) (.register 4)) (c := .pair H6.length cp)
    (by simp [CellExpr.eval, Atom.eval, t7, t6, t5, t4, t3, t2, t1, s2, s1, regs,
      loadRegisters, decoded, Value.asPointer]) a9
  have a7 := Within.allocate (regs := t6) (dst := 9) (h := H6)
    (expr := .pair (.register 7) (.register 8)) (c := .pair H4.length H5.length)
    (by simp [CellExpr.eval, Atom.eval, t6, t5, Value.asPointer]) a8
  have a6 := Within.allocate (regs := t5) (dst := 8) (h := H5)
    (expr := .bit (.flag false) (.register 6)) (c := .bit false rrp)
    (by simp [CellExpr.eval, Atom.eval, t5, t4, t3, t2, t1, s2, s1, regs,
      loadRegisters, decoded, Value.asPointer, Value.asFlag]) a7
  have a5 := Within.allocate (regs := t4) (dst := 7) (h := H4)
    (expr := .bit (.flag true) (.register 5)) (c := .bit true lp)
    (by simp [CellExpr.eval, Atom.eval, t4, t3, t2, t1, s2, s1, regs,
      loadRegisters, decoded, Value.asPointer, Value.asFlag]) a6
  have a4 := Within.allocate (regs := t3) (dst := 10) (h := H3)
    (expr := .pair (.register 9) (.register 4)) (c := .pair H2.length cp)
    (by simp [CellExpr.eval, Atom.eval, t3, t2, t1, s2, s1, regs,
      loadRegisters, decoded, Value.asPointer]) a5
  have a3 := Within.allocate (regs := t2) (dst := 9) (h := H2)
    (expr := .pair (.register 7) (.register 8)) (c := .pair h.length H1.length)
    (by simp [CellExpr.eval, Atom.eval, t2, t1, Value.asPointer]) a4
  have a2 := Within.allocate (regs := t1) (dst := 8) (h := H1)
    (expr := .bit (.flag true) (.register 6)) (c := .bit true rrp)
    (by simp [CellExpr.eval, Atom.eval, t1, s2, s1, regs,
      loadRegisters, decoded, Value.asPointer, Value.asFlag]) a3
  have a1 := Within.allocate (regs := s2) (dst := 7) (h := h)
    (expr := .bit (.flag false) (.register 5)) (c := .bit false lp)
    (by simp [CellExpr.eval, Atom.eval, s2, s1, regs,
      loadRegisters, decoded, Value.asPointer, Value.asFlag]) a2
  have l2 := Within.load (regs := s1) (address := .register 3) (first := 5) (second := 6)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair :=
        .allocate 7 (.bit (.flag false) (.register 5))
        (.allocate 8 (.bit (.flag true) (.register 6))
        (.allocate 9 (.pair (.register 7) (.register 8))
        (.allocate 10 (.pair (.register 9) (.register 4))
        (.allocate 7 (.bit (.flag true) (.register 5))
        (.allocate 8 (.bit (.flag false) (.register 6))
        (.allocate 9 (.pair (.register 7) (.register 8))
        (.allocate 11 (.pair (.register 9) (.register 4))
        (.allocate 12 (.cons (.register 11) (.register 2))
        (.allocate 13 (.cons (.register 10) (.register 12))
        (.ret [.register 13])))))))))) })
    (by simp [s1, loadRegisters, decoded, Atom.eval]) c2 a1
  have l1 := Within.load (regs := regs) (address := .register 0) (first := 3) (second := 4)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 3) 5 6 15 { CompiledTrie.failCases with
        pair :=
          .allocate 7 (.bit (.flag false) (.register 5))
          (.allocate 8 (.bit (.flag true) (.register 6))
          (.allocate 9 (.pair (.register 7) (.register 8))
          (.allocate 10 (.pair (.register 9) (.register 4))
          (.allocate 7 (.bit (.flag true) (.register 5))
          (.allocate 8 (.bit (.flag false) (.register 6))
          (.allocate 9 (.pair (.register 7) (.register 8))
          (.allocate 11 (.pair (.register 9) (.register 4))
          (.allocate 12 (.cons (.register 11) (.register 2))
          (.allocate 13 (.cons (.register 10) (.register 12))
          (.ret [.register 13])))))))))) } })
    (by simp [regs, initialRegisters, Atom.eval]) c1 l2
  rw [hitem]
  exact l1.mono (by simp [CellExpr.args])

theorem nodeItem_compiled (code : Code p) (item : Fin p) (hitem : code item = nodeItemBody)
    {h : Heap} (hh : Valid h) {vp dp acc : Ptr} {v : Bits W} {tail : List (Bits (W + 1))}
    (hv : BitsAt h vp v) (ht : WordsAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q ([parityWord false v, parityWord true v] ++ tail) ∧
      Within code h (initialRegisters [.pointer vp, .pointer dp, .pointer acc])
        (code item) [.pointer q] out 40 := by
  have hvp := hv.allocated
  have hacc := ListRep.allocated ht
  let H1 := h ++ [Cell.bit false vp]
  let H2 := H1 ++ [Cell.bit true vp]
  let H3 := H2 ++ [Cell.cons H1.length acc]
  let H4 := H3 ++ [Cell.cons h.length H2.length]
  obtain ⟨e1, v1, q1⟩ := allocate_fits hh (bit_fits (b := false) hvp)
  obtain ⟨e2, v2, q2⟩ := allocate_fits v1 (bit_fits (h := H1) (b := true) (a := vp)
    (lt_app hvp _))
  obtain ⟨e3, v3, q3⟩ := allocate_fits v2 (cons_fits (h := H2) (a := H1.length) (b := acc)
    (by simp [H2, H1]) (lt_app (lt_app hacc _) _))
  obtain ⟨e4, v4, q4⟩ := allocate_fits v3 (cons_fits (h := H3) (a := h.length) (b := H2.length)
    (by simp [H3, H2, H1]) (by simp [H3, H2, H1]))
  have x3 : Extends H3 H4 := e4
  have x2 : Extends H2 H4 := e3.trans x3
  have x1 : Extends H1 H4 := e2.trans x2
  have x0 : Extends h H4 := e1.trans x1
  have hv' := hv.mono x0
  refine ⟨H4, H3.length, x0, v4, ?_, ?_⟩
  · exact WordsAt.cons q4 (BitsAt.cons (x1.lookup q1) hv')
      (WordsAt.cons (x3.lookup q3) (BitsAt.cons (x2.lookup q2) hv') (ht.mono x0))
  let regs := initialRegisters [Value.pointer vp, .pointer dp, .pointer acc]
  let t1 := Function.update regs 3 (.pointer h.length)
  let t2 := Function.update t1 4 (.pointer H1.length)
  let t3 := Function.update t2 5 (.pointer H2.length)
  let t4 := Function.update t3 6 (.pointer H3.length)
  have last : Within code H4 t4 (.ret [.register 6]) [.pointer H3.length] H4 3 := by
    simpa [t4, values, Atom.eval] using Within.ret code H4 t4 [.register 6]
  have a4 := Within.allocate (regs := t3) (dst := 6) (h := H3)
    (expr := .cons (.register 3) (.register 5)) (c := .cons h.length H2.length)
    (by simp [CellExpr.eval, Atom.eval, t3, t2, t1, Value.asPointer]) last
  have a3 := Within.allocate (regs := t2) (dst := 5) (h := H2)
    (expr := .cons (.register 4) (.register 2)) (c := .cons H1.length acc)
    (by simp [CellExpr.eval, Atom.eval, t2, t1, regs, initialRegisters, Value.asPointer]) a4
  have a2 := Within.allocate (regs := t1) (dst := 4) (h := H1)
    (expr := .bit (.flag true) (.register 0)) (c := .bit true vp)
    (by simp [CellExpr.eval, Atom.eval, t1, regs, initialRegisters, Value.asPointer,
      Value.asFlag]) a3
  have a1 := Within.allocate (regs := regs) (dst := 3) (h := h)
    (expr := .bit (.flag false) (.register 0)) (c := .bit false vp)
    (by simp [CellExpr.eval, Atom.eval, regs, initialRegisters, Value.asPointer,
      Value.asFlag]) a2
  rw [hitem]
  exact a1.mono (by simp [CellExpr.args])

def budget (W M N : ℕ) : ℕ :=
  (56 * M + 23) + (137 * M + 13) + (67 * N + 13) +
    RegisterAdjacencyTable.budget (W + 1) (2 * M) (2 * N) + 40

theorem parityRecords_length (recs : List (Record W K)) :
    (parityRecords recs).length = 2 * recs.length := by
  induction recs with
  | nil => rfl
  | cons r rs ih =>
    simp only [parityRecords, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]
    simp [parityPair]
    ring

theorem parityNodeWords_length' (nodes : List (Bits W)) :
    (parityNodeWords nodes).length = 2 * nodes.length := by
  induction nodes with
  | nil => rfl
  | cons r rs ih =>
    simp only [parityNodeWords, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]
    simp
    ring

/-- The parity table, the edge-index records and the parity copies. -/
theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {n m : ℕ} (left right : Fin m → Fin n)
    {h : Heap} (hh : Valid h) {ep ip np op : Ptr}
    (he : ListRep EdgeAt h ep (edgeWords W left right))
    (hi : WordsAt h ip (rangeWords K m)) (hn : WordsAt h np (rangeWords W n))
    (ho : BitsAt h op one) :
    ∃ out tp rp pp, Extends h out ∧ Valid out ∧
      TableAt out tp (parityTableW (records W left right (fun e => word K e.val)) (rangeWords W n)) ∧
      RecordsAt out rp (records W left right (fun e => word K e.val)) ∧
      WordsAt out pp (parityNodeWords (rangeWords W n)) ∧
      Within code h (initialRegisters [.pointer ep, .pointer ip, .pointer np, .pointer op])
        (code d.self) [.pointer tp, .pointer rp, .pointer pp] out (budget W m n) := by
  obtain ⟨htab, hpi, hpairs, hni, hnodes, hself⟩ := hm
  let yw : Fin m → Bits K := fun e => word K e.val
  have hy : WordsAt h ip ((List.finRange m).map yw) := hi
  obtain ⟨H1, recp, e1, v1, hrec, zrun⟩ := records_compiled code d.table.edge htab.1 left right yw
    hh he hy
  obtain ⟨H2, prp, e2, v2, hprec, prun⟩ := RegisterListFlatMap.compiled code d.pairs d.pairItem
    hpairs RecordAt (fun _ _ (_ : Unit) => True) (fun h p l => RecordsAt h p l)
    (fun he _ _ hx => hx.mono he) (fun _ _ _ _ => trivial) (fun _ r => parityPair r) 110
    (fun hv _ _ _ _ _ _ hx _ ht => pairItem_compiled code d.pairItem hpi hv hx ht)
    v1 hrec (dataPtr := 0) (data := ()) trivial
    (RegisterListCommon.listRep_null (R := RecordAt) v1 : RecordsAt H1 0 ([] : List (Record (W + 1) K)))
  rw [List.append_nil] at hprec
  obtain ⟨H3, pnp, e3, v3, hpn, nrun⟩ := RegisterListFlatMap.compiled code d.nodes d.nodeItem
    hnodes (fun h p (x : Bits W) => BitsAt h p x) (fun _ _ (_ : Unit) => True)
    (fun h p l => WordsAt h p l)
    (fun he _ _ hx => hx.mono he) (fun _ _ _ _ => trivial)
    (fun _ v => [parityWord false v, parityWord true v]) 40
    (fun hv _ _ _ _ _ _ hx _ ht => nodeItem_compiled code d.nodeItem hni hv hx ht)
    v2 ((hn.mono e1).mono e2) (dataPtr := 0) (data := ()) trivial
    (WordsAt.nil v2.1 : WordsAt H2 0 ([] : List (Bits (W + 1))))
  rw [List.append_nil] at hpn
  obtain ⟨H4, tp, e4, v4, htable, trun⟩ := RegisterAdjacencyTable.compiled code d.table htab v3
    hpn (hprec.mono e3) (((ho.mono e1).mono e2).mono e3)
  refine ⟨H4, tp, recp, pnp, e1.trans (e2.trans (e3.trans e4)), v4, htable,
    ((hrec.mono e2).mono e3).mono e4, hpn.mono e4, ?_⟩
  let regs := initialRegisters [Value.pointer ep, .pointer ip, .pointer np, .pointer op]
  let s1 := bindResults regs [4] [.pointer recp]
  let s2 := bindResults s1 [5] [.pointer prp]
  let s3 := bindResults s2 [6] [.pointer pnp]
  let s4 := bindResults s3 [7] [.pointer tp]
  have last : Within code H4 s4 (.ret [.register 7, .register 4, .register 6])
      [.pointer tp, .pointer recp, .pointer pnp] H4 7 := by
    simpa [s4, s3, s2, s1, bindResults, values, Atom.eval] using
      Within.ret code H4 s4 [.register 7, .register 4, .register 6]
  have targs : values s3 [.register 6, .register 5, .register 3] =
      [.pointer pnp, .pointer prp, .pointer op] := by
    simp [s3, s2, s1, regs, bindResults, initialRegisters, values, Atom.eval]
  have tcall := Within.call (procedure := d.table.self) (regs := s3)
    (arguments := [.register 6, .register 5, .register 3]) (results := [7])
    (by simpa only [targs] using trun) last
  have nargs : values s2 [.register 2, .null, .null] =
      [.pointer np, .pointer 0, .pointer 0] := by
    simp [s2, s1, regs, bindResults, initialRegisters, values, Atom.eval]
  have ncall := Within.call (procedure := d.nodes) (regs := s2)
    (arguments := [.register 2, .null, .null]) (results := [6])
    (by simpa only [nargs] using nrun) tcall
  have pargs : values s1 [.register 4, .null, .null] =
      [.pointer recp, .pointer 0, .pointer 0] := by
    simp [s1, regs, bindResults, values, Atom.eval]
  have pcall := Within.call (procedure := d.pairs) (regs := s1)
    (arguments := [.register 4, .null, .null]) (results := [5])
    (by simpa only [pargs] using prun) ncall
  have zargs : values regs [.register 0, .register 1, .null] =
      [.pointer ep, .pointer ip, .pointer 0] := by
    simp [regs, initialRegisters, values, Atom.eval]
  have zcall := Within.call (procedure := d.table.edge.zip) (regs := regs)
    (arguments := [.register 0, .register 1, .null]) (results := [4])
    (by simpa only [zargs] using zrun) pcall
  rw [hself]
  refine zcall.mono ?_
  have hrl : (records W left right yw).length = m := by simp [records]
  have hprl := parityRecords_length (records W left right yw)
  have hpnl := parityNodeWords_length' (rangeWords W n)
  have hnl : (rangeWords W n).length = n := by simp [rangeWords]
  simp only [parityRecords] at hprl
  simp only [parityNodeWords] at hpnl
  simp only [budget, List.length_cons, List.length_nil, hrl, hnl, hprl, hpnl]
  omega

end WeightedMIS.RegisterParityTable
