module

public import WeightedMIS.NetworkWords
public import WeightedMIS.RegisterNetworkWeights
public import WeightedMIS.RegisterListZip
public import WeightedMIS.RegisterListFlatMap

/-!
# Register construction of the network node records

From the vertex words, the scaled weight words and a zero word of the capacity
width, the procedure builds the list of node records of
`NetworkWords.nodes n = MaxFlowPreprocessing.networkNodes (List.finRange n)`.
A node record is a `pair` cell holding the node word and the scaled weight of the
underlying vertex (the zero word for the terminals). The vertex words are
shared; each node word adds two tag cells in front of them. The terminal words
are built in front of the zero vertex word obtained from the first vertex word.

A second procedure projects the record list to the list of node words, the
vertex list expected by the maximum-flow solver.
-/

@[expose] public section

namespace WeightedMIS.RegisterNetworkNodes

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords
open WeightedMIS.DoubleCoverNetwork WeightedMIS.GraphReachEncoded WeightedMIS.NetworkWords
open WeightedMIS.RegisterNetworkWeights (allocate_fits pair_fits cons_fits bit_fits null_lt)

/-! ## Representations -/

theorem listRep_map {α β : Type*} {R : Heap → Ptr → β → Prop} {h : Heap} {p : Ptr}
    {f : α → β} {xs : List α} :
    ListRep R h p (xs.map f) ↔ ListRep (fun h p x => R h p (f x)) h p xs := by
  constructor
  · rintro ⟨ptrs, hl, hr⟩
    exact ⟨ptrs, hl, List.forall₂_map_right_iff.mp hr⟩
  · rintro ⟨ptrs, hl, hr⟩
    exact ⟨ptrs, hl, List.forall₂_map_right_iff.mpr hr⟩

theorem lt_of_ext {h h' : Heap} (he : Extends h h') {b : Ptr} (hb : b < h.length) :
    b < h'.length :=
  lt_of_lt_of_le hb he.length_le

theorem flatMap_single {α β : Type*} (f : α → β) (l : List α) :
    l.flatMap (fun x => [f x]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem mem_zip_self {α : Type*} {l : List α} {a b : α} (h : (a, b) ∈ l.zip l) : a = b := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · rfl
    · exact ih h

variable {n B : ℕ}

/-- A vertex with its scaled weight: `pair vertexWord weightWord`. -/
def VertexAt (W : ℕ) (muw : Fin n → Bits B) (h : Heap) (p : Ptr) (v : Fin n) : Prop :=
  ∃ a b, h[p]? = some (.pair a b) ∧ BitsAt h a (word W v.val) ∧ BitsAt h b (muw v)

/-- A network node record: `pair nodeWord weightWord`. -/
def NodeAt (W : ℕ) (muw : Fin n → Bits B) (zero : Bits B) (h : Heap) (p : Ptr)
    (u : Node (Fin n)) : Prop :=
  ∃ a b, h[p]? = some (.pair a b) ∧ BitsAt h a (nodeWord W u) ∧ BitsAt h b (muOf muw zero u)

theorem VertexAt.mono {W : ℕ} {muw : Fin n → Bits B} {h h' : Heap} (he : Extends h h')
    {p : Ptr} {v : Fin n} (hv : VertexAt W muw h p v) : VertexAt W muw h' p v := by
  obtain ⟨a, b, c, ha, hb⟩ := hv
  exact ⟨a, b, he.lookup c, ha.mono he, hb.mono he⟩

theorem NodeAt.mono {W : ℕ} {muw : Fin n → Bits B} {zero : Bits B} {h h' : Heap}
    (he : Extends h h') {p : Ptr} {u : Node (Fin n)} (hu : NodeAt W muw zero h p u) :
    NodeAt W muw zero h' p u := by
  obtain ⟨a, b, c, ha, hb⟩ := hu
  exact ⟨a, b, he.lookup c, ha.mono he, hb.mono he⟩

theorem NodeAt.allocated {W : ℕ} {muw : Fin n → Bits B} {zero : Bits B} {h : Heap} {p : Ptr}
    {u : Node (Fin n)} (hu : NodeAt W muw zero h p u) : p < h.length := by
  obtain ⟨a, b, c, -⟩ := hu
  exact (List.getElem?_eq_some_iff.mp c).1

/-- The stored list of node records. -/
abbrev NodesAt (W : ℕ) (muw : Fin n → Bits B) (zero : Bits B) (h : Heap) (p : Ptr)
    (us : List (Node (Fin n))) : Prop :=
  ListRep (NodeAt W muw zero) h p us

theorem NodesAt.mono {W : ℕ} {muw : Fin n → Bits B} {zero : Bits B} {h h' : Heap}
    (he : Extends h h') {p : Ptr} {us : List (Node (Fin n))}
    (hu : NodesAt W muw zero h p us) : NodesAt W muw zero h' p us :=
  ListRep.mono he (fun _ _ hx => hx.mono he) hu

/-! ## Procedures -/

structure Procedures (p : ℕ) where
  zero : Fin p
  pairItem : Fin p
  zip : Fin p
  leftItem : Fin p
  left : Fin p
  rightItem : Fin p
  right : Fin p
  wordItem : Fin p
  words : Fin p
  self : Fin p

variable {p : ℕ}

/-- Arguments: vertex word, weight word, unused data. -/
def pairItemBody : Command p :=
  .allocate 3 (.pair (.register 0) (.register 1)) (.ret [.register 3])

/-- Arguments: vertex record, unused data, accumulator. Prepends the record of
the vertex copy on the given side. -/
def nodeItemBody (side : Bool) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    pair := .allocate 5 (.bit (.flag side) (.register 3))
      (.allocate 6 (.bit (.flag true) (.register 5))
        (.allocate 7 (.pair (.register 6) (.register 4))
          (.allocate 8 (.cons (.register 7) (.register 2)) (.ret [.register 8])))) }

/-- Arguments: node record, unused data. Returns the node word. -/
def wordItemBody : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with pair := .ret [.register 2] }

/-- Arguments: vertex words, weight words, zero weight word. Results: node
records, source word, sink word. -/
def nodesBody (zero zip left right : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    cons := .call zero [.register 3] [5]
      (.call zip [.register 0, .register 1, .null] [6]
        (.call right [.register 6, .null, .null] [7]
          (.call left [.register 6, .null, .register 7] [8]
            (.allocate 9 (.bit (.flag false) (.register 5))
              (.allocate 10 (.bit (.flag false) (.register 9))
                (.allocate 11 (.bit (.flag true) (.register 5))
                  (.allocate 12 (.bit (.flag false) (.register 11))
                    (.allocate 13 (.pair (.register 10) (.register 2))
                      (.allocate 14 (.pair (.register 12) (.register 2))
                        (.allocate 15 (.cons (.register 14) (.register 8))
                          (.allocate 4 (.cons (.register 13) (.register 15))
                            (.ret [.register 4, .register 10, .register 12])))))))))))) }

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  code d.zero = RegisterZero.zeroBody d.zero ∧
  code d.pairItem = pairItemBody ∧
  code d.zip = RegisterListZip.body d.zip d.pairItem ∧
  code d.leftItem = nodeItemBody false ∧
  code d.left = RegisterListFlatMap.body d.left d.leftItem ∧
  code d.rightItem = nodeItemBody true ∧
  code d.right = RegisterListFlatMap.body d.right d.rightItem ∧
  code d.wordItem = wordItemBody ∧
  code d.words = RegisterListMap.body d.words d.wordItem ∧
  code d.self = nodesBody d.zero d.zip d.left d.right

/-! ## Items -/

theorem pairItem_compiled (code : Code p) (item : Fin p) (hitem : code item = pairItemBody)
    {W : ℕ} {muw : Fin n → Bits B} {h : Heap} (hh : Valid h) {ap bp dp : Ptr} {v : Fin n}
    (ha : BitsAt h ap (word W v.val)) (hb : BitsAt h bp (muw v)) :
    ∃ out q, Extends h out ∧ Valid out ∧ VertexAt W muw out q v ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp, .pointer dp])
        (code item) [.pointer q] out 11 := by
  obtain ⟨e, v1, c⟩ := allocate_fits hh (pair_fits ha.allocated hb.allocated)
  refine ⟨_, h.length, e, v1, ⟨ap, bp, c, ha.mono e, hb.mono e⟩, ?_⟩
  let regs := initialRegisters [Value.pointer ap, .pointer bp, .pointer dp]
  have last := Within.ret code (h ++ [.pair ap bp]) (Function.update regs 3 (.pointer h.length))
    [.register 3]
  have al := Within.allocate (regs := regs) (dst := 3) (h := h)
    (expr := .pair (.register 0) (.register 1)) (c := .pair ap bp)
    (by simp [CellExpr.eval, Atom.eval, regs, initialRegisters, Value.asPointer])
    (by simpa [values, Atom.eval] using last)
  rw [hitem]
  exact al.mono (by simp [CellExpr.args])

theorem nodeItem_compiled (code : Code p) (item : Fin p) (side : Bool)
    (hitem : code item = nodeItemBody side)
    {W : ℕ} {muw : Fin n → Bits B} {zero : Bits B} {h : Heap} (hh : Valid h)
    {vp dp acc : Ptr} {v : Fin n} {tail : List (Node (Fin n))}
    (hv : VertexAt W muw h vp v) (ht : NodesAt W muw zero h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧
      NodesAt W muw zero out q ([(Sum.inr (side, v) : Node (Fin n))] ++ tail) ∧
      Within code h (initialRegisters [.pointer vp, .pointer dp, .pointer acc])
        (code item) [.pointer q] out 45 := by
  obtain ⟨a, b, cell, ha, hb⟩ := hv
  let H1 := h ++ [Cell.bit side a]
  let H2 := H1 ++ [Cell.bit true h.length]
  let H3 := H2 ++ [Cell.pair H1.length b]
  let H4 := H3 ++ [Cell.cons H2.length acc]
  obtain ⟨e1, v1, c1⟩ := allocate_fits hh (bit_fits (b := side) ha.allocated)
  obtain ⟨e2, v2, c2⟩ := allocate_fits v1 (bit_fits (b := true) (h := H1) (a := h.length)
    (by simp [H1]))
  obtain ⟨e3, v3, c3⟩ := allocate_fits v2 (pair_fits (h := H2) (a := H1.length) (b := b)
    (by simp [H2, H1]) (lt_of_ext (e1.trans e2) hb.allocated))
  obtain ⟨e4, v4, c4⟩ := allocate_fits v3 (cons_fits (h := H3) (a := H2.length) (b := acc)
    (by simp [H3, H2]) (lt_of_ext (e1.trans (e2.trans e3)) ht.allocated))
  have hword : BitsAt H3 H1.length (nodeWord W (Sum.inr (side, v) : Node (Fin n))) :=
    .cons (e3.lookup c2) (.cons (e2.trans e3 |>.lookup c1) (ha.mono (e1.trans (e2.trans e3))))
  have hrec : NodeAt W muw zero H3 H2.length (Sum.inr (side, v)) :=
    ⟨H1.length, b, c3, hword, hb.mono (e1.trans (e2.trans e3))⟩
  have hlist : NodesAt W muw zero H4 H3.length ([(Sum.inr (side, v) : Node (Fin n))] ++ tail) := by
    obtain ⟨ptrs, hl, hr⟩ := ht
    exact ⟨H2.length :: ptrs, .cons c4 (hl.mono (e1.trans (e2.trans (e3.trans e4)))),
      .cons (hrec.mono e4) (hr.imp fun _ _ hx => hx.mono (e1.trans (e2.trans (e3.trans e4))))⟩
  refine ⟨H4, H3.length, e1.trans (e2.trans (e3.trans e4)), v4, hlist, ?_⟩
  let regs := initialRegisters [Value.pointer vp, .pointer dp, .pointer acc]
  let r1 := loadRegisters regs 3 4 15 (.pair a b)
  let r2 := Function.update r1 5 (.pointer h.length)
  let r3 := Function.update r2 6 (.pointer H1.length)
  let r4 := Function.update r3 7 (.pointer H2.length)
  let r5 := Function.update r4 8 (.pointer H3.length)
  have last : Within code H4 r5 (.ret [.register 8]) [.pointer H3.length] H4 3 := by
    simpa [values, Atom.eval, r5] using Within.ret code H4 r5 [.register 8]
  have a8 := Within.allocate (regs := r4) (dst := 8) (h := H3)
    (expr := .cons (.register 7) (.register 2)) (c := .cons H2.length acc)
    (by simp [CellExpr.eval, Atom.eval, r4, r3, r2, r1, regs, loadRegisters, decoded,
      initialRegisters, Value.asPointer]) last
  have a7 := Within.allocate (regs := r3) (dst := 7) (h := H2)
    (expr := .pair (.register 6) (.register 4)) (c := .pair H1.length b)
    (by simp [CellExpr.eval, Atom.eval, r3, r2, r1, loadRegisters, decoded, Value.asPointer]) a8
  have a6 := Within.allocate (regs := r2) (dst := 6) (h := H1)
    (expr := .bit (.flag true) (.register 5)) (c := .bit true h.length)
    (by simp [CellExpr.eval, Atom.eval, r2, Value.asPointer, Value.asFlag]) a7
  have a5 := Within.allocate (regs := r1) (dst := 5) (h := h)
    (expr := .bit (.flag side) (.register 3)) (c := .bit side a)
    (by simp [CellExpr.eval, Atom.eval, r1, loadRegisters, decoded, Value.asPointer,
      Value.asFlag]) a6
  have l := Within.load (regs := regs) (address := .register 0) (first := 3) (second := 4)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .allocate 5 (.bit (.flag side) (.register 3))
        (.allocate 6 (.bit (.flag true) (.register 5))
          (.allocate 7 (.pair (.register 6) (.register 4))
            (.allocate 8 (.cons (.register 7) (.register 2)) (.ret [.register 8])))) })
    (by simp [Atom.eval, regs, initialRegisters]) cell a5
  rw [hitem]
  exact l.mono (by simp [CellExpr.args])

theorem wordItem_compiled (code : Code p) (item : Fin p) (hitem : code item = wordItemBody)
    {W : ℕ} {muw : Fin n → Bits B} {zero : Bits B} {h : Heap} (hh : Valid h)
    {rp dp : Ptr} {u : Node (Fin n)} (hu : NodeAt W muw zero h rp u) :
    ∃ out q, Extends h out ∧ Valid out ∧ BitsAt out q (nodeWord W u) ∧
      Within code h (initialRegisters [.pointer rp, .pointer dp]) (code item) [.pointer q] out 13 := by
  obtain ⟨a, b, cell, ha, hb⟩ := hu
  refine ⟨h, a, .refl h, hh, ha, ?_⟩
  let regs := initialRegisters [Value.pointer rp, .pointer dp]
  have last := Within.ret code h (loadRegisters regs 2 3 15 (.pair a b)) [.register 2]
  have l := Within.load (regs := regs) (address := .register 0) (first := 2) (second := 3)
    (bit := 15) (branches := { CompiledTrie.failCases with pair := .ret [.register 2] })
    (by simp [Atom.eval, regs, initialRegisters]) cell
    (by simpa [values, Atom.eval, loadRegisters, decoded, Cases.select] using last)
  rw [hitem]
  exact l

/-! ## Node words of a record list -/

theorem words_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {W : ℕ} {muw : Fin n → Bits B} {zero : Bits B} {h : Heap} (hh : Valid h)
    {rp : Ptr} {us : List (Node (Fin n))} (hu : NodesAt W muw zero h rp us) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (us.map (nodeWord W)) ∧
      Within code h (initialRegisters [.pointer rp, .pointer 0]) (code d.words) [.pointer q] out
        (48 * us.length + 13) := by
  obtain ⟨out, q, he, hv, hq, run⟩ := RegisterListMap.compiled_const code d.words d.wordItem
    hm.2.2.2.2.2.2.2.2.1 (NodeAt W muw zero) (fun _ _ (_ : Unit) => True)
    (fun h p (x : Bits (W + 2)) => BitsAt h p x)
    (fun he _ _ hx => hx.mono he) (fun _ _ _ _ => trivial) (fun he _ _ hx => hx.mono he)
    (fun _ hx => hx.allocated) (fun _ u => nodeWord W u) 13 (dataPtr := 0) (data := ())
    hh hu trivial (fun hv _ _ _ hx _ => wordItem_compiled code d.wordItem hm.2.2.2.2.2.2.2.1 hv hx)
  exact ⟨out, q, he, hv, hq, run.mono (by omega)⟩

/-! ## The node record list -/

def budget (W n : ℕ) : ℕ := 24 * W + 200 * n + 300

theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {W : ℕ} (hn : 0 < n) (muw : Fin n → Bits B) (zero : Bits B)
    {h : Heap} (hh : Valid h) {vp mp zp : Ptr}
    (hv : WordsAt h vp (rangeWords W n)) (hmu : WordsAt h mp ((List.finRange n).map muw))
    (hz : BitsAt h zp zero) :
    ∃ out rp sp tp, Extends h out ∧ Valid out ∧ NodesAt W muw zero out rp (nodes n) ∧
      BitsAt out sp (nodeWord W (sourceNode : Node (Fin n))) ∧
      BitsAt out tp (nodeWord W (sinkNode : Node (Fin n))) ∧
      Within code h (initialRegisters [.pointer vp, .pointer mp, .pointer zp]) (code d.self)
        [.pointer rp, .pointer sp, .pointer tp] out (budget W n) := by
  obtain ⟨hzero, hpair, hzip, hlitem, hleft, hritem, hright, -, -, hself⟩ := hm
  -- the first vertex word
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨x0, rest, cell0, hx0⟩ : ∃ x0 rest, h[vp]? = some (.cons x0 rest) ∧
      BitsAt h x0 (word W 0) := by
    obtain ⟨ptrs, hl, hr⟩ := hv
    rw [rangeWords, List.finRange_succ, List.map_cons] at hr
    cases hr with
    | cons hhead _ =>
      cases hl with
      | cons cell _ => exact ⟨_, _, cell, hhead⟩
  obtain ⟨h1, zW, e1, v1, hzW, -, zeroRun⟩ := RegisterZero.compiled code d.zero hzero hh hx0
  -- vertex records
  have hvl : ListRep (fun h p (v : Fin (k + 1)) => BitsAt h p (word W v.val)) h vp
      (List.finRange (k + 1)) := listRep_map.mp hv
  have hml : ListRep (fun h p (v : Fin (k + 1)) => BitsAt h p (muw v)) h mp
      (List.finRange (k + 1)) := listRep_map.mp hmu
  obtain ⟨h2, vr, e2, v2, hvr, zipRun⟩ := RegisterListZip.compiled_const code d.zip d.pairItem
    hzip (fun h p (v : Fin (k + 1)) => BitsAt h p (word W v.val))
    (fun h p (v : Fin (k + 1)) => BitsAt h p (muw v)) (fun _ _ (_ : Unit) => True)
    (VertexAt W muw) (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he)
    (fun _ _ _ _ => trivial) (fun he _ _ hx => hx.mono he)
    (fun _ hx => by obtain ⟨_, _, c, -⟩ := hx; exact (List.getElem?_eq_some_iff.mp c).1)
    (fun _ a _ => a) 11 (dataPtr := 0) (data := ()) v1 (hvl.mono e1 (fun _ _ hx => hx.mono e1))
    (hml.mono e1 (fun _ _ hx => hx.mono e1)) trivial
    (fun hv' _ _ _ _ hmem ha hb _ => by
      have := mem_zip_self hmem
      subst this
      exact pairItem_compiled code d.pairItem hpair hv' ha hb)
  have hzipEq : List.zipWith (fun a (_ : Fin (k + 1)) => a) (List.finRange (k + 1))
      (List.finRange (k + 1)) = List.finRange (k + 1) := by
    simp [List.zipWith_self]
  rw [hzipEq] at hvr
  simp only [List.length_finRange, min_self] at zipRun
  -- right and left copies
  have hnil : NodesAt W muw zero h2 0 [] := RegisterListCommon.listRep_null v2
  obtain ⟨h3, rr, e3, v3, hrr, rightRun⟩ := RegisterListFlatMap.compiled code d.right
    d.rightItem hright (VertexAt W muw) (fun _ _ (_ : Unit) => True) (NodesAt W muw zero)
    (fun he _ _ hx => hx.mono he) (fun _ _ _ _ => trivial)
    (fun _ v => [(Sum.inr (true, v) : Node (Fin (k + 1)))]) 45
    (fun hv' _ _ _ _ _ _ hx _ ht => nodeItem_compiled code d.rightItem true hritem hv' hx ht)
    (dataPtr := 0) (data := ()) v2 hvr trivial hnil
  obtain ⟨h4, lr, e4, v4, hlr, leftRun⟩ := RegisterListFlatMap.compiled code d.left
    d.leftItem hleft (VertexAt W muw) (fun _ _ (_ : Unit) => True) (NodesAt W muw zero)
    (fun he _ _ hx => hx.mono he) (fun _ _ _ _ => trivial)
    (fun _ v => [(Sum.inr (false, v) : Node (Fin (k + 1)))]) 45
    (fun hv' _ _ _ _ _ _ hx _ ht => nodeItem_compiled code d.leftItem false hlitem hv' hx ht)
    (dataPtr := 0) (data := ()) v3 (hvr.mono e3 (fun _ _ hx => hx.mono e3)) trivial hrr
  simp only [List.length_finRange] at rightRun leftRun
  -- terminal words and records
  have e14 := e1.trans (e2.trans (e3.trans e4))
  have hzW4 := hzW.mono (e2.trans (e3.trans e4))
  have hz4 := hz.mono e14
  let H1 := h4 ++ [Cell.bit false zW]
  let H2 := H1 ++ [Cell.bit false h4.length]
  let H3 := H2 ++ [Cell.bit true zW]
  let H4 := H3 ++ [Cell.bit false H2.length]
  let H5 := H4 ++ [Cell.pair H1.length zp]
  let H6 := H5 ++ [Cell.pair H3.length zp]
  let H7 := H6 ++ [Cell.cons H5.length lr]
  let H8 := H7 ++ [Cell.cons H4.length H6.length]
  obtain ⟨f1, w1, c1⟩ := allocate_fits v4 (bit_fits (b := false) hzW4.allocated)
  obtain ⟨f2, w2, c2⟩ := allocate_fits w1 (bit_fits (b := false) (h := H1) (a := h4.length)
    (by simp [H1]))
  obtain ⟨f3, w3, c3⟩ := allocate_fits w2 (bit_fits (b := true) (h := H2) (a := zW)
    (lt_of_ext (f1.trans f2) hzW4.allocated))
  obtain ⟨f4, w4, c4⟩ := allocate_fits w3 (bit_fits (b := false) (h := H3) (a := H2.length)
    (by simp [H3]))
  obtain ⟨f5, w5, c5⟩ := allocate_fits w4 (pair_fits (h := H4) (a := H1.length) (b := zp)
    (by simp [H4, H3, H2]) (lt_of_ext (f1.trans (f2.trans (f3.trans f4))) hz4.allocated))
  obtain ⟨f6, w6, c6⟩ := allocate_fits w5 (pair_fits (h := H5) (a := H3.length) (b := zp)
    (by simp [H5, H4]) (lt_of_ext (f1.trans (f2.trans (f3.trans (f4.trans f5)))) hz4.allocated))
  obtain ⟨f7, w7, c7⟩ := allocate_fits w6 (cons_fits (h := H6) (a := H5.length) (b := lr)
    (by simp [H6])
    (lt_of_ext (f1.trans (f2.trans (f3.trans (f4.trans (f5.trans f6))))) hlr.allocated))
  obtain ⟨f8, w8, c8⟩ := allocate_fits w7 (cons_fits (h := H7) (a := H4.length) (b := H6.length)
    (by simp [H7, H6, H5]) (by simp [H7]))
  have g28 := f2.trans (f3.trans (f4.trans (f5.trans (f6.trans (f7.trans f8)))))
  have g48 := f4.trans (f5.trans (f6.trans (f7.trans f8)))
  have hs : BitsAt H2 H1.length (nodeWord W (sourceNode : Node (Fin (k + 1)))) :=
    .cons c2 (.cons (f2.lookup c1) (hzW4.mono (f1.trans f2)))
  have ht : BitsAt H4 H3.length (nodeWord W (sinkNode : Node (Fin (k + 1)))) :=
    .cons c4 (.cons (f4.lookup c3) (hzW4.mono (f1.trans (f2.trans (f3.trans f4)))))
  have hsrec : NodeAt W muw zero H5 H4.length (sourceNode : Node (Fin (k + 1))) :=
    ⟨H1.length, zp, c5, hs.mono (f3.trans (f4.trans f5)),
      hz4.mono (f1.trans (f2.trans (f3.trans (f4.trans f5))))⟩
  have htrec : NodeAt W muw zero H6 H5.length (sinkNode : Node (Fin (k + 1))) :=
    ⟨H3.length, zp, c6, ht.mono (f5.trans f6),
      hz4.mono (f1.trans (f2.trans (f3.trans (f4.trans (f5.trans f6)))))⟩
  have hlist : NodesAt W muw zero H8 H7.length (nodes (k + 1)) := by
    rw [nodes_eq]
    obtain ⟨ptrs, hl, hr⟩ := hlr
    have hl' : ListAt H8 H7.length (H4.length :: H5.length :: ptrs) :=
      .cons c8 (.cons (f8.lookup c7) (hl.mono (f1.trans g28)))
    refine ⟨_, hl', .cons (hsrec.mono (f6.trans (f7.trans f8)))
      (.cons (htrec.mono (f7.trans f8)) ?_)⟩
    have hr' := hr.imp (fun _ _ hx => hx.mono (f1.trans g28))
    rw [List.append_nil, flatMap_single, flatMap_single] at hr'
    exact hr'
  refine ⟨H8, H7.length, H1.length, H3.length, e14.trans (f1.trans g28), w8, hlist,
    hs.mono (f3.trans g48), ht.mono (f5.trans (f6.trans (f7.trans f8))), ?_⟩
  -- the derivation
  let r0 := initialRegisters [Value.pointer vp, .pointer mp, .pointer zp]
  let r1 := loadRegisters r0 3 4 15 (.cons x0 rest)
  let r2 := bindResults r1 [5] [.pointer zW]
  let r3 := bindResults r2 [6] [.pointer vr]
  let r4 := bindResults r3 [7] [.pointer rr]
  let r5 := bindResults r4 [8] [.pointer lr]
  let r6 := Function.update r5 9 (.pointer h4.length)
  let r7 := Function.update r6 10 (.pointer H1.length)
  let r8 := Function.update r7 11 (.pointer H2.length)
  let r9 := Function.update r8 12 (.pointer H3.length)
  let r10 := Function.update r9 13 (.pointer H4.length)
  let r11 := Function.update r10 14 (.pointer H5.length)
  let r12 := Function.update r11 15 (.pointer H6.length)
  let r13 := Function.update r12 4 (.pointer H7.length)
  have last : Within code H8 r13 (.ret [.register 4, .register 10, .register 12])
      [.pointer H7.length, .pointer H1.length, .pointer H3.length] H8 7 := by
    simpa [values, Atom.eval, r13, r12, r11, r10, r9, r8, r7] using
      Within.ret code H8 r13 [.register 4, .register 10, .register 12]
  have a4 := Within.allocate (regs := r12) (dst := 4) (h := H7)
    (expr := .cons (.register 13) (.register 15)) (c := .cons H4.length H6.length)
    (by simp [CellExpr.eval, Atom.eval, r12, r11, r10, Value.asPointer]) last
  have a15 := Within.allocate (regs := r11) (dst := 15) (h := H6)
    (expr := .cons (.register 14) (.register 8)) (c := .cons H5.length lr)
    (by simp [CellExpr.eval, Atom.eval, r11, r10, r9, r8, r7, r6, r5, bindResults,
      Value.asPointer]) a4
  have a14 := Within.allocate (regs := r10) (dst := 14) (h := H5)
    (expr := .pair (.register 12) (.register 2)) (c := .pair H3.length zp)
    (by simp [CellExpr.eval, Atom.eval, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, r0,
      bindResults, loadRegisters, decoded, initialRegisters, Value.asPointer]) a15
  have a13 := Within.allocate (regs := r9) (dst := 13) (h := H4)
    (expr := .pair (.register 10) (.register 2)) (c := .pair H1.length zp)
    (by simp [CellExpr.eval, Atom.eval, r9, r8, r7, r6, r5, r4, r3, r2, r1, r0,
      bindResults, loadRegisters, decoded, initialRegisters, Value.asPointer]) a14
  have a12 := Within.allocate (regs := r8) (dst := 12) (h := H3)
    (expr := .bit (.flag false) (.register 11)) (c := .bit false H2.length)
    (by simp [CellExpr.eval, Atom.eval, r8, Value.asPointer, Value.asFlag]) a13
  have a11 := Within.allocate (regs := r7) (dst := 11) (h := H2)
    (expr := .bit (.flag true) (.register 5)) (c := .bit true zW)
    (by simp [CellExpr.eval, Atom.eval, r7, r6, r5, r4, r3, r2, bindResults, Value.asPointer,
      Value.asFlag]) a12
  have a10 := Within.allocate (regs := r6) (dst := 10) (h := H1)
    (expr := .bit (.flag false) (.register 9)) (c := .bit false h4.length)
    (by simp [CellExpr.eval, Atom.eval, r6, Value.asPointer, Value.asFlag]) a11
  have a9 := Within.allocate (regs := r5) (dst := 9) (h := h4)
    (expr := .bit (.flag false) (.register 5)) (c := .bit false zW)
    (by simp [CellExpr.eval, Atom.eval, r5, r4, r3, r2, bindResults, Value.asPointer,
      Value.asFlag]) a10
  have aL : values r4 [.register 6, .null, .register 7] = [.pointer vr, .pointer 0, .pointer rr] := by
    simp [values, Atom.eval, r4, r3, bindResults]
  have cL := Within.call (procedure := d.left) (regs := r4)
    (arguments := [.register 6, .null, .register 7]) (results := [8])
    (by simpa only [aL] using leftRun) a9
  have aR : values r3 [.register 6, .null, .null] = [.pointer vr, .pointer 0, .pointer 0] := by
    simp [values, Atom.eval, r3, bindResults]
  have cR := Within.call (procedure := d.right) (regs := r3)
    (arguments := [.register 6, .null, .null]) (results := [7])
    (by simpa only [aR] using rightRun) cL
  have aZ : values r2 [.register 0, .register 1, .null] =
      [.pointer vp, .pointer mp, .pointer 0] := by
    simp [values, Atom.eval, r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters]
  have cZ := Within.call (procedure := d.zip) (regs := r2)
    (arguments := [.register 0, .register 1, .null]) (results := [6])
    (by simpa only [aZ] using zipRun) cR
  have a0 : values r1 [.register 3] = [.pointer x0] := by
    simp [values, Atom.eval, r1, loadRegisters, decoded]
  have c0 := Within.call (procedure := d.zero) (regs := r1)
    (arguments := [.register 3]) (results := [5]) (by simpa only [a0] using zeroRun) cZ
  have l := Within.load (regs := r0) (address := .register 0) (first := 3) (second := 4)
    (bit := 15) (branches := { CompiledTrie.failCases with
      cons := .call d.zero [.register 3] [5]
        (.call d.zip [.register 0, .register 1, .null] [6]
          (.call d.right [.register 6, .null, .null] [7]
            (.call d.left [.register 6, .null, .register 7] [8]
              (.allocate 9 (.bit (.flag false) (.register 5))
                (.allocate 10 (.bit (.flag false) (.register 9))
                  (.allocate 11 (.bit (.flag true) (.register 5))
                    (.allocate 12 (.bit (.flag false) (.register 11))
                      (.allocate 13 (.pair (.register 10) (.register 2))
                        (.allocate 14 (.pair (.register 12) (.register 2))
                          (.allocate 15 (.cons (.register 14) (.register 8))
                            (.allocate 4 (.cons (.register 13) (.register 15))
                              (.ret [.register 4, .register 10, .register 12])))))))))))) })
    (by simp [Atom.eval, r0, initialRegisters]) cell0 c0
  rw [hself]
  exact l.mono (by simp [CellExpr.args, budget]; omega)

end WeightedMIS.RegisterNetworkNodes
