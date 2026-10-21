module

public import WeightedMIS.RibbonTable
public import WeightedMIS.GraphReachEncoded
public import WeightedMIS.RegisterFlagKeys
public import WeightedMIS.RegisterListFlatMap
public import WeightedMIS.RegisterListCommon

/-!
# Search tables of stored ribbon tables

The endpoint words of the records of a ribbon table are the endpoint words of
its edges. A flat-map over the records reads the two shared endpoint words of
each record and prepends two unit-capacity arcs (adjacency) or four parity
arcs; the parity copies of a word are single bit cells in front of the shared
word. A second flat-map lists both parity copies of every vertex word. The
results are exactly `GraphReachEncoded.adjArcs`, `GraphReachEncoded.parityArcs`
and `GraphReachEncoded.parityNodeWords` of the edge words of the ribbon.
-/

@[expose] public section

namespace WeightedMIS.RegisterGraphArcs

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys
open WeightedMIS.ExpandedWords WeightedMIS.ResidualWords
open WeightedMIS.GraphReachEncoded (one parityWord adjArcs parityArcs parityNodeWords edgeWords)

variable {p : ℕ}

/-! ## Reference -/

/-- Endpoint words of the records of a table, in record order. -/
def edgePairs {W : ℕ} (T : List (EdgeRec W)) : List (Bits W × Bits W) :=
  T.map (fun r => (r.left, r.right))

/-- The endpoint words of the table of a ribbon are the endpoint words of its edges. -/
theorem edgePairs_encode (W : ℕ) {n m : ℕ} {left right : Fin m → Fin n}
    (R : EmbeddingFaces.Ribbon left right) :
    edgePairs (encodeRibbon W R) = edgeWords W left right := by
  simp only [edgePairs, encodeRibbon, edgeWords, List.map_map]
  rfl

/-- The adjacency arcs contributed by one record. -/
def adjItem {W : ℕ} (r : EdgeRec W) : List (Arc W 1) :=
  [⟨r.left, r.right, one⟩, ⟨r.right, r.left, one⟩]

/-- The parity arcs contributed by one record. -/
def parityItem {W : ℕ} (r : EdgeRec W) : List (Arc (W + 1) 1) :=
  [⟨parityWord false r.left, parityWord true r.right, one⟩,
   ⟨parityWord true r.left, parityWord false r.right, one⟩,
   ⟨parityWord true r.right, parityWord false r.left, one⟩,
   ⟨parityWord false r.right, parityWord true r.left, one⟩]

theorem adjArcs_eq {W : ℕ} (T : List (EdgeRec W)) :
    adjArcs (edgePairs T) = T.flatMap adjItem := by
  simp only [adjArcs, edgePairs, List.flatMap_map]
  rfl

theorem parityArcs_eq {W : ℕ} (T : List (EdgeRec W)) :
    parityArcs (edgePairs T) = T.flatMap parityItem := by
  simp only [parityArcs, edgePairs, List.flatMap_map]
  rfl

/-! ## Allocation facts -/

/-- One allocated `cons` cell of allocated fields keeps the heap valid. -/
theorem alloc_cons {h : Heap} (hh : Valid h) {a b : Ptr} (ha : a < h.length)
    (hb : b < h.length) :
    Extends h (h ++ [.cons a b]) ∧ Valid (h ++ [.cons a b]) ∧
      (h ++ [.cons a b])[h.length]? = some (.cons a b) := by
  have hs := safe_allocate h hh (.cons a b) (by
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> assumption)
  refine ⟨hs.1, hs.2.1, ?_⟩
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- The unit word as one allocated bit cell. -/
theorem alloc_one {h : Heap} (hh : Valid h) :
    Extends h (h ++ [.bit true 0]) ∧ Valid (h ++ [.bit true 0]) ∧
      BitsAt (h ++ [.bit true 0]) h.length one :=
  alloc_bit hh true (BitsAt.nil hh.1)

/-! ## Prepending one arc -/

/-- Arguments 0 = source, 1 = target, 2 = capacity, 3 = arc list. -/
def arcBody : Command p :=
  .allocate 4 (.pair (.register 1) (.register 2))
    (.allocate 5 (.pair (.register 0) (.register 4))
      (.allocate 6 (.cons (.register 5) (.register 3)) (.ret [.register 6])))

theorem arc_compiled (code : Code p) (self : Fin p) (hself : code self = arcBody)
    {n b : ℕ} {h : Heap} (hh : Valid h) {sp tp cp lp : Ptr} {a : Arc n b} {as : List (Arc n b)}
    (hs : BitsAt h sp a.source) (ht : BitsAt h tp a.target) (hc : BitsAt h cp a.capacity)
    (hl : TableAt h lp as) :
    ∃ out q, Extends h out ∧ Valid out ∧ TableAt out q (a :: as) ∧
      Within code h (initialRegisters [.pointer sp, .pointer tp, .pointer cp, .pointer lp])
        (code self) [.pointer q] out 35 := by
  obtain ⟨e1, v1, c1⟩ := alloc_pair hh ht.allocated hc.allocated
  have hs1 : sp < (h ++ [Cell.pair tp cp]).length := lt_of_lt_of_le hs.allocated e1.length_le
  have hh1 : h.length < (h ++ [Cell.pair tp cp]).length := by simp
  obtain ⟨e2, v2, c2⟩ := alloc_pair v1 hs1 hh1
  have hl2 : lp < (h ++ [Cell.pair tp cp] ++ [Cell.pair sp h.length]).length :=
    lt_of_lt_of_le hl.allocated (e1.trans e2).length_le
  have hq2 : (h ++ [Cell.pair tp cp]).length <
      (h ++ [Cell.pair tp cp] ++ [Cell.pair sp h.length]).length := by simp
  obtain ⟨e3, v3, c3⟩ := alloc_cons v2 hq2 hl2
  set h3 := h ++ [Cell.pair tp cp] ++ [Cell.pair sp h.length] ++
    [Cell.cons (h ++ [Cell.pair tp cp]).length lp]
  have e13 := (e1.trans e2).trans e3
  have harc : ArcAt h3 (h ++ [Cell.pair tp cp]).length a :=
    ⟨sp, h.length, tp, cp, e3.lookup c2, (e2.trans e3).lookup c1, hs.mono e13, ht.mono e13,
      hc.mono e13⟩
  refine ⟨h3, (h ++ [Cell.pair tp cp] ++ [Cell.pair sp h.length]).length, e13, v3,
    TableAt.cons c3 harc (hl.mono e13), ?_⟩
  rw [hself]
  refine (Within.allocate (c := Cell.pair tp cp) (by reg_simp)
    (Within.allocate (c := Cell.pair sp h.length) (by reg_simp)
    (Within.allocate (c := Cell.cons (h ++ [Cell.pair tp cp]).length lp) (by reg_simp)
    (ret_values (by reg_simp) le_rfl)))).mono ?_
  simp [CellExpr.args]

/-! ## Record items -/

/-- Arguments 0 = record, 1 = unit word, 2 = arc list. -/
def adjItemBody (arc : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    pair := .load (.register 4) 5 6 15 { CompiledTrie.failCases with
      pair := .load (.register 6) 7 8 15 { CompiledTrie.failCases with
        pair := .call arc [.register 7, .register 5, .register 1, .register 2] [9]
          (.call arc [.register 5, .register 7, .register 1, .register 9] [10]
            (.ret [.register 10])) } } }

/-- Arguments 0 = record, 1 = unit word, 2 = arc list. -/
def parityItemBody (arc : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    pair := .load (.register 4) 5 6 15 { CompiledTrie.failCases with
      pair := .load (.register 6) 7 8 15 { CompiledTrie.failCases with
        pair := .allocate 9 (.bit (.flag false) (.register 5))
          (.allocate 10 (.bit (.flag true) (.register 5))
          (.allocate 11 (.bit (.flag false) (.register 7))
          (.allocate 12 (.bit (.flag true) (.register 7))
          (.call arc [.register 11, .register 10, .register 1, .register 2] [13]
          (.call arc [.register 12, .register 9, .register 1, .register 13] [14]
          (.call arc [.register 10, .register 11, .register 1, .register 14] [0]
          (.call arc [.register 9, .register 12, .register 1, .register 0] [3]
            (.ret [.register 3])))))))) } } }

/-- Arguments 0 = vertex word, 1 = unused, 2 = word list. -/
def nodeItemBody : Command p :=
  .allocate 3 (.bit (.flag true) (.register 0))
    (.allocate 4 (.cons (.register 3) (.register 2))
      (.allocate 5 (.bit (.flag false) (.register 0))
        (.allocate 6 (.cons (.register 5) (.register 4)) (.ret [.register 6]))))

structure Procedures (p : ℕ) where
  adjArcs : Fin p
  parityArcs : Fin p
  parityNodes : Fin p
  adjItem : Fin p
  parityItem : Fin p
  nodeItem : Fin p
  arc : Fin p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.adjArcs = RegisterListFlatMap.body ids.adjArcs ids.adjItem ∧
  code ids.parityArcs = RegisterListFlatMap.body ids.parityArcs ids.parityItem ∧
  code ids.parityNodes = RegisterListFlatMap.body ids.parityNodes ids.nodeItem ∧
  code ids.adjItem = adjItemBody ids.arc ∧
  code ids.parityItem = parityItemBody ids.arc ∧
  code ids.nodeItem = nodeItemBody ∧
  code ids.arc = arcBody

def adjBudget (t : ℕ) : ℕ := 160 * t + 13

def parityBudget (t : ℕ) : ℕ := 280 * t + 13

def nodesBudget (k : ℕ) : ℕ := 70 * k + 13

/-- The record fields of an edge record. -/
theorem edgeRec_fields {W : ℕ} {h : Heap} {rp : Ptr} {r : EdgeRec W} (hr : EdgeRecAt h rp r) :
    ∃ kp a lp b rp' c, h[rp]? = some (.pair kp a) ∧ h[a]? = some (.pair lp b) ∧
      h[b]? = some (.pair rp' c) ∧ BitsAt h lp r.left ∧ BitsAt h rp' r.right := by
  obtain ⟨kp, a, lp, b, rp', c, _, _, _, _, _, _, h0, -, ha, hl, hb, hr, -⟩ := hr
  exact ⟨kp, a, lp, b, rp', c, h0, ha, hb, hl, hr⟩

theorem adjItem_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {rp op acc : Ptr} {r : EdgeRec W} {as : List (Arc W 1)}
    (hr : EdgeRecAt h rp r) (ho : BitsAt h op one) (ha : TableAt h acc as) :
    ∃ out q, Extends h out ∧ Valid out ∧ TableAt out q (adjItem r ++ as) ∧
      Within code h (initialRegisters [.pointer rp, .pointer op, .pointer acc])
        (code ids.adjItem) [.pointer q] out 130 := by
  obtain ⟨-, -, -, hitem, -, -, harc⟩ := hm
  obtain ⟨kp, a, lp, b, rp', c, c0, ca, cb, hl, hrt⟩ := edgeRec_fields hr
  obtain ⟨o1, q1, e1, v1, t1, w1⟩ := arc_compiled code ids.arc harc hh
    (a := ⟨r.right, r.left, one⟩) hrt hl ho ha
  obtain ⟨o2, q2, e2, v2, t2, w2⟩ := arc_compiled code ids.arc harc v1
    (a := ⟨r.left, r.right, one⟩) (hl.mono e1) (hrt.mono e1) (ho.mono e1) t1
  refine ⟨o2, q2, e1.trans e2, v2, t2, ?_⟩
  rw [hitem]
  refine (Within.load (pointer := rp) (c := Cell.pair kp a) (by reg_simp) c0
    (Within.load (pointer := a) (c := Cell.pair lp b) (by reg_simp) ca
    (Within.load (pointer := b) (c := Cell.pair rp' c) (by reg_simp) cb
    (call_of (by reg_simp) w1 (call_of (by reg_simp) w2
    (ret_values (by reg_simp) le_rfl)))))).mono ?_
  norm_num

theorem parityItem_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {rp op acc : Ptr} {r : EdgeRec W}
    {as : List (Arc (W + 1) 1)}
    (hr : EdgeRecAt h rp r) (ho : BitsAt h op one) (ha : TableAt h acc as) :
    ∃ out q, Extends h out ∧ Valid out ∧ TableAt out q (parityItem r ++ as) ∧
      Within code h (initialRegisters [.pointer rp, .pointer op, .pointer acc])
        (code ids.parityItem) [.pointer q] out 250 := by
  obtain ⟨-, -, -, -, hitem, -, harc⟩ := hm
  obtain ⟨kp, a, lp, b, rp', c, c0, ca, cb, hl, hrt⟩ := edgeRec_fields hr
  obtain ⟨e1, v1, b1⟩ := alloc_bit hh false hl
  obtain ⟨e2, v2, b2⟩ := alloc_bit v1 true (hl.mono e1)
  obtain ⟨e3, v3, b3⟩ := alloc_bit v2 false ((hrt.mono e1).mono e2)
  obtain ⟨e4, v4, b4⟩ := alloc_bit v3 true (((hrt.mono e1).mono e2).mono e3)
  have e14 := ((e1.trans e2).trans e3).trans e4
  have pfl := ((b1.mono e2).mono e3).mono e4
  have ptl := (b2.mono e3).mono e4
  have pfr := b3.mono e4
  obtain ⟨o1, q1, f1, u1, t1, w1⟩ := arc_compiled code ids.arc harc v4
    (a := ⟨parityWord false r.right, parityWord true r.left, one⟩) pfr ptl (ho.mono e14)
    (ha.mono e14)
  obtain ⟨o2, q2, f2, u2, t2, w2⟩ := arc_compiled code ids.arc harc u1
    (a := ⟨parityWord true r.right, parityWord false r.left, one⟩) (b4.mono f1) (pfl.mono f1)
    ((ho.mono e14).mono f1) t1
  have f12 := f1.trans f2
  obtain ⟨o3, q3, f3, u3, t3, w3⟩ := arc_compiled code ids.arc harc u2
    (a := ⟨parityWord true r.left, parityWord false r.right, one⟩) (ptl.mono f12)
    (pfr.mono f12) ((ho.mono e14).mono f12) t2
  have f13 := f12.trans f3
  obtain ⟨o4, q4, f4, u4, t4, w4⟩ := arc_compiled code ids.arc harc u3
    (a := ⟨parityWord false r.left, parityWord true r.right, one⟩) (pfl.mono f13)
    (b4.mono f13) ((ho.mono e14).mono f13) t3
  refine ⟨o4, q4, e14.trans (f13.trans f4), u4, t4, ?_⟩
  rw [hitem]
  refine (Within.load (pointer := rp) (c := Cell.pair kp a) (by reg_simp) c0
    (Within.load (pointer := a) (c := Cell.pair lp b) (by reg_simp) ca
    (Within.load (pointer := b) (c := Cell.pair rp' c) (by reg_simp) cb
    (Within.allocate (c := Cell.bit false lp) (by reg_simp)
    (Within.allocate (c := Cell.bit true lp) (by reg_simp)
    (Within.allocate (c := Cell.bit false rp') (by reg_simp)
    (Within.allocate (c := Cell.bit true rp') (by reg_simp)
    (call_of (by reg_simp) w1 (call_of (by reg_simp) w2 (call_of (by reg_simp) w3
    (call_of (by reg_simp) w4 (ret_values (by reg_simp) le_rfl)))))))))))).mono ?_
  simp [CellExpr.args]

theorem nodeItem_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {vp dp acc : Ptr} {v : Bits W}
    {ws : List (Bits (W + 1))} (hv : BitsAt h vp v) (ha : WordsAt h acc ws) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q ([parityWord false v, parityWord true v] ++ ws) ∧
      Within code h (initialRegisters [.pointer vp, .pointer dp, .pointer acc])
        (code ids.nodeItem) [.pointer q] out 40 := by
  obtain ⟨-, -, -, -, -, hitem, -⟩ := hm
  obtain ⟨e1, v1, b1⟩ := alloc_bit hh true hv
  have hacc1 := ha.mono e1
  obtain ⟨e2, v2, c2⟩ := alloc_cons v1 b1.allocated hacc1.allocated
  have l2 := WordsAt.cons c2 (b1.mono e2) (hacc1.mono e2)
  obtain ⟨e3, v3, b3⟩ := alloc_bit v2 false ((hv.mono e1).mono e2)
  obtain ⟨e4, v4, c4⟩ := alloc_cons v3 b3.allocated (l2.mono e3).allocated
  have l4 := WordsAt.cons c4 (b3.mono e4) ((l2.mono e3).mono e4)
  refine ⟨_, _, ((e1.trans e2).trans e3).trans e4, v4, l4, ?_⟩
  rw [hitem]
  refine (Within.allocate (c := Cell.bit true vp) (by reg_simp)
    (Within.allocate (c := Cell.cons h.length acc) (by reg_simp)
    (Within.allocate (c := Cell.bit false vp) (by reg_simp)
    (Within.allocate (c := Cell.cons (h ++ [Cell.bit true vp] ++
        [Cell.cons h.length acc]).length (h ++ [Cell.bit true vp]).length) (by reg_simp)
    (ret_values (by reg_simp) le_rfl))))).mono ?_
  simp [CellExpr.args]

/-! ## Tables -/

theorem adjArcs_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {tp op : Ptr} {T : List (EdgeRec W)}
    (hT : RecordsAt h tp T) (ho : BitsAt h op one) :
    ∃ out q, Extends h out ∧ Valid out ∧ TableAt out q (adjArcs (edgePairs T)) ∧
      Within code h (initialRegisters [.pointer tp, .pointer op, .pointer 0])
        (code ids.adjArcs) [.pointer q] out (adjBudget T.length) := by
  have hm' := hm
  obtain ⟨hself, -⟩ := hm'
  obtain ⟨out, q, he, hv, hq, hw⟩ := RegisterListFlatMap.compiled code ids.adjArcs ids.adjItem
    hself EdgeRecAt (fun h p (_ : Unit) => BitsAt h p one) TableAt
    (fun he _ _ hr => hr.mono he) (fun he _ _ hb => hb.mono he) (fun _ r => adjItem r) 130
    (fun hv _ _ _ _ _ _ hx hd ht => adjItem_compiled ids code hm hv hx hd ht)
    hh hT (data := ()) ho (TableAt.nil hh.1 : TableAt h 0 ([] : List (Arc W 1)))
  refine ⟨out, q, he, hv, by simpa [adjArcs_eq] using hq, hw.mono ?_⟩
  simp [adjBudget]; omega

theorem parityArcs_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {tp op : Ptr} {T : List (EdgeRec W)}
    (hT : RecordsAt h tp T) (ho : BitsAt h op one) :
    ∃ out q, Extends h out ∧ Valid out ∧ TableAt out q (parityArcs (edgePairs T)) ∧
      Within code h (initialRegisters [.pointer tp, .pointer op, .pointer 0])
        (code ids.parityArcs) [.pointer q] out (parityBudget T.length) := by
  have hm' := hm
  obtain ⟨-, hself, -⟩ := hm'
  obtain ⟨out, q, he, hv, hq, hw⟩ := RegisterListFlatMap.compiled code ids.parityArcs
    ids.parityItem hself EdgeRecAt (fun h p (_ : Unit) => BitsAt h p one) TableAt
    (fun he _ _ hr => hr.mono he) (fun he _ _ hb => hb.mono he) (fun _ r => parityItem r) 250
    (fun hv _ _ _ _ _ _ hx hd ht => parityItem_compiled ids code hm hv hx hd ht)
    hh hT (data := ()) ho (TableAt.nil hh.1 : TableAt h 0 ([] : List (Arc (W + 1) 1)))
  refine ⟨out, q, he, hv, by simpa [parityArcs_eq] using hq, hw.mono ?_⟩
  simp [parityBudget]; omega

theorem parityNodes_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {np : Ptr} {nodes : List (Bits W)}
    (hn : WordsAt h np nodes) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (parityNodeWords nodes) ∧
      Within code h (initialRegisters [.pointer np, .pointer 0, .pointer 0])
        (code ids.parityNodes) [.pointer q] out (nodesBudget nodes.length) := by
  have hm' := hm
  obtain ⟨-, -, hself, -⟩ := hm'
  obtain ⟨out, q, he, hv, hq, hw⟩ := RegisterListFlatMap.compiled code ids.parityNodes
    ids.nodeItem hself (fun h p (w : Bits W) => BitsAt h p w) (fun _ _ (_ : Unit) => True)
    WordsAt (fun he _ _ hb => hb.mono he) (fun _ _ _ _ => trivial)
    (fun _ v => [parityWord false v, parityWord true v]) 40
    (fun hv _ _ _ _ _ _ hx _ ht => nodeItem_compiled ids code hm hv hx ht)
    hh hn (data := ()) trivial (WordsAt.nil hh.1 : WordsAt h 0 ([] : List (Bits (W + 1))))
  refine ⟨out, q, he, hv, by simpa [parityNodeWords] using hq, hw.mono ?_⟩
  simp [nodesBudget]; omega

end WeightedMIS.RegisterGraphArcs
