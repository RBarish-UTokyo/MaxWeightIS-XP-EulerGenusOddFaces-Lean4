module

public import WeightedMIS.RegisterAdjacencyScan

/-!
# Register construction of the complete capacity table

The table lists one arc record `(source, (target, capacity))` for every ordered
pair of network nodes, in the `List.product` order of
`NetworkWords.nodes n`. It is built by a nested flat map over the node record
list. For each pair the capacity is selected from the two tag bits of both node
words: the scaled weight of the target for `source → left`, the scaled weight of
the source for `right → sink`, the large capacity `1 + Σ μ` or zero for
`left → right` according to an edge scan, and zero otherwise. Capacity words are
shared, never copied.

The resulting stored table is exactly
`((nodes n).product (nodes n)).map (encodeArc (nodeWord W) (capWord B adj μ))`
for every decision instance of the endpoint adjacency `adj`.
-/

@[expose] public section

namespace WeightedMIS.RegisterNetworkTable

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.ResidualWords
open WeightedMIS.DoubleCoverNetwork WeightedMIS.GraphReachEncoded WeightedMIS.NetworkWords
open WeightedMIS.RegisterNetworkNodes WeightedMIS.RegisterAdjacencyScan
open WeightedMIS.RegisterNetworkWeights (allocate_fits pair_fits cons_fits)
open scoped BigOperators

variable {n B W m : ℕ}

/-! ## Representations -/

/-- Shared network data: `pair edges (pair big zero)`. -/
def GlobalAt (es : List (Bits W × Bits W)) (big zero : Bits B) (h : Heap) (p : Ptr) : Prop :=
  ∃ ep rest bp zp, h[p]? = some (.pair ep rest) ∧ h[rest]? = some (.pair bp zp) ∧
    EdgeWordsAt h ep es ∧ BitsAt h bp big ∧ BitsAt h zp zero

theorem GlobalAt.mono {es : List (Bits W × Bits W)} {big zero : Bits B} {h h' : Heap}
    (he : Extends h h') {p : Ptr} (hg : GlobalAt es big zero h p) : GlobalAt es big zero h' p := by
  obtain ⟨ep, rest, bp, zp, c1, c2, h1, h2, h3⟩ := hg
  exact ⟨ep, rest, bp, zp, he.lookup c1, he.lookup c2, h1.mono he, h2.mono he, h3.mono he⟩

/-- The canonical scaled weight words. -/
abbrev muWordOf (B : ℕ) (μ : Fin n → ℕ) : Fin n → Bits B := fun v => word B (μ v)

/-- The arc record of an ordered pair. -/
abbrev arc (W B : ℕ) (adj : Fin n → Fin n → Prop) [DecidableRel adj] (μ : Fin n → ℕ)
    (a : Node (Fin n) × Node (Fin n)) : Arc (W + 2) B :=
  ResidualCrossingRefinement.encodeArc (nodeWord W) (capWord B adj μ) a

/-! ## Procedures -/

structure Procedures (p : ℕ) where
  adj : RegisterAdjacencyScan.Procedures p
  capSel : Fin p
  innerItem : Fin p
  inner : Fin p
  outerItem : Fin p
  outer : Fin p
  self : Fin p

variable {p : ℕ}

/-- Selection from the tag bits (registers 6, 10 of the source word and 8, 12 of
the target word). -/
def capTree (adj : Fin p) : Command p :=
  .branch (.register 6)
    (.branch (.register 10)
      (.branch (.register 8) (.ret [.register 4])
        (.branch (.register 12) (.ret [.register 1]) (.ret [.register 4])))
      (.branch (.register 8)
        (.branch (.register 12)
          (.call adj [.register 13, .register 9, .register 11] [5]
            (.branch (.register 5) (.ret [.register 14]) (.ret [.register 4])))
          (.ret [.register 4]))
        (.ret [.register 4])))
    (.branch (.register 10) (.ret [.register 4])
      (.branch (.register 8)
        (.branch (.register 12) (.ret [.register 4]) (.ret [.register 3]))
        (.ret [.register 4])))

/-- Arguments: source word, source weight, target word, target weight, shared
data. Result: the capacity word. -/
def capSelBody (adj : Fin p) : Command p :=
  .load (.register 0) 5 15 6 { CompiledTrie.failCases with
    bit := .load (.register 2) 7 15 8 { CompiledTrie.failCases with
      bit := .load (.register 5) 9 15 10 { CompiledTrie.failCases with
        bit := .load (.register 7) 11 15 12 { CompiledTrie.failCases with
          bit := .load (.register 4) 13 14 15 { CompiledTrie.failCases with
            pair := .load (.register 14) 14 4 15 { CompiledTrie.failCases with
              pair := capTree adj } } } } } }

/-- Arguments: target record, data `pair sourceRecord shared`, accumulator. -/
def innerItemBody (capSel : Fin p) : Command p :=
  .load (.register 1) 3 4 15 { CompiledTrie.failCases with
    pair := .load (.register 3) 5 6 15 { CompiledTrie.failCases with
      pair := .load (.register 0) 7 8 15 { CompiledTrie.failCases with
        pair := .call capSel [.register 5, .register 6, .register 7, .register 8, .register 4] [9]
          (.allocate 10 (.pair (.register 7) (.register 9))
            (.allocate 11 (.pair (.register 5) (.register 10))
              (.allocate 12 (.cons (.register 11) (.register 2)) (.ret [.register 12])))) } } }

/-- Arguments: source record, data `pair records shared`, accumulator. -/
def outerItemBody (inner : Fin p) : Command p :=
  .load (.register 1) 3 4 15 { CompiledTrie.failCases with
    pair := .allocate 5 (.pair (.register 0) (.register 4))
      (.call inner [.register 3, .register 5, .register 2] [6] (.ret [.register 6])) }

/-- Arguments: node records, edges, large capacity, zero. Result: the table. -/
def tableBody (outer : Fin p) : Command p :=
  .allocate 4 (.pair (.register 2) (.register 3))
    (.allocate 5 (.pair (.register 1) (.register 4))
      (.allocate 6 (.pair (.register 0) (.register 5))
        (.call outer [.register 0, .register 6, .null] [7] (.ret [.register 7]))))

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  d.adj.Matches code ∧
  code d.capSel = capSelBody d.adj.self ∧
  code d.innerItem = innerItemBody d.capSel ∧
  code d.inner = RegisterListFlatMap.body d.inner d.innerItem ∧
  code d.outerItem = outerItemBody d.inner ∧
  code d.outer = RegisterListFlatMap.body d.outer d.outerItem ∧
  code d.self = tableBody d.outer

/-! ## Capacity selection -/

theorem branch_reg {code : Code p} {h h' : Heap} {regs : Registers} {r : Register} {b : Bool}
    {yes no : Command p} {outputs : List Value} {budget : ℕ} (hr : regs r = .flag b)
    (rest : Within code h regs (if b then yes else no) outputs h' budget) :
    Within code h regs (.branch (.register r) yes no) outputs h' (3 + budget) :=
  Within.branch (by simp [Atom.eval, hr]) rest

theorem ret_reg (code : Code p) (h : Heap) {regs : Registers} {r : Register} {c : Ptr}
    (hr : regs r = .pointer c) : Within code h regs (.ret [.register r]) [.pointer c] h 3 := by
  simpa [values, Atom.eval, hr] using Within.ret code h regs [.register r]

def capBudget (W m : ℕ) : ℕ := RegisterAdjacencyScan.budget W m + 100

theorem tree_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    (hn : n < 2 ^ W) (left right : Fin m → Fin n) [DecidableRel (EdgeTransport.Adj left right)]
    (μ : Fin n → ℕ) {h : Heap} (hh : Valid h) {regs : Registers}
    {ump vmp zp bp ep ux vx : Ptr} (u v : Node (Fin n))
    (g1 : regs 1 = .pointer ump) (g3 : regs 3 = .pointer vmp) (g4 : regs 4 = .pointer zp)
    (g6 : regs 6 = .flag (tagInner u)) (g8 : regs 8 = .flag (tagInner v))
    (g9 : regs 9 = .pointer ux) (g10 : regs 10 = .flag (tagSide u))
    (g11 : regs 11 = .pointer vx) (g12 : regs 12 = .flag (tagSide v))
    (g13 : regs 13 = .pointer ep) (g14 : regs 14 = .pointer bp)
    (hum : BitsAt h ump (muOf (muWordOf B μ) (word B 0) u))
    (hvm : BitsAt h vmp (muOf (muWordOf B μ) (word B 0) v))
    (hz : BitsAt h zp (word B 0)) (hb : BitsAt h bp (word B (1 + ∑ x, μ x)))
    (he : EdgeWordsAt h ep (edgeWords W left right))
    (hux : BitsAt h ux (payload W u)) (hvx : BitsAt h vx (payload W v)) :
    ∃ out c, Extends h out ∧ Valid out ∧
      BitsAt out c (capWord B (EdgeTransport.Adj left right) μ u v) ∧
      Within code h regs (capTree d.adj.self) [.pointer c] out (capBudget W m) := by
  have z4 := ret_reg code h g4
  rcases u with (_ | _) | ⟨(_ | _), x⟩ <;> rcases v with (_ | _) | ⟨(_ | _), y⟩ <;>
    simp only [tagInner, tagSide] at g6 g8 g10 g12
  -- source row
  · exact ⟨h, zp, .refl h, hh, hz, (branch_reg g6 (branch_reg g10 (branch_reg g8 z4))).mono
      (by unfold capBudget; omega)⟩
  · exact ⟨h, zp, .refl h, hh, hz, (branch_reg g6 (branch_reg g10 (branch_reg g8 z4))).mono
      (by unfold capBudget; omega)⟩
  · exact ⟨h, vmp, .refl h, hh, hvm, (branch_reg g6 (branch_reg g10 (branch_reg g8
      (branch_reg g12 (ret_reg code h g3))))).mono (by unfold capBudget; omega)⟩
  · exact ⟨h, zp, .refl h, hh, hz, (branch_reg g6 (branch_reg g10 (branch_reg g8
      (branch_reg g12 z4)))).mono (by unfold capBudget; omega)⟩
  -- sink row
  all_goals first
    | exact ⟨h, zp, .refl h, hh, hz, (branch_reg g6 (branch_reg g10 z4)).mono
        (by unfold capBudget; omega)⟩
    | skip
  -- left rows
  · exact ⟨h, zp, .refl h, hh, hz, (branch_reg g6 (branch_reg g10 (branch_reg g8 z4))).mono
      (by unfold capBudget; omega)⟩
  · exact ⟨h, zp, .refl h, hh, hz, (branch_reg g6 (branch_reg g10 (branch_reg g8 z4))).mono
      (by unfold capBudget; omega)⟩
  · exact ⟨h, zp, .refl h, hh, hz, (branch_reg g6 (branch_reg g10 (branch_reg g8
      (branch_reg g12 z4)))).mono (by unfold capBudget; omega)⟩
  · obtain ⟨out, b, ext, valid, hiff, run⟩ := RegisterAdjacencyScan.compiled_adj code d.adj
      hm.1 hn left right x y hh he hux hvx
    let s := bindResults regs [5] [.flag b]
    have tail : ∃ c, BitsAt out c (capWord B (EdgeTransport.Adj left right) μ
        (.inr (false, x)) (.inr (true, y))) ∧
        Within code out s (.branch (.register 5) (.ret [.register 14]) (.ret [.register 4]))
          [.pointer c] out 6 := by
      rw [cap_left_right]
      cases b
      · have hna : ¬ EdgeTransport.Adj left right x y := fun ha => by simpa using hiff.mpr ha
        refine ⟨zp, by simpa [hna] using hz.mono ext, ?_⟩
        have r5 : s 5 = .flag false := by simp [s, bindResults]
        have r4 : s 4 = .pointer zp := by simp [s, bindResults, g4]
        exact (branch_reg (regs := s) r5 (ret_reg code out r4)).mono (by omega)
      · have ha : EdgeTransport.Adj left right x y := hiff.mp rfl
        refine ⟨bp, by simpa [ha] using hb.mono ext, ?_⟩
        have r5 : s 5 = .flag true := by simp [s, bindResults]
        have r14 : s 14 = .pointer bp := by simp [s, bindResults, g14]
        exact (branch_reg (regs := s) r5 (ret_reg code out r14)).mono (by omega)
    obtain ⟨c, hc, tailRun⟩ := tail
    have args : values regs [.register 13, .register 9, .register 11] =
        [.pointer ep, .pointer ux, .pointer vx] := by
      simp [values, Atom.eval, g13, g9, g11]
    have call := Within.call (procedure := d.adj.self) (regs := regs)
      (arguments := [.register 13, .register 9, .register 11]) (results := [5])
      (by simpa only [args] using run) tailRun
    exact ⟨out, c, ext, valid, hc, (branch_reg g6 (branch_reg g10 (branch_reg g8
      (branch_reg g12 call)))).mono
        (by unfold capBudget; simp only [List.length_cons, List.length_nil]; omega)⟩
  -- right rows
  · exact ⟨h, zp, .refl h, hh, hz, (branch_reg g6 (branch_reg g10 (branch_reg g8
      (branch_reg g12 z4)))).mono (by unfold capBudget; omega)⟩
  · exact ⟨h, ump, .refl h, hh, hum, (branch_reg g6 (branch_reg g10 (branch_reg g8
      (branch_reg g12 (ret_reg code h g1))))).mono (by unfold capBudget; omega)⟩
  · exact ⟨h, zp, .refl h, hh, hz, (branch_reg g6 (branch_reg g10 (branch_reg g8 z4))).mono
      (by unfold capBudget; omega)⟩
  · exact ⟨h, zp, .refl h, hh, hz, (branch_reg g6 (branch_reg g10 (branch_reg g8 z4))).mono
      (by unfold capBudget; omega)⟩

theorem nodeWord_cells {h : Heap} {wp : Ptr} {u : Node (Fin n)} (hw : BitsAt h wp (nodeWord W u)) :
    ∃ t1 xp, h[wp]? = some (.bit (tagInner u) t1) ∧ h[t1]? = some (.bit (tagSide u) xp) ∧
      BitsAt h xp (payload W u) := by
  unfold nodeWord at hw
  cases hw with
  | cons c1 rest =>
    cases rest with
    | cons c2 rest2 => exact ⟨_, _, c1, c2, rest2⟩

theorem capSel_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    (hn : n < 2 ^ W) (left right : Fin m → Fin n) [DecidableRel (EdgeTransport.Adj left right)]
    (μ : Fin n → ℕ) {h : Heap} (hh : Valid h) {uwp ump vwp vmp gp : Ptr} {u v : Node (Fin n)}
    (huw : BitsAt h uwp (nodeWord W u)) (hum : BitsAt h ump (muOf (muWordOf B μ) (word B 0) u))
    (hvw : BitsAt h vwp (nodeWord W v)) (hvm : BitsAt h vmp (muOf (muWordOf B μ) (word B 0) v))
    (hg : GlobalAt (edgeWords W left right) (word B (1 + ∑ x, μ x)) (word B 0) h gp) :
    ∃ out c, Extends h out ∧ Valid out ∧
      BitsAt out c (capWord B (EdgeTransport.Adj left right) μ u v) ∧
      Within code h (initialRegisters [.pointer uwp, .pointer ump, .pointer vwp, .pointer vmp,
        .pointer gp]) (code d.capSel) [.pointer c] out (capBudget W m + 60) := by
  obtain ⟨t1, ux, cu1, cu2, hux⟩ := nodeWord_cells huw
  obtain ⟨s1, vx, cv1, cv2, hvx⟩ := nodeWord_cells hvw
  obtain ⟨ep, rest, bp, zp, cg1, cg2, he, hb, hz⟩ := hg
  let r0 := initialRegisters [Value.pointer uwp, .pointer ump, .pointer vwp, .pointer vmp,
    .pointer gp]
  let r1 := loadRegisters r0 5 15 6 (.bit (tagInner u) t1)
  let r2 := loadRegisters r1 7 15 8 (.bit (tagInner v) s1)
  let r3 := loadRegisters r2 9 15 10 (.bit (tagSide u) ux)
  let r4 := loadRegisters r3 11 15 12 (.bit (tagSide v) vx)
  let r5 := loadRegisters r4 13 14 15 (.pair ep rest)
  let r6 := loadRegisters r5 14 4 15 (.pair bp zp)
  obtain ⟨out, c, ext, valid, hc, run⟩ := tree_compiled code d hm hn left right μ hh
    (regs := r6) u v
    (by simp [r6, r5, r4, r3, r2, r1, r0, loadRegisters, decoded, initialRegisters])
    (by simp [r6, r5, r4, r3, r2, r1, r0, loadRegisters, decoded, initialRegisters])
    (by simp [r6, loadRegisters, decoded])
    (by simp [r6, r5, r4, r3, r2, r1, loadRegisters, decoded])
    (by simp [r6, r5, r4, r3, r2, loadRegisters, decoded])
    (by simp [r6, r5, r4, r3, loadRegisters, decoded])
    (by simp [r6, r5, r4, r3, loadRegisters, decoded])
    (by simp [r6, r5, r4, loadRegisters, decoded])
    (by simp [r6, r5, r4, loadRegisters, decoded])
    (by simp [r6, r5, loadRegisters, decoded])
    (by simp [r6, loadRegisters, decoded]) hum hvm hz hb he hux hvx
  refine ⟨out, c, ext, valid, hc, ?_⟩
  have l6 := Within.load (regs := r5) (address := .register 14) (first := 14) (second := 4)
    (bit := 15) (branches := { CompiledTrie.failCases with pair := capTree d.adj.self })
    (by simp [Atom.eval, r5, loadRegisters, decoded]) cg2 run
  have l5 := Within.load (regs := r4) (address := .register 4) (first := 13) (second := 14)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 14) 14 4 15 { CompiledTrie.failCases with
        pair := capTree d.adj.self } })
    (by simp [Atom.eval, r4, r3, r2, r1, r0, loadRegisters, decoded, initialRegisters]) cg1 l6
  have l4 := Within.load (regs := r3) (address := .register 7) (first := 11) (second := 15)
    (bit := 12) (branches := { CompiledTrie.failCases with
      bit := .load (.register 4) 13 14 15 { CompiledTrie.failCases with
        pair := .load (.register 14) 14 4 15 { CompiledTrie.failCases with
          pair := capTree d.adj.self } } })
    (by simp [Atom.eval, r3, r2, loadRegisters, decoded]) cv2 l5
  have l3 := Within.load (regs := r2) (address := .register 5) (first := 9) (second := 15)
    (bit := 10) (branches := { CompiledTrie.failCases with
      bit := .load (.register 7) 11 15 12 { CompiledTrie.failCases with
        bit := .load (.register 4) 13 14 15 { CompiledTrie.failCases with
          pair := .load (.register 14) 14 4 15 { CompiledTrie.failCases with
            pair := capTree d.adj.self } } } })
    (by simp [Atom.eval, r2, r1, loadRegisters, decoded]) cu2 l4
  have l2 := Within.load (regs := r1) (address := .register 2) (first := 7) (second := 15)
    (bit := 8) (branches := { CompiledTrie.failCases with
      bit := .load (.register 5) 9 15 10 { CompiledTrie.failCases with
        bit := .load (.register 7) 11 15 12 { CompiledTrie.failCases with
          bit := .load (.register 4) 13 14 15 { CompiledTrie.failCases with
            pair := .load (.register 14) 14 4 15 { CompiledTrie.failCases with
              pair := capTree d.adj.self } } } } })
    (by simp [Atom.eval, r1, r0, loadRegisters, decoded, initialRegisters]) cv1 l3
  have l1 := Within.load (regs := r0) (address := .register 0) (first := 5) (second := 15)
    (bit := 6) (branches := { CompiledTrie.failCases with
      bit := .load (.register 2) 7 15 8 { CompiledTrie.failCases with
        bit := .load (.register 5) 9 15 10 { CompiledTrie.failCases with
          bit := .load (.register 7) 11 15 12 { CompiledTrie.failCases with
            bit := .load (.register 4) 13 14 15 { CompiledTrie.failCases with
              pair := .load (.register 14) 14 4 15 { CompiledTrie.failCases with
                pair := capTree d.adj.self } } } } } })
    (by simp [Atom.eval, r0, initialRegisters]) cu1 l2
  rw [hm.2.1]
  exact l1.mono (by omega)

/-! ## The nested flat map -/

section Table

variable (W B) (left right : Fin m → Fin n) [DecidableRel (EdgeTransport.Adj left right)]
  (μ : Fin n → ℕ)

/-- Data of the inner flat map: `pair sourceRecord shared`. -/
def InnerAt (h : Heap) (dp : Ptr) (u : Node (Fin n)) : Prop :=
  ∃ up gp, h[dp]? = some (.pair up gp) ∧ NodeAt W (muWordOf B μ) (word B 0) h up u ∧
    GlobalAt (edgeWords W left right) (word B (1 + ∑ x, μ x)) (word B 0) h gp

/-- Data of the outer flat map: `pair records shared`. -/
def OuterAt (h : Heap) (dp : Ptr) (_ : Unit) : Prop :=
  ∃ rp gp, h[dp]? = some (.pair rp gp) ∧ NodesAt W (muWordOf B μ) (word B 0) h rp (nodes n) ∧
    GlobalAt (edgeWords W left right) (word B (1 + ∑ x, μ x)) (word B 0) h gp

end Table

def innerItemBudget (W m : ℕ) : ℕ := capBudget W m + 130

theorem innerItem_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    (hn : n < 2 ^ W) (left right : Fin m → Fin n) [DecidableRel (EdgeTransport.Adj left right)]
    (μ : Fin n → ℕ) {h : Heap} (hh : Valid h) {vrp dp acc : Ptr} {v u : Node (Fin n)}
    {tail : List (Arc (W + 2) B)}
    (hv : NodeAt W (muWordOf B μ) (word B 0) h vrp v) (hd : InnerAt B W left right μ h dp u)
    (ht : TableAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧
      TableAt out q ([arc W B (EdgeTransport.Adj left right) μ (u, v)] ++ tail) ∧
      Within code h (initialRegisters [.pointer vrp, .pointer dp, .pointer acc])
        (code d.innerItem) [.pointer q] out (innerItemBudget W m) := by
  obtain ⟨up, gp, cd, hu, hg⟩ := hd
  obtain ⟨uw, um, cu, huw, hum⟩ := hu
  obtain ⟨vw, vm, cv, hvw, hvm⟩ := hv
  obtain ⟨h1, c, e1, v1, hc, capRun⟩ := capSel_compiled code d hm hn left right μ hh
    huw hum hvw hvm hg
  let H2 := h1 ++ [Cell.pair vw c]
  let H3 := H2 ++ [Cell.pair uw h1.length]
  let H4 := H3 ++ [Cell.cons H2.length acc]
  obtain ⟨e2, v2, c2⟩ := allocate_fits v1 (pair_fits (hvw.mono e1).allocated hc.allocated)
  obtain ⟨e3, v3, c3⟩ := allocate_fits v2 (pair_fits (h := H2) (b := h1.length)
    (RegisterNetworkNodes.lt_of_ext (e1.trans e2) huw.allocated) (by simp [H2]))
  obtain ⟨e4, v4, c4⟩ := allocate_fits v3 (cons_fits (h := H3) (a := H2.length) (b := acc)
    (by simp [H3]) (RegisterNetworkNodes.lt_of_ext (e1.trans (e2.trans e3)) ht.allocated))
  have harc : ArcAt H3 H2.length (arc W B (EdgeTransport.Adj left right) μ (u, v)) :=
    ⟨uw, h1.length, vw, c, c3, e3.lookup c2, huw.mono (e1.trans (e2.trans e3)),
      hvw.mono (e1.trans (e2.trans e3)), hc.mono (e2.trans e3)⟩
  have hlist : TableAt H4 H3.length ([arc W B (EdgeTransport.Adj left right) μ (u, v)] ++ tail) :=
    TableAt.cons c4 (harc.mono e4) (ht.mono (e1.trans (e2.trans (e3.trans e4))))
  refine ⟨H4, H3.length, e1.trans (e2.trans (e3.trans e4)), v4, hlist, ?_⟩
  let r0 := initialRegisters [Value.pointer vrp, .pointer dp, .pointer acc]
  let r1 := loadRegisters r0 3 4 15 (.pair up gp)
  let r2 := loadRegisters r1 5 6 15 (.pair uw um)
  let r3 := loadRegisters r2 7 8 15 (.pair vw vm)
  let r4 := bindResults r3 [9] [.pointer c]
  let r5 := Function.update r4 10 (.pointer h1.length)
  let r6 := Function.update r5 11 (.pointer H2.length)
  let r7 := Function.update r6 12 (.pointer H3.length)
  have last : Within code H4 r7 (.ret [.register 12]) [.pointer H3.length] H4 3 :=
    ret_reg code H4 (by simp [r7])
  have a12 := Within.allocate (regs := r6) (dst := 12) (h := H3)
    (expr := .cons (.register 11) (.register 2)) (c := .cons H2.length acc)
    (by simp [CellExpr.eval, Atom.eval, r6, r5, r4, r3, r2, r1, r0, bindResults, loadRegisters,
      decoded, initialRegisters, Value.asPointer]) last
  have a11 := Within.allocate (regs := r5) (dst := 11) (h := H2)
    (expr := .pair (.register 5) (.register 10)) (c := .pair uw h1.length)
    (by simp [CellExpr.eval, Atom.eval, r5, r4, r3, r2, bindResults, loadRegisters, decoded,
      Value.asPointer]) a12
  have a10 := Within.allocate (regs := r4) (dst := 10) (h := h1)
    (expr := .pair (.register 7) (.register 9)) (c := .pair vw c)
    (by simp [CellExpr.eval, Atom.eval, r4, r3, bindResults, loadRegisters, decoded,
      Value.asPointer]) a11
  have args : values r3 [.register 5, .register 6, .register 7, .register 8, .register 4] =
      [.pointer uw, .pointer um, .pointer vw, .pointer vm, .pointer gp] := by
    simp [values, Atom.eval, r3, r2, r1, loadRegisters, decoded]
  have call := Within.call (procedure := d.capSel) (regs := r3)
    (arguments := [.register 5, .register 6, .register 7, .register 8, .register 4])
    (results := [9]) (by simpa only [args] using capRun) a10
  have l3 := Within.load (regs := r2) (address := .register 0) (first := 7) (second := 8)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .call d.capSel [.register 5, .register 6, .register 7, .register 8, .register 4] [9]
        (.allocate 10 (.pair (.register 7) (.register 9))
          (.allocate 11 (.pair (.register 5) (.register 10))
            (.allocate 12 (.cons (.register 11) (.register 2)) (.ret [.register 12])))) })
    (by simp [Atom.eval, r2, r1, r0, loadRegisters, decoded, initialRegisters]) cv call
  have l2 := Within.load (regs := r1) (address := .register 3) (first := 5) (second := 6)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 0) 7 8 15 { CompiledTrie.failCases with
        pair := .call d.capSel [.register 5, .register 6, .register 7, .register 8,
            .register 4] [9]
          (.allocate 10 (.pair (.register 7) (.register 9))
            (.allocate 11 (.pair (.register 5) (.register 10))
              (.allocate 12 (.cons (.register 11) (.register 2)) (.ret [.register 12])))) } })
    (by simp [Atom.eval, r1, loadRegisters, decoded]) cu l3
  have l1 := Within.load (regs := r0) (address := .register 1) (first := 3) (second := 4)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 3) 5 6 15 { CompiledTrie.failCases with
        pair := .load (.register 0) 7 8 15 { CompiledTrie.failCases with
          pair := .call d.capSel [.register 5, .register 6, .register 7, .register 8,
              .register 4] [9]
            (.allocate 10 (.pair (.register 7) (.register 9))
              (.allocate 11 (.pair (.register 5) (.register 10))
                (.allocate 12 (.cons (.register 11) (.register 2)) (.ret [.register 12])))) } } })
    (by simp [Atom.eval, r0, initialRegisters]) cd l2
  rw [hm.2.2.1]
  exact l1.mono (by simp [innerItemBudget, CellExpr.args]; omega)

def innerBudget (W m n : ℕ) : ℕ := (innerItemBudget W m + 27) * (2 * n + 2) + 13

def outerItemBudget (W m n : ℕ) : ℕ := innerBudget W m n + 40

theorem outerItem_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    (hn : n < 2 ^ W) (left right : Fin m → Fin n) [DecidableRel (EdgeTransport.Adj left right)]
    (μ : Fin n → ℕ) {h : Heap} (hh : Valid h) {urp dp acc : Ptr} {u : Node (Fin n)}
    {tail : List (Arc (W + 2) B)}
    (hu : NodeAt W (muWordOf B μ) (word B 0) h urp u) (hd : OuterAt B W left right μ h dp ())
    (ht : TableAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧
      TableAt out q ((nodes n).flatMap (fun v => [arc W B (EdgeTransport.Adj left right) μ (u, v)])
        ++ tail) ∧
      Within code h (initialRegisters [.pointer urp, .pointer dp, .pointer acc])
        (code d.outerItem) [.pointer q] out (outerItemBudget W m n) := by
  obtain ⟨rp, gp, cd, hr, hg⟩ := hd
  obtain ⟨e1, v1, c1⟩ := allocate_fits hh (pair_fits hu.allocated
    (by obtain ⟨_, _, _, _, c, -⟩ := hg; exact (List.getElem?_eq_some_iff.mp c).1))
  have hdata : InnerAt B W left right μ (h ++ [.pair urp gp]) h.length u :=
    ⟨urp, gp, c1, hu.mono e1, hg.mono e1⟩
  obtain ⟨out, q, e2, v2, hq, run⟩ := RegisterListFlatMap.compiled code d.inner d.innerItem
    hm.2.2.2.1 (NodeAt W (muWordOf B μ) (word B 0)) (InnerAt B W left right μ)
    (fun h p (xs : List (Arc (W + 2) B)) => TableAt h p xs)
    (fun he _ _ hx => hx.mono he)
    (fun he _ _ hx => by
      obtain ⟨a, b, c, h1, h2⟩ := hx
      exact ⟨a, b, he.lookup c, h1.mono he, h2.mono he⟩)
    (fun u v => [arc W B (EdgeTransport.Adj left right) μ (u, v)]) (innerItemBudget W m)
    (fun hv _ _ _ _ _ _ hx hd ht => innerItem_compiled code d hm hn left right μ hv hx hd ht)
    v1 (hr.mono e1) hdata (ht.mono e1)
  refine ⟨out, q, e1.trans e2, v2, hq, ?_⟩
  let r0 := initialRegisters [Value.pointer urp, .pointer dp, .pointer acc]
  let r1 := loadRegisters r0 3 4 15 (.pair rp gp)
  let r2 := Function.update r1 5 (.pointer h.length)
  let r3 := bindResults r2 [6] [.pointer q]
  have last : Within code out r3 (.ret [.register 6]) [.pointer q] out 3 :=
    ret_reg code out (by simp [r3, bindResults])
  have args : values r2 [.register 3, .register 5, .register 2] =
      [.pointer rp, .pointer h.length, .pointer acc] := by
    simp [values, Atom.eval, r2, r1, r0, loadRegisters, decoded, initialRegisters]
  have call := Within.call (procedure := d.inner) (regs := r2)
    (arguments := [.register 3, .register 5, .register 2]) (results := [6])
    (by simpa only [args] using run) last
  have al := Within.allocate (regs := r1) (dst := 5) (h := h)
    (expr := .pair (.register 0) (.register 4)) (c := .pair urp gp)
    (by simp [CellExpr.eval, Atom.eval, r1, r0, loadRegisters, decoded, initialRegisters,
      Value.asPointer]) call
  have l1 := Within.load (regs := r0) (address := .register 1) (first := 3) (second := 4)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .allocate 5 (.pair (.register 0) (.register 4))
        (.call d.inner [.register 3, .register 5, .register 2] [6] (.ret [.register 6])) })
    (by simp [Atom.eval, r0, initialRegisters]) cd al
  rw [hm.2.2.2.2.1]
  have hlen : (nodes n).length = 2 * n + 2 := by rw [nodes_eq]; simp; ring
  rw [hlen] at l1
  exact l1.mono (by simp [outerItemBudget, innerBudget, CellExpr.args]; omega)

def budget (W m n : ℕ) : ℕ := (outerItemBudget W m n + 27) * (2 * n + 2) + 60

theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    (hn : n < 2 ^ W) (left right : Fin m → Fin n) [DecidableRel (EdgeTransport.Adj left right)]
    (μ : Fin n → ℕ) {h : Heap} (hh : Valid h) {rp ep bp zp : Ptr}
    (hr : NodesAt W (muWordOf B μ) (word B 0) h rp (nodes n))
    (he : EdgeWordsAt h ep (edgeWords W left right))
    (hb : BitsAt h bp (word B (1 + ∑ x, μ x))) (hz : BitsAt h zp (word B 0)) :
    ∃ out tp, Extends h out ∧ Valid out ∧
      TableAt out tp (((nodes n).product (nodes n)).map (arc W B (EdgeTransport.Adj left right) μ)) ∧
      Within code h (initialRegisters [.pointer rp, .pointer ep, .pointer bp, .pointer zp])
        (code d.self) [.pointer tp] out (budget W m n) := by
  let H1 := h ++ [Cell.pair bp zp]
  let H2 := H1 ++ [Cell.pair ep h.length]
  let H3 := H2 ++ [Cell.pair rp H1.length]
  obtain ⟨e1, v1, c1⟩ := allocate_fits hh (pair_fits hb.allocated hz.allocated)
  obtain ⟨e2, v2, c2⟩ := allocate_fits v1 (pair_fits (h := H1) (b := h.length)
    (RegisterNetworkNodes.lt_of_ext e1 he.allocated) (by simp [H1]))
  obtain ⟨e3, v3, c3⟩ := allocate_fits v2 (pair_fits (h := H2) (b := H1.length)
    (RegisterNetworkNodes.lt_of_ext (e1.trans e2) (ListRep.allocated hr)) (by simp [H2]))
  have e13 := e1.trans (e2.trans e3)
  have hg : GlobalAt (edgeWords W left right) (word B (1 + ∑ x, μ x)) (word B 0) H3 H1.length :=
    ⟨ep, h.length, bp, zp, e3.lookup c2, (e2.trans e3).lookup c1, he.mono e13, hb.mono e13,
      hz.mono e13⟩
  have hdata : OuterAt B W left right μ H3 H2.length () :=
    ⟨rp, H1.length, c3, hr.mono e13, hg⟩
  have hnil : TableAt H3 0 ([] : List (Arc (W + 2) B)) := RegisterListCommon.listRep_null v3
  obtain ⟨out, q, e4, v4, hq, run⟩ := RegisterListFlatMap.compiled code d.outer d.outerItem
    hm.2.2.2.2.2.1 (NodeAt W (muWordOf B μ) (word B 0)) (OuterAt B W left right μ)
    (fun h p (xs : List (Arc (W + 2) B)) => TableAt h p xs)
    (fun he _ _ hx => hx.mono he)
    (fun he _ _ hx => by
      obtain ⟨a, b, c, h1, h2⟩ := hx
      exact ⟨a, b, he.lookup c, h1.mono he, h2.mono he⟩)
    (fun _ u => (nodes n).flatMap (fun v => [arc W B (EdgeTransport.Adj left right) μ (u, v)]))
    (outerItemBudget W m n)
    (fun hv _ _ _ _ data _ hx hd ht => by
      cases data
      exact outerItem_compiled code d hm hn left right μ hv hx hd ht)
    v3 (hr.mono e13) hdata hnil
  have htab : (nodes n).flatMap (fun u => (nodes n).flatMap
      (fun v => [arc W B (EdgeTransport.Adj left right) μ (u, v)])) ++ [] =
      ((nodes n).product (nodes n)).map (arc W B (EdgeTransport.Adj left right) μ) := by
    rw [List.append_nil, product_map_eq]
  rw [htab] at hq
  refine ⟨out, q, e13.trans e4, v4, hq, ?_⟩
  let r0 := initialRegisters [Value.pointer rp, .pointer ep, .pointer bp, .pointer zp]
  let r1 := Function.update r0 4 (.pointer h.length)
  let r2 := Function.update r1 5 (.pointer H1.length)
  let r3 := Function.update r2 6 (.pointer H2.length)
  let r4 := bindResults r3 [7] [.pointer q]
  have last : Within code out r4 (.ret [.register 7]) [.pointer q] out 3 :=
    ret_reg code out (by simp [r4, bindResults])
  have args : values r3 [.register 0, .register 6, .null] =
      [.pointer rp, .pointer H2.length, .pointer 0] := by
    simp [values, Atom.eval, r3, r2, r1, r0, initialRegisters]
  have hlen : (nodes n).length = 2 * n + 2 := by rw [nodes_eq]; simp; ring
  rw [hlen] at run
  have call := Within.call (procedure := d.outer) (regs := r3)
    (arguments := [.register 0, .register 6, .null]) (results := [7])
    (by simpa only [args] using run) last
  have a6 := Within.allocate (regs := r2) (dst := 6) (h := H2)
    (expr := .pair (.register 0) (.register 5)) (c := .pair rp H1.length)
    (by simp [CellExpr.eval, Atom.eval, r2, r1, r0, initialRegisters, Value.asPointer]) call
  have a5 := Within.allocate (regs := r1) (dst := 5) (h := H1)
    (expr := .pair (.register 1) (.register 4)) (c := .pair ep h.length)
    (by simp [CellExpr.eval, Atom.eval, r1, r0, initialRegisters, Value.asPointer]) a6
  have a4 := Within.allocate (regs := r0) (dst := 4) (h := h)
    (expr := .pair (.register 2) (.register 3)) (c := .pair bp zp)
    (by simp [CellExpr.eval, Atom.eval, r0, initialRegisters, Value.asPointer]) a5
  rw [hm.2.2.2.2.2.2]
  exact a4.mono (by simp [budget, CellExpr.args]; omega)

end WeightedMIS.RegisterNetworkTable
