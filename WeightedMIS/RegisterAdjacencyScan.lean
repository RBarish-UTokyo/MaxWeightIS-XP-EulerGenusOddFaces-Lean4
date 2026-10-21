module

public import WeightedMIS.NetworkWords
public import WeightedMIS.RegisterNetworkNodes
public import WeightedMIS.RegisterListFind

/-!
# Adjacency of two vertex words by an edge scan

Edges are stored as a linked list of `pair` cells holding the two endpoint
words. The procedure packs the two query words into one `pair` cell and runs
the linked-list search with an item predicate that compares an edge with the
query in both orientations, using the compiled binary comparator. The result
flag is `edges.any (NetworkWords.edgeMatch x y)`; on the encoded edge list of a
graph it is exactly the endpoint adjacency `EdgeTransport.Adj`.
-/

@[expose] public section

namespace WeightedMIS.RegisterAdjacencyScan

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.NetworkWords
open WeightedMIS.RegisterNetworkWeights (allocate_fits pair_fits)

/-! ## Stored edge lists -/

/-- One edge: `pair leftWord rightWord`. -/
def EdgeAt {W : ℕ} (h : Heap) (p : Ptr) (e : Bits W × Bits W) : Prop :=
  ∃ lp rp, h[p]? = some (.pair lp rp) ∧ BitsAt h lp e.1 ∧ BitsAt h rp e.2

def EdgeWordsAt {W : ℕ} (h : Heap) (p : Ptr) (es : List (Bits W × Bits W)) : Prop :=
  ListRep EdgeAt h p es

theorem EdgeAt.mono {W : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr} {e : Bits W × Bits W}
    (hx : EdgeAt h p e) : EdgeAt h' p e := by
  obtain ⟨lp, rp, c, hl, hr⟩ := hx
  exact ⟨lp, rp, he.lookup c, hl.mono he, hr.mono he⟩

theorem EdgeWordsAt.mono {W : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr}
    {es : List (Bits W × Bits W)} (hx : EdgeWordsAt h p es) : EdgeWordsAt h' p es :=
  ListRep.mono he (fun _ _ hx => hx.mono he) hx

theorem EdgeWordsAt.allocated {W : ℕ} {h : Heap} {p : Ptr} {es : List (Bits W × Bits W)}
    (hx : EdgeWordsAt h p es) : p < h.length := ListRep.allocated hx

/-- The query pair `pair x y`. -/
def QueryAt {W : ℕ} (h : Heap) (p : Ptr) (q : Bits W × Bits W) : Prop := EdgeAt h p q

/-! ## Procedures -/

variable {p : ℕ}

def secondBody (cmp : Fin p) : Command p :=
  .call cmp [.register 2, .register 5] [6, 9]
    (.branch (.register 9)
      (.call cmp [.register 3, .register 4] [6, 10] (.ret [.register 10]))
      (.ret [.flag false]))

/-- Arguments: edge record, query record. Result: the match flag. -/
def edgeItemBody (cmp : Fin p) : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    pair := .load (.register 1) 4 5 15 { CompiledTrie.failCases with
      pair := .call cmp [.register 2, .register 4] [6, 7]
        (.branch (.register 7)
          (.call cmp [.register 3, .register 5] [6, 8]
            (.branch (.register 8) (.ret [.flag true]) (secondBody cmp)))
          (secondBody cmp)) } }

/-- Arguments: edge list, two vertex words. Result: the adjacency flag. -/
def adjBody (find : Fin p) : Command p :=
  .allocate 3 (.pair (.register 1) (.register 2))
    (.call find [.register 0, .register 3] [4, 5] (.ret [.register 4]))

structure Procedures (p : ℕ) where
  cmp : Fin p
  item : Fin p
  find : Fin p
  self : Fin p

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  code d.cmp = RegisterComparator.comparatorBody d.cmp ∧
  code d.item = edgeItemBody d.cmp ∧
  code d.find = RegisterListFind.body d.find d.item ∧
  code d.self = adjBody d.find

/-! ## The comparison item -/

theorem cmp_eq {W : ℕ} (a b : Bits W) :
    decide ((Bits.compare a b).1 = .eq) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [(Bits.compare_correct a b).2.1]
  exact ⟨fun h => ResidualListReach.bits_value_inj h, fun h => h ▸ rfl⟩

theorem cmp_run (code : Code p) (cmp : Fin p) (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {W : ℕ} {h : Heap} {ap bp : Ptr} {a b : Bits W} (ha : BitsAt h ap a) (hb : BitsAt h bp b) :
    Within code h (initialRegisters [.pointer ap, .pointer bp]) (code cmp)
      [.flag (decide ((Bits.compare a b).1 = .lt)), .flag (decide (a = b))] h (36 * W + 25) := by
  have := RegisterComparator.compiled code cmp hcmp ha hb
  simpa [RegisterComparator.flags, cmp_eq] using this

theorem second_within (code : Code p) (cmp : Fin p)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp) {W : ℕ} {h : Heap}
    {regs : Registers} {lp rp xp yp : Ptr} {e : Bits W × Bits W} {x y : Bits W}
    (h2 : regs 2 = .pointer lp) (h3 : regs 3 = .pointer rp) (h4 : regs 4 = .pointer xp)
    (h5 : regs 5 = .pointer yp) (hl : BitsAt h lp e.1) (hr : BitsAt h rp e.2)
    (hx : BitsAt h xp x) (hy : BitsAt h yp y) :
    Within code h regs (secondBody cmp) [.flag (decide (e.1 = y) && decide (e.2 = x))] h
      (72 * W + 70) := by
  have r1 := cmp_run code cmp hcmp hl hy
  let s1 := bindResults regs [6, 9]
    [.flag (decide ((Bits.compare e.1 y).1 = .lt)), .flag (decide (e.1 = y))]
  by_cases hey : e.1 = y
  · have r2 := cmp_run code cmp hcmp hr hx
    let s2 := bindResults s1 [6, 10]
      [.flag (decide ((Bits.compare e.2 x).1 = .lt)), .flag (decide (e.2 = x))]
    have last : Within code h s2 (.ret [.register 10]) [.flag (decide (e.2 = x))] h 3 := by
      simpa [values, Atom.eval, s2, bindResults] using Within.ret code h s2 [.register 10]
    have a2 : values s1 [.register 3, .register 4] = [.pointer rp, .pointer xp] := by
      simp [values, Atom.eval, s1, bindResults, h3, h4]
    have c2 := Within.call (procedure := cmp) (regs := s1)
      (arguments := [.register 3, .register 4]) (results := [6, 10])
      (by simpa only [a2] using r2) last
    have br := Within.branch (regs := s1) (test := .register 9) (b := true)
      (no := .ret [.flag false]) (by simp [Atom.eval, s1, bindResults, hey]) c2
    have a1 : values regs [.register 2, .register 5] = [.pointer lp, .pointer yp] := by
      simp [values, Atom.eval, h2, h5]
    have c1 := Within.call (procedure := cmp) (regs := regs)
      (arguments := [.register 2, .register 5]) (results := [6, 9])
      (by simpa only [a1] using r1) br
    simpa [secondBody, hey] using c1.mono (by simp; omega)
  · have last : Within code h s1 (.ret [.flag false]) [.flag false] h 3 := by
      simpa [values, Atom.eval] using Within.ret code h s1 [.flag false]
    have br := Within.branch (regs := s1) (test := .register 9) (b := false)
      (yes := .call cmp [.register 3, .register 4] [6, 10] (.ret [.register 10]))
      (by simp [Atom.eval, s1, bindResults, hey]) last
    have a1 : values regs [.register 2, .register 5] = [.pointer lp, .pointer yp] := by
      simp [values, Atom.eval, h2, h5]
    have c1 := Within.call (procedure := cmp) (regs := regs)
      (arguments := [.register 2, .register 5]) (results := [6, 9])
      (by simpa only [a1] using r1) br
    simpa [secondBody, hey] using c1.mono (by simp; omega)

def itemBudget (W : ℕ) : ℕ := 144 * W + 160

theorem item_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {W : ℕ} {h : Heap} {ep qp : Ptr} {e q : Bits W × Bits W}
    (he : EdgeAt h ep e) (hq : QueryAt h qp q) :
    Within code h (initialRegisters [.pointer ep, .pointer qp]) (code d.item)
      [.flag (edgeMatch q.1 q.2 e)] h (itemBudget W) := by
  obtain ⟨hcmp, hitem, -⟩ := hm
  obtain ⟨lp, rp, c1, hl, hr⟩ := he
  obtain ⟨xp, yp, c2, hx, hy⟩ := hq
  let regs := initialRegisters [Value.pointer ep, .pointer qp]
  let r1 := loadRegisters regs 2 3 15 (.pair lp rp)
  let r2 := loadRegisters r1 4 5 15 (.pair xp yp)
  have g2 : r2 2 = .pointer lp := by simp [r2, r1, loadRegisters, decoded]
  have g3 : r2 3 = .pointer rp := by simp [r2, r1, loadRegisters, decoded]
  have g4 : r2 4 = .pointer xp := by simp [r2, loadRegisters, decoded]
  have g5 : r2 5 = .pointer yp := by simp [r2, loadRegisters, decoded]
  let inner : Command p := .call d.cmp [.register 2, .register 4] [6, 7]
    (.branch (.register 7)
      (.call d.cmp [.register 3, .register 5] [6, 8]
        (.branch (.register 8) (.ret [.flag true]) (secondBody d.cmp)))
      (secondBody d.cmp))
  have tree : Within code h r2 inner [.flag (edgeMatch q.1 q.2 e)] h (144 * W + 140) := by
    have run1 := cmp_run code d.cmp hcmp hl hx
    let s1 := bindResults r2 [6, 7]
      [.flag (decide ((Bits.compare e.1 q.1).1 = .lt)), .flag (decide (e.1 = q.1))]
    have t2 : s1 2 = .pointer lp := by simp [s1, bindResults, g2]
    have t3 : s1 3 = .pointer rp := by simp [s1, bindResults, g3]
    have t4 : s1 4 = .pointer xp := by simp [s1, bindResults, g4]
    have t5 : s1 5 = .pointer yp := by simp [s1, bindResults, g5]
    have a1 : values r2 [.register 2, .register 4] = [.pointer lp, .pointer xp] := by
      simp [values, Atom.eval, g2, g4]
    by_cases hex : e.1 = q.1
    · have run2 := cmp_run code d.cmp hcmp hr hy
      let s2 := bindResults s1 [6, 8]
        [.flag (decide ((Bits.compare e.2 q.2).1 = .lt)), .flag (decide (e.2 = q.2))]
      have tail : Within code h s2 (.branch (.register 8) (.ret [.flag true]) (secondBody d.cmp))
          [.flag (edgeMatch q.1 q.2 e)] h (72 * W + 73) := by
        by_cases hey : e.2 = q.2
        · have last : Within code h s2 (.ret [.flag true]) [.flag true] h 3 := by
            simpa [values, Atom.eval] using Within.ret code h s2 [.flag true]
          have br := Within.branch (regs := s2) (test := .register 8) (b := true)
            (no := secondBody d.cmp) (by simp [Atom.eval, s2, bindResults, hey]) last
          simpa [edgeMatch, hex, hey] using br.mono (by omega)
        · have sec := second_within code d.cmp hcmp (regs := s2) (e := e) (x := q.1) (y := q.2)
            (by simp [s2, bindResults, t2]) (by simp [s2, bindResults, t3])
            (by simp [s2, bindResults, t4]) (by simp [s2, bindResults, t5]) hl hr hx hy
          have br := Within.branch (regs := s2) (test := .register 8) (b := false)
            (yes := .ret [.flag true]) (by simp [Atom.eval, s2, bindResults, hey]) sec
          have hm' : edgeMatch q.1 q.2 e = (decide (e.1 = q.2) && decide (e.2 = q.1)) := by
            simp [edgeMatch, hex, hey]
          rw [hm']
          exact br.mono (by omega)
      have a2 : values s1 [.register 3, .register 5] = [.pointer rp, .pointer yp] := by
        simp [values, Atom.eval, t3, t5]
      have c2 := Within.call (procedure := d.cmp) (regs := s1)
        (arguments := [.register 3, .register 5]) (results := [6, 8])
        (by simpa only [a2] using run2) tail
      have br := Within.branch (regs := s1) (test := .register 7) (b := true)
        (no := secondBody d.cmp) (by simp [Atom.eval, s1, bindResults, hex]) c2
      have c1 := Within.call (procedure := d.cmp) (regs := r2)
        (arguments := [.register 2, .register 4]) (results := [6, 7])
        (by simpa only [a1] using run1) br
      exact c1.mono (by simp; omega)
    · have sec := second_within code d.cmp hcmp (regs := s1) (e := e) (x := q.1) (y := q.2)
        t2 t3 t4 t5 hl hr hx hy
      have br := Within.branch (regs := s1) (test := .register 7) (b := false)
        (yes := .call d.cmp [.register 3, .register 5] [6, 8]
          (.branch (.register 8) (.ret [.flag true]) (secondBody d.cmp)))
        (by simp [Atom.eval, s1, bindResults, hex]) sec
      have c1 := Within.call (procedure := d.cmp) (regs := r2)
        (arguments := [.register 2, .register 4]) (results := [6, 7])
        (by simpa only [a1] using run1) br
      have hm' : edgeMatch q.1 q.2 e = (decide (e.1 = q.2) && decide (e.2 = q.1)) := by
        simp [edgeMatch, hex]
      rw [hm']
      exact c1.mono (by simp; omega)
  have l2 := Within.load (regs := r1) (address := .register 1) (first := 4) (second := 5)
    (bit := 15) (branches := { CompiledTrie.failCases with pair := inner })
    (by simp [Atom.eval, r1, regs, loadRegisters, decoded, initialRegisters]) c2 tree
  have l1 := Within.load (regs := regs) (address := .register 0) (first := 2) (second := 3)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 1) 4 5 15 { CompiledTrie.failCases with pair := inner } })
    (by simp [Atom.eval, regs, initialRegisters]) c1 l2
  rw [hitem]
  exact l1.mono (by simp [itemBudget]; omega)

/-! ## The adjacency procedure -/

def budget (W m : ℕ) : ℕ := (itemBudget W + 30) * m + 40

theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {ep xp yp : Ptr} {es : List (Bits W × Bits W)}
    {x y : Bits W} (he : EdgeWordsAt h ep es) (hx : BitsAt h xp x) (hy : BitsAt h yp y) :
    ∃ out, Extends h out ∧ Valid out ∧
      Within code h (initialRegisters [.pointer ep, .pointer xp, .pointer yp]) (code d.self)
        [.flag (es.any (edgeMatch x y))] out (budget W es.length) := by
  obtain ⟨e1, v1, c1⟩ := allocate_fits hh (pair_fits hx.allocated hy.allocated)
  have hq : QueryAt (h ++ [.pair xp yp]) h.length (x, y) := ⟨xp, yp, c1, hx.mono e1, hy.mono e1⟩
  obtain ⟨out, q, e2, v2, -, -, run⟩ := RegisterListFind.compiled_const code d.find d.item
    hm.2.2.1 EdgeAt QueryAt (fun he _ _ hx => hx.mono he) (fun he _ _ hx => EdgeAt.mono he hx)
    (fun qq e => edgeMatch qq.1 qq.2 e) (itemBudget W) v1 (he.mono e1) hq
    (fun hv _ _ _ hx hq => ⟨_, .refl _, hv, item_compiled code d hm hx hq⟩)
  have hany : (es.find? (fun e => edgeMatch x y e)).isSome = es.any (edgeMatch x y) := by
    apply Bool.eq_iff_iff.mpr
    simp
  rw [hany] at run
  refine ⟨out, e1.trans e2, v2, ?_⟩
  let regs := initialRegisters [Value.pointer ep, .pointer xp, .pointer yp]
  let r1 := Function.update regs 3 (.pointer h.length)
  let r2 := bindResults r1 [4, 5] [.flag (es.any (edgeMatch x y)), .pointer q]
  have last : Within code out r2 (.ret [.register 4]) [.flag (es.any (edgeMatch x y))] out 3 := by
    simpa [values, Atom.eval, r2, bindResults] using Within.ret code out r2 [.register 4]
  have a1 : values r1 [.register 0, .register 3] = [.pointer ep, .pointer h.length] := by
    simp [values, Atom.eval, r1, regs, initialRegisters]
  have c := Within.call (procedure := d.find) (regs := r1)
    (arguments := [.register 0, .register 3]) (results := [4, 5])
    (by simpa only [a1] using run) last
  have al := Within.allocate (regs := regs) (dst := 3) (h := h)
    (expr := .pair (.register 1) (.register 2)) (c := .pair xp yp)
    (by simp [CellExpr.eval, Atom.eval, regs, initialRegisters, Value.asPointer]) c
  rw [hm.2.2.2]
  exact al.mono (by simp [CellExpr.args, budget]; omega)

/-- On the encoded edge list of a graph the flag is endpoint adjacency. -/
theorem compiled_adj (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {W n m : ℕ} (hn : n < 2 ^ W) (left right : Fin m → Fin n) (u v : Fin n)
    {h : Heap} (hh : Valid h) {ep xp yp : Ptr}
    (he : EdgeWordsAt h ep (GraphReachEncoded.edgeWords W left right))
    (hx : BitsAt h xp (GraphReachEncoded.word W u.val))
    (hy : BitsAt h yp (GraphReachEncoded.word W v.val)) :
    ∃ out b, Extends h out ∧ Valid out ∧ (b = true ↔ EdgeTransport.Adj left right u v) ∧
      Within code h (initialRegisters [.pointer ep, .pointer xp, .pointer yp]) (code d.self)
        [.flag b] out (budget W m) := by
  obtain ⟨out, ext, valid, run⟩ := compiled code d hm hh he hx hy
  refine ⟨out, _, ext, valid, adj_words hn left right u v, ?_⟩
  simpa [GraphReachEncoded.edgeWords] using run

end WeightedMIS.RegisterAdjacencyScan
