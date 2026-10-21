module

public import WeightedMIS.SupportCycleWords
public import WeightedMIS.RegisterRationalCut
public import WeightedMIS.RegisterListFlatMap
public import WeightedMIS.RegisterListZip

/-!
# Compiled arc records of the signed support graph

An arc record is the cell `.bit active body` with `body = .pair key states`,
`states = .pair source target`; the key, source and target are binary words
of width `W + 1` (orientation or sign bit followed by an index or vertex
word), so arc identity and state equality are single comparator calls.

For one rational coordinate word and one edge-table entry
`.pair indexWord (.pair leftWord rightWord)`, `arcPair` reads the sign and the
binary zero test of the coordinate and builds the record pair of both
orientations, exactly `SupportCycleWords.arcPairW`. Zipping over the stored
row and the table and flattening the pairs yields `arcsW (pairsW xs table)`.
The three predicates used by the searches (active, successor, same arc) are
fixed bodies with constant cost plus one comparator call.
-/

@[expose] public section

namespace WeightedMIS.RegisterSupportArcs

open PointerMemory RegisterMachine EfficientSearch EfficientSearch.Pointer StoredRational
open SupportCycleWords
open RegisterIncidenceRows (EdgeAt)
open RegisterRationalRow (RowAt)

variable {p W N : ℕ}

/-! ## Representations -/

def ArcWAt (h : Heap) (ptr : Ptr) (a : ArcW W) : Prop :=
  ∃ bp kp sp srcp tgtp, h[ptr]? = some (.bit a.active bp) ∧ h[bp]? = some (.pair kp sp) ∧
    BitsAt h kp a.key ∧ h[sp]? = some (.pair srcp tgtp) ∧ BitsAt h srcp a.source ∧
    BitsAt h tgtp a.target

theorem ArcWAt.mono {h out : Heap} (ext : Extends h out) {ptr : Ptr} {a : ArcW W}
    (ha : ArcWAt h ptr a) : ArcWAt out ptr a := by
  obtain ⟨bp, kp, sp, srcp, tgtp, c1, c2, hk, c3, hs, ht⟩ := ha
  exact ⟨bp, kp, sp, srcp, tgtp, ext.lookup c1, ext.lookup c2, hk.mono ext, ext.lookup c3,
    hs.mono ext, ht.mono ext⟩

theorem ArcWAt.allocated {h : Heap} {ptr : Ptr} {a : ArcW W} (ha : ArcWAt h ptr a) :
    ptr < h.length := by
  obtain ⟨_, _, _, _, _, c1, _⟩ := ha
  exact List.getElem?_eq_some_iff.mp c1 |>.1

/-- A pair record of the two arcs of one edge. -/
def PairAt (h : Heap) (ptr : Ptr) (pr : ArcW W × ArcW W) : Prop :=
  ∃ a b, h[ptr]? = some (.pair a b) ∧ ArcWAt h a pr.1 ∧ ArcWAt h b pr.2

theorem PairAt.mono {h out : Heap} (ext : Extends h out) {ptr : Ptr} {pr : ArcW W × ArcW W}
    (hp : PairAt h ptr pr) : PairAt out ptr pr := by
  obtain ⟨a, b, c, ha, hb⟩ := hp
  exact ⟨a, b, ext.lookup c, ha.mono ext, hb.mono ext⟩

theorem PairAt.allocated {h : Heap} {ptr : Ptr} {pr : ArcW W × ArcW W} (hp : PairAt h ptr pr) :
    ptr < h.length := by
  obtain ⟨_, _, c, _⟩ := hp
  exact List.getElem?_eq_some_iff.mp c |>.1

/-- An edge-table entry `.pair indexWord (.pair leftWord rightWord)`. -/
def TableAt (h : Heap) (ptr : Ptr) (t : EdgeW W) : Prop :=
  ∃ ip ep, h[ptr]? = some (.pair ip ep) ∧ BitsAt h ip t.1 ∧ EdgeAt h ep t.2

theorem TableAt.mono {h out : Heap} (ext : Extends h out) {ptr : Ptr} {t : EdgeW W}
    (ht : TableAt h ptr t) : TableAt out ptr t := by
  obtain ⟨ip, ep, c, hi, he⟩ := ht
  exact ⟨ip, ep, ext.lookup c, hi.mono ext, he.mono ext⟩

theorem TableAt.allocated {h : Heap} {ptr : Ptr} {t : EdgeW W} (ht : TableAt h ptr t) :
    ptr < h.length := by
  obtain ⟨_, _, c, _⟩ := ht
  exact List.getElem?_eq_some_iff.mp c |>.1

/-- One checked allocation. -/
theorem alloc {h : Heap} (hh : Valid h) (c : Cell)
    (hc : ∀ q : ℕ, q ∈ c.references → q < h.length) :
    Extends h (h ++ [c]) ∧ Valid (h ++ [c]) ∧ (h ++ [c])[h.length]? = some c := by
  have safe := safe_allocate h hh c hc
  exact ⟨safe.1, safe.2.1, by simp⟩

theorem lt_of_extends {h h' : Heap} (e : Extends h h') {q : Ptr} (hq : q < h.length) :
    q < h'.length := lt_of_lt_of_le hq e.length_le

/-- Discharge the reference bound of a fresh cell built from allocated pointers. -/
macro "fits_tac" : tactic => `(tactic| (
  intro q hq
  simp (config := { zetaDelta := true }) only [Cell.references, List.mem_cons,
    List.not_mem_nil, or_false] at hq
  rcases hq with hq | hq <;> (try subst hq) <;>
  first
  | exact Nat.lt_of_lt_of_le ‹_› (by simp (config := { zetaDelta := true }))
  | simp (config := { zetaDelta := true })))

/-! ## Building one arc record -/

/-- Arguments 0=active, 1=orientation, 2=index word, 3=source sign, 4=source
vertex word, 5=target sign, 6=target vertex word. -/
def mkArcBody : Command p :=
  .allocate 7 (.bit (.register 3) (.register 4))
    (.allocate 8 (.bit (.register 5) (.register 6))
      (.allocate 9 (.pair (.register 7) (.register 8))
        (.allocate 10 (.bit (.register 1) (.register 2))
          (.allocate 11 (.pair (.register 10) (.register 9))
            (.allocate 12 (.bit (.register 0) (.register 11)) (.ret [.register 12]))))))

theorem mkArc_compiled (code : Code p) (self : Fin p) (hself : code self = mkArcBody)
    {h : Heap} (hh : Valid h) {ip sv tv : Ptr} {act back ss ts : Bool} {idx srcV tgtV : Bits W}
    (hi : BitsAt h ip idx) (hs : BitsAt h sv srcV) (ht : BitsAt h tv tgtV) :
    ∃ out ptr, Extends h out ∧ Valid out ∧
      ArcWAt out ptr ⟨act, .cons back idx, .cons ss srcV, .cons ts tgtV⟩ ∧
      Within code h (initialRegisters [.flag act, .flag back, .pointer ip, .flag ss, .pointer sv,
        .flag ts, .pointer tv]) (code self) [.pointer ptr] out 51 := by
  have hia := hi.allocated
  have hsa := hs.allocated
  have hta := ht.allocated
  let c1 : Cell := .bit ss sv
  obtain ⟨e1, v1, l1⟩ := alloc hh c1 (by fits_tac)
  let h1 := h ++ [c1]
  let c2 : Cell := .bit ts tv
  obtain ⟨e2, v2, l2⟩ := alloc v1 c2 (by fits_tac)
  let h2 := h1 ++ [c2]
  let c3 : Cell := .pair h.length h1.length
  obtain ⟨e3, v3, l3⟩ := alloc v2 c3 (by fits_tac)
  let h3 := h2 ++ [c3]
  let c4 : Cell := .bit back ip
  obtain ⟨e4, v4, l4⟩ := alloc v3 c4 (by fits_tac)
  let h4 := h3 ++ [c4]
  let c5 : Cell := .pair h3.length h2.length
  obtain ⟨e5, v5, l5⟩ := alloc v4 c5 (by fits_tac)
  let h5 := h4 ++ [c5]
  let c6 : Cell := .bit act h4.length
  obtain ⟨e6, v6, l6⟩ := alloc v5 c6 (by fits_tac)
  let h6 := h5 ++ [c6]
  have e16 : Extends h h6 := e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))
  have e26 : Extends h1 h6 := e2.trans (e3.trans (e4.trans (e5.trans e6)))
  have e36 : Extends h2 h6 := e3.trans (e4.trans (e5.trans e6))
  have e46 : Extends h3 h6 := e4.trans (e5.trans e6)
  have e56 : Extends h4 h6 := e5.trans e6
  refine ⟨h6, h5.length, e16, v6, ⟨h4.length, h3.length, h2.length, h.length, h1.length,
    l6, e6.lookup l5, .cons (e56.lookup l4) (hi.mono e16), e46.lookup l3,
    .cons (e26.lookup l1) (hs.mono e16), .cons (e36.lookup l2) (ht.mono e16)⟩, ?_⟩
  let r0 := initialRegisters [Value.flag act, .flag back, .pointer ip, .flag ss, .pointer sv,
    .flag ts, .pointer tv]
  let r1 := Function.update r0 7 (Value.pointer h.length)
  let r2 := Function.update r1 8 (Value.pointer h1.length)
  let r3 := Function.update r2 9 (Value.pointer h2.length)
  let r4 := Function.update r3 10 (Value.pointer h3.length)
  let r5 := Function.update r4 11 (Value.pointer h4.length)
  let r6 := Function.update r5 12 (Value.pointer h5.length)
  have w6 : Within code h6 r6 (.ret [.register 12]) [.pointer h5.length] h6 3 := by
    simpa [r6, values, Atom.eval] using Within.ret code h6 r6 [.register 12]
  have w5 := Within.allocate (h := h5) (regs := r5) (dst := 12)
    (expr := .bit (.register 0) (.register 11)) (c := c6)
    (by simp [CellExpr.eval, Atom.eval, r5, r4, r3, r2, r1, r0, initialRegisters,
      Value.asFlag, Value.asPointer, c6]) w6
  have w4 := Within.allocate (h := h4) (regs := r4) (dst := 11)
    (expr := .pair (.register 10) (.register 9)) (c := c5)
    (by simp [CellExpr.eval, Atom.eval, r4, r3, Value.asPointer, c5]) w5
  have w3 := Within.allocate (h := h3) (regs := r3) (dst := 10)
    (expr := .bit (.register 1) (.register 2)) (c := c4)
    (by simp [CellExpr.eval, Atom.eval, r3, r2, r1, r0, initialRegisters,
      Value.asFlag, Value.asPointer, c4]) w4
  have w2 := Within.allocate (h := h2) (regs := r2) (dst := 9)
    (expr := .pair (.register 7) (.register 8)) (c := c3)
    (by simp [CellExpr.eval, Atom.eval, r2, r1, Value.asPointer, c3]) w3
  have w1 := Within.allocate (h := h1) (regs := r1) (dst := 8)
    (expr := .bit (.register 5) (.register 6)) (c := c2)
    (by simp [CellExpr.eval, Atom.eval, r1, r0, initialRegisters,
      Value.asFlag, Value.asPointer, c2]) w2
  have w0 := Within.allocate (h := h) (regs := r0) (dst := 7)
    (expr := .bit (.register 3) (.register 4)) (c := c1)
    (by simp [CellExpr.eval, Atom.eval, r0, initialRegisters,
      Value.asFlag, Value.asPointer, c1]) w1
  rw [hself]
  exact w0.mono (by simp [CellExpr.args])

/-! ## The two arcs of one edge -/

/-- Arguments 0=sign, 1=negated sign, 2=active, 3=index word, 4=left word,
5=right word. -/
def mkPairBody (mkArc : Fin p) : Command p :=
  .call mkArc [.register 2, .flag false, .register 3, .register 1, .register 4, .register 0,
      .register 5] [6]
    (.call mkArc [.register 2, .flag true, .register 3, .register 1, .register 5, .register 0,
        .register 4] [7]
      (.allocate 8 (.pair (.register 6) (.register 7)) (.ret [.register 8])))

theorem mkPair_compiled (code : Code p) (mkArc self : Fin p) (hmk : code mkArc = mkArcBody)
    (hself : code self = mkPairBody mkArc) {h : Heap} (hh : Valid h) {ip lp rp : Ptr}
    (s a : Bool) {t : EdgeW W}
    (hi : BitsAt h ip t.1) (hl : BitsAt h lp t.2.1) (hr : BitsAt h rp t.2.2) :
    ∃ out ptr, Extends h out ∧ Valid out ∧
      PairAt out ptr (⟨a, .cons false t.1, .cons (!s) t.2.1, .cons s t.2.2⟩,
        ⟨a, .cons true t.1, .cons (!s) t.2.2, .cons s t.2.1⟩) ∧
      Within code h (initialRegisters [.flag s, .flag (!s), .flag a, .pointer ip, .pointer lp,
        .pointer rp]) (code self) [.pointer ptr] out 143 := by
  obtain ⟨m1, a0, e1, v1, h0, w0⟩ :=
    mkArc_compiled code mkArc hmk hh (act := a) (back := false) (ss := !s) (ts := s) hi hl hr
  obtain ⟨m2, a1, e2, v2, h1, w1⟩ :=
    mkArc_compiled code mkArc hmk v1 (act := a) (back := true) (ss := !s) (ts := s)
      (hi.mono e1) (hr.mono e1) (hl.mono e1)
  obtain ⟨e3, v3, l3⟩ := alloc v2 (.pair a0 a1) (by
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact (h0.mono e2).allocated
    · exact h1.allocated)
  refine ⟨m2 ++ [.pair a0 a1], m2.length, e1.trans (e2.trans e3), v3,
    ⟨a0, a1, l3, (h0.mono e2).mono e3, h1.mono e3⟩, ?_⟩
  let r0 := initialRegisters [Value.flag s, .flag (!s), .flag a, .pointer ip, .pointer lp,
    .pointer rp]
  let r1 := bindResults r0 [6] [Value.pointer a0]
  let r2 := bindResults r1 [7] [Value.pointer a1]
  have last := RegisterListCommon.within_consRet code m2 (regs := r2) (dst := 8) (head := 6)
    (tail := 7) (a := a0) (t := a1) (by simp [r2, r1, bindResults]) (by simp [r2, bindResults])
  have last' : Within code m2 r2 (.allocate 8 (.pair (.register 6) (.register 7))
      (.ret [.register 8])) [.pointer m2.length] (m2 ++ [.pair a0 a1]) 11 := by
    apply Within.allocate (budget := 3) (c := .pair a0 a1)
    · simp [CellExpr.eval, Atom.eval, r2, r1, bindResults, Value.asPointer]
    · simpa [values, Atom.eval] using
        Within.ret code (m2 ++ [.pair a0 a1]) (Function.update r2 8 (.pointer m2.length))
          [.register 8]
  clear last
  have a2 : values r1 [.register 2, .flag true, .register 3, .register 1, .register 5,
      .register 0, .register 4] =
      [.flag a, .flag true, .pointer ip, .flag (!s), .pointer rp, .flag s, .pointer lp] := by
    simp [r1, r0, bindResults, initialRegisters, values, Atom.eval]
  have c2 := Within.call (procedure := mkArc) (regs := r1) (results := [7])
    (arguments := [.register 2, .flag true, .register 3, .register 1, .register 5, .register 0,
      .register 4]) (by simpa only [a2] using w1) last'
  have a1' : values r0 [.register 2, .flag false, .register 3, .register 1, .register 4,
      .register 0, .register 5] =
      [.flag a, .flag false, .pointer ip, .flag (!s), .pointer lp, .flag s, .pointer rp] := by
    simp [r0, initialRegisters, values, Atom.eval]
  have c1 := Within.call (procedure := mkArc) (regs := r0) (results := [6])
    (arguments := [.register 2, .flag false, .register 3, .register 1, .register 4, .register 0,
      .register 5]) (by simpa only [a1'] using w0) c2
  rw [hself]
  exact c1.mono (by simp)

/-- Call the pair builder with constant sign and activity flags. -/
def pairCall (mkPair : Fin p) (s a : Bool) : Command p :=
  .call mkPair [.flag s, .flag (!s), .flag a, .register 3, .register 5, .register 6] [11]
    (.ret [.register 11])

/-- Arguments 0=coordinate record, 1=table entry, 2=unused data. -/
def arcPairBody (read zeroTest mkPair : Fin p) : Command p :=
  RegisterPairReads.readPairs [(1, 3, 4), (4, 5, 6)]
    (.call read [.register 0] [7, 8, 9]
      (.call zeroTest [.register 0] [10]
        (.branch (.register 10) (pairCall mkPair true false)
          (.branch (.register 7) (pairCall mkPair false true) (pairCall mkPair true true)))))

def arcPairBudget (N : ℕ) : ℕ := 60 * N + 300

theorem arcPair_compiled (code : Code p) (read zero compare zeroTest mkArc mkPair self : Fin p)
    (hread : code read = StoredRational.readBody)
    (hzero : code zero = RegisterZero.zeroBody zero)
    (hcompare : code compare = RegisterComparator.comparatorBody compare)
    (hzt : code zeroTest = RegisterRationalZero.body read zero compare)
    (hmk : code mkArc = mkArcBody) (hmp : code mkPair = mkPairBody mkArc)
    (hself : code self = arcPairBody read zeroTest mkPair)
    {h : Heap} (hh : Valid h) {xp tp dp : Ptr} {q : BinaryRational.Word N} {t : EdgeW W}
    (hq : At h xp q) (ht : TableAt h tp t) :
    ∃ out ptr, Extends h out ∧ Valid out ∧ PairAt out ptr (arcPairW q t) ∧
      Within code h (initialRegisters [.pointer xp, .pointer tp, .pointer dp]) (code self)
        [.pointer ptr] out (arcPairBudget N) := by
  obtain ⟨ip, ep, ct, hi, lp, rp, ce, hl, hr⟩ := ht
  obtain ⟨np, dnp, -, -, readQ⟩ := StoredRational.read_compiled code hq
  obtain ⟨mid, e1, v1, tested⟩ :=
    RegisterRationalZero.compiled code read zero compare hread hzero hcompare hh hq
  obtain ⟨out, ptr, e2, v2, hpair, built⟩ := mkPair_compiled code mkArc mkPair hmk hmp v1
    (signW q) (activeW q) (t := t) (hi.mono e1) (hl.mono e1) (hr.mono e1)
  refine ⟨out, ptr, e1.trans e2, v2, hpair, ?_⟩
  let r0 := initialRegisters [Value.pointer xp, .pointer tp, .pointer dp]
  let r1 := loadRegisters r0 3 4 15 (.pair ip ep)
  let r2 := loadRegisters r1 5 6 15 (.pair lp rp)
  have reads : RegisterPairReads.Reads h r0 [(1, 3, 4), (4, 5, 6)] r2 := by
    refine .cons (ptr := tp) (by simp [r0, initialRegisters]) ct ?_
    refine .cons (ptr := ep) (by simp [loadRegisters, decoded]) ce ?_
    exact .nil _
  let r3 := bindResults r2 [7, 8, 9] [Value.flag q.negative, .pointer np, .pointer dnp]
  let z := (BinaryRational.isZero q).1
  let r4 := bindResults r3 [10] [Value.flag z]
  have finish : ∀ s a : Bool, signW q = s → activeW q = a →
      Within code mid r4 (pairCall mkPair s a) [.pointer ptr] out (1 + 2 * 6 + 143 + 3) := by
    intro s a hs ha
    rw [← hs, ← ha]
    have last : Within code out (bindResults r4 [11] [.pointer ptr]) (.ret [.register 11])
        [.pointer ptr] out 3 := by
      simpa [bindResults, values, Atom.eval] using
        Within.ret code out (bindResults r4 [11] [.pointer ptr]) [.register 11]
    have args : values r4 [.flag (signW q), .flag (!signW q), .flag (activeW q), .register 3,
        .register 5, .register 6] = [.flag (signW q), .flag (!signW q), .flag (activeW q),
        .pointer ip, .pointer lp, .pointer rp] := by
      simp [r4, r3, r2, r1, bindResults, loadRegisters, decoded, values, Atom.eval]
    exact Within.call (procedure := mkPair) (regs := r4) (results := [11])
      (by simpa only [args] using built) last
  have h10 : (Atom.register 10).eval r4 = .flag z := by simp [r4, bindResults, Atom.eval]
  have h7 : (Atom.register 7).eval r4 = .flag q.negative := by
    simp [r4, r3, bindResults, Atom.eval]
  have branched : Within code mid r4
      (.branch (.register 10) (pairCall mkPair true false)
        (.branch (.register 7) (pairCall mkPair false true) (pairCall mkPair true true)))
      [.pointer ptr] out (3 + (3 + (1 + 2 * 6 + 143 + 3))) := by
    cases hz : z
    · refine Within.branch (b := false) (by rw [h10, hz]) ?_
      cases hn : q.negative
      · exact Within.branch (b := false) (by rw [h7, hn])
          (finish true true (by simp [signW, hn]) (by simp [activeW, zeroW, ← hz, z]))
      · exact Within.branch (b := true) (by rw [h7, hn])
          (finish false true (by simp [signW, zeroW, hn, ← hz, z])
            (by simp [activeW, zeroW, ← hz, z]))
    · exact (Within.branch (b := true) (by rw [h10, hz])
        (finish true false (by simp [signW, zeroW, ← hz, z]) (by simp [activeW, zeroW, ← hz, z]))).mono
          (by omega)
  have zArgs : values r3 [.register 0] = [.pointer xp] := by
    simp [r3, r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
  have zCall := Within.call (procedure := zeroTest) (regs := r3) (results := [10])
    (arguments := [.register 0]) (by simpa only [zArgs, hzt] using tested) branched
  have rArgs : values r2 [.register 0] = [.pointer xp] := by
    simp [r2, r1, r0, loadRegisters, decoded, initialRegisters, values, Atom.eval]
  have rCall := Within.call (procedure := read) (regs := r2) (results := [7, 8, 9])
    (arguments := [.register 0]) (by simpa only [rArgs, hread] using readQ) zCall
  have whole := reads.within rCall
  rw [hself]
  exact whole.mono (by simp [arcPairBudget]; omega)

/-! ## Flattening and predicates -/

/-- FlatMap item: arguments 0=pair record, 1=unused data, 2=accumulator. -/
def splitBody : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    pair := .allocate 5 (.cons (.register 4) (.register 2))
      (.allocate 6 (.cons (.register 3) (.register 5)) (.ret [.register 6])) }

theorem split_compiled (code : Code p) (self : Fin p) (hself : code self = splitBody)
    {h : Heap} (hh : Valid h) {pp dp acc : Ptr} {pr : ArcW W × ArcW W} {tail : List (ArcW W)}
    (hp : PairAt h pp pr) (ha : ListRep ArcWAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧ ListRep ArcWAt out q ([pr.1, pr.2] ++ tail) ∧
      Within code h (initialRegisters [.pointer pp, .pointer dp, .pointer acc]) (code self)
        [.pointer q] out 29 := by
  obtain ⟨a0, a1, cell, h0, h1⟩ := hp
  have mono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr (x : ArcW W), ArcWAt h ptr x →
      ArcWAt h' ptr x := fun e _ _ hx => hx.mono e
  obtain ⟨e1, v1, l1⟩ := RegisterListCommon.allocate_consRep mono hh h1 h1.allocated ha
  let m1 := h ++ [.cons a1 acc]
  obtain ⟨e2, v2, l2⟩ := RegisterListCommon.allocate_consRep mono v1 (h0.mono e1)
    (h0.mono e1).allocated l1
  refine ⟨_, _, e1.trans e2, v2, l2, ?_⟩
  let r0 := initialRegisters [Value.pointer pp, .pointer dp, .pointer acc]
  let r1 := loadRegisters r0 3 4 15 (.pair a0 a1)
  let r2 := Function.update r1 5 (Value.pointer h.length)
  have last := RegisterListCommon.within_consRet code m1 (regs := r2) (dst := 6) (head := 3)
    (tail := 5) (a := a0) (t := h.length)
    (by simp [r2, r1, loadRegisters, decoded]) (by simp [r2])
  have alloc5 := Within.allocate (h := h) (regs := r1) (dst := 5)
    (expr := .cons (.register 4) (.register 2)) (c := .cons a1 acc)
    (by simp [CellExpr.eval, Atom.eval, r1, r0, loadRegisters, decoded, initialRegisters,
      Value.asPointer]) last
  have loaded := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
    (branches := { CompiledTrie.failCases with
      pair := .allocate 5 (.cons (.register 4) (.register 2))
        (.allocate 6 (.cons (.register 3) (.register 5)) (.ret [.register 6])) })
    (by simp [Atom.eval, r0, initialRegisters]) cell alloc5
  rw [hself]
  exact loaded.mono (by simp [CellExpr.args])

/-- Find item: arguments 0=arc, 1=unused data; the result is the active flag. -/
def activeBody : Command p :=
  .load (.register 0) 2 3 4 { CompiledTrie.failCases with bit := .ret [.register 4] }

theorem active_compiled (code : Code p) (self : Fin p) (hself : code self = activeBody)
    {h : Heap} {ap dp : Ptr} {a : ArcW W} (ha : ArcWAt h ap a) :
    Within code h (initialRegisters [.pointer ap, .pointer dp]) (code self) [.flag a.active] h
      13 := by
  obtain ⟨bp, _, _, _, _, cell, _⟩ := ha
  let r0 := initialRegisters [Value.pointer ap, .pointer dp]
  have last : Within code h (loadRegisters r0 2 3 4 (.bit a.active bp)) (.ret [.register 4])
      [.flag a.active] h 3 := by
    simpa [values, Atom.eval, loadRegisters, decoded] using
      Within.ret code h (loadRegisters r0 2 3 4 (.bit a.active bp)) [.register 4]
  rw [hself]
  exact Within.load (address := .register 0) (first := 2) (second := 3) (bit := 4)
    (branches := { CompiledTrie.failCases with bit := .ret [.register 4] })
    (by simp [Atom.eval, r0, initialRegisters]) cell last

/-- Comparison of the source state of the loaded arc body (register 2) with
the state word in register 1. -/
def succTail (compare : Fin p) : Command p :=
  .load (.register 2) 5 6 15 { CompiledTrie.failCases with
    pair := .load (.register 6) 7 8 15 { CompiledTrie.failCases with
      pair := .call compare [.register 7, .register 1] [9, 10] (.ret [.register 10]) } }

/-- Find item: arguments 0=arc, 1=state word; the result is `succPred`. -/
def succBody (compare : Fin p) : Command p :=
  .load (.register 0) 2 3 4 { CompiledTrie.failCases with
    bit := .branch (.register 4) (succTail compare) (.ret [.flag false]) }

def predBudget (W : ℕ) : ℕ := 36 * W + 120

theorem succ_compiled (code : Code p) (compare self : Fin p)
    (hcompare : code compare = RegisterComparator.comparatorBody compare)
    (hself : code self = succBody compare)
    {h : Heap} {bp tp : Ptr} {b : ArcW W} {t : StateW W} (hb : ArcWAt h bp b) (ht : BitsAt h tp t) :
    Within code h (initialRegisters [.pointer bp, .pointer tp]) (code self) [.flag (succPred t b)]
      h (predBudget W) := by
  obtain ⟨body, kp, sp, srcp, tgtp, c1, c2, -, c3, hs, -⟩ := hb
  let r0 := initialRegisters [Value.pointer bp, .pointer tp]
  let r1 := loadRegisters r0 2 3 4 (.bit b.active body)
  have h4 : (Atom.register 4).eval r1 = .flag b.active := by
    simp [r1, loadRegisters, decoded, Atom.eval]
  have tail : Within code h r1 (if b.active then succTail compare else .ret [.flag false])
      [.flag (succPred t b)] h (36 * (W + 1) + 25 + 28) := by
    cases hact : b.active
    · simpa [succPred, hact, values, Atom.eval] using
        (Within.ret code h r1 [.flag false]).mono (b := 36 * (W + 1) + 25 + 28) (by simp)
    · simp only [↓reduceIte]
      let r2 := loadRegisters r1 5 6 15 (.pair kp sp)
      let r3 := loadRegisters r2 7 8 15 (.pair srcp tgtp)
      let flags := RegisterComparator.flags (Bits.compare b.source t).1
      let r4 := bindResults r3 [9, 10] flags
      have last : Within code h r4 (.ret [.register 10]) [.flag (succPred t b)] h 3 := by
        simpa [r4, flags, RegisterComparator.flags, succPred, hact, RegisterIncidenceRows.eqb, bindResults, values,
          Atom.eval] using Within.ret code h r4 [.register 10]
      have cargs : values r3 [.register 7, .register 1] = [.pointer srcp, .pointer tp] := by
        simp [r3, r2, r1, r0, loadRegisters, decoded, initialRegisters, values, Atom.eval]
      have ccall := Within.call (procedure := compare) (regs := r3) (results := [9, 10])
        (arguments := [.register 7, .register 1])
        (by simpa only [cargs, hcompare] using
          RegisterComparator.compiled code compare hcompare hs ht) last
      have l2 := Within.load (address := .register 6) (first := 7) (second := 8) (bit := 15)
        (branches := { CompiledTrie.failCases with
          pair := .call compare [.register 7, .register 1] [9, 10] (.ret [.register 10]) })
        (by simp [Atom.eval, r2, loadRegisters, decoded]) c3 ccall
      have l1 := Within.load (address := .register 2) (first := 5) (second := 6) (bit := 15)
        (branches := { CompiledTrie.failCases with
          pair := .load (.register 6) 7 8 15 { CompiledTrie.failCases with
            pair := .call compare [.register 7, .register 1] [9, 10] (.ret [.register 10]) } })
        (by simp [Atom.eval, r1, loadRegisters, decoded]) c2 l2
      exact l1.mono (by simp only [List.length_cons, List.length_nil]; omega)
  have br := Within.branch h4 tail
  rw [hself]
  exact (Within.load (address := .register 0) (first := 2) (second := 3) (bit := 4)
    (branches := { CompiledTrie.failCases with
      bit := .branch (.register 4) (succTail compare) (.ret [.flag false]) })
    (by simp [Atom.eval, r0, initialRegisters]) c1 br).mono (by simp [predBudget]; omega)

/-- Comparison of the key of the loaded arc body (register 5) with the key of
the arc in register 1. -/
def sameTail (compare : Fin p) : Command p :=
  .load (.register 1) 6 7 8 { CompiledTrie.failCases with
    bit := .load (.register 6) 9 10 15 { CompiledTrie.failCases with
      pair := .call compare [.register 5, .register 9] [11, 12] (.ret [.register 12]) } }

/-- Find item: arguments 0=arc `b`, 1=arc `a`; the result is `samePred a b`. -/
def sameBody (compare : Fin p) : Command p :=
  .load (.register 0) 2 3 4 { CompiledTrie.failCases with
    bit := .load (.register 2) 5 6 15 { CompiledTrie.failCases with pair := sameTail compare } }

theorem same_compiled (code : Code p) (compare self : Fin p)
    (hcompare : code compare = RegisterComparator.comparatorBody compare)
    (hself : code self = sameBody compare)
    {h : Heap} {bp ap : Ptr} {b a : ArcW W} (hb : ArcWAt h bp b) (ha : ArcWAt h ap a) :
    Within code h (initialRegisters [.pointer bp, .pointer ap]) (code self) [.flag (samePred a b)]
      h (predBudget W) := by
  obtain ⟨bbody, bk, bs, -, -, b1, b2, hbk, -⟩ := hb
  obtain ⟨abody, ak, as, -, -, a1, a2, hak, -⟩ := ha
  let r0 := initialRegisters [Value.pointer bp, .pointer ap]
  let r1 := loadRegisters r0 2 3 4 (.bit b.active bbody)
  let r2 := loadRegisters r1 5 6 15 (.pair bk bs)
  let r3 := loadRegisters r2 6 7 8 (.bit a.active abody)
  let r4 := loadRegisters r3 9 10 15 (.pair ak as)
  let flags := RegisterComparator.flags (Bits.compare b.key a.key).1
  let r5 := bindResults r4 [11, 12] flags
  have last : Within code h r5 (.ret [.register 12]) [.flag (samePred a b)] h 3 := by
    simpa [r5, flags, RegisterComparator.flags, samePred, RegisterIncidenceRows.eqb, bindResults, values,
      Atom.eval] using Within.ret code h r5 [.register 12]
  have cargs : values r4 [.register 5, .register 9] = [.pointer bk, .pointer ak] := by
    simp [r4, r3, r2, loadRegisters, decoded, values, Atom.eval]
  have ccall := Within.call (procedure := compare) (regs := r4) (results := [11, 12])
    (arguments := [.register 5, .register 9])
    (by simpa only [cargs, hcompare] using
      RegisterComparator.compiled code compare hcompare hbk hak) last
  have l4 := Within.load (address := .register 6) (first := 9) (second := 10) (bit := 15)
    (branches := { CompiledTrie.failCases with
      pair := .call compare [.register 5, .register 9] [11, 12] (.ret [.register 12]) })
    (by simp [Atom.eval, r3, loadRegisters, decoded]) a2 ccall
  have l3 := Within.load (address := .register 1) (first := 6) (second := 7) (bit := 8)
    (branches := { CompiledTrie.failCases with
      bit := .load (.register 6) 9 10 15 { CompiledTrie.failCases with
        pair := .call compare [.register 5, .register 9] [11, 12] (.ret [.register 12]) } })
    (by simp [Atom.eval, r2, r1, r0, loadRegisters, decoded, initialRegisters]) a1 l4
  have l2 := Within.load (address := .register 2) (first := 5) (second := 6) (bit := 15)
    (branches := { CompiledTrie.failCases with pair := sameTail compare })
    (by simp [Atom.eval, r1, loadRegisters, decoded]) b2 l3
  have l1 := Within.load (address := .register 0) (first := 2) (second := 3) (bit := 4)
    (branches := { CompiledTrie.failCases with
      bit := .load (.register 2) 5 6 15 { CompiledTrie.failCases with pair := sameTail compare } })
    (by simp [Atom.eval, r0, initialRegisters]) b1 l2
  rw [hself]
  exact l1.mono (by simp [predBudget]; omega)

/-! ## Procedure table and list stages -/

structure Procedures (p : ℕ) where
  read : Fin p
  zero : Fin p
  compare : Fin p
  zeroTest : Fin p
  mkArc : Fin p
  mkPair : Fin p
  arcPair : Fin p
  zipArcs : Fin p
  split : Fin p
  flatArcs : Fin p
  active : Fin p
  succ : Fin p
  same : Fin p

structure Procedures.Matches (ids : Procedures p) (code : Code p) : Prop where
  read : code ids.read = StoredRational.readBody
  zero : code ids.zero = RegisterZero.zeroBody ids.zero
  compare : code ids.compare = RegisterComparator.comparatorBody ids.compare
  zeroTest : code ids.zeroTest = RegisterRationalZero.body ids.read ids.zero ids.compare
  mkArc : code ids.mkArc = mkArcBody
  mkPair : code ids.mkPair = mkPairBody ids.mkArc
  arcPair : code ids.arcPair = arcPairBody ids.read ids.zeroTest ids.mkPair
  zipArcs : code ids.zipArcs = RegisterListZip.body ids.zipArcs ids.arcPair
  split : code ids.split = splitBody
  flatArcs : code ids.flatArcs = RegisterListFlatMap.body ids.flatArcs ids.split
  active : code ids.active = activeBody
  succ : code ids.succ = succBody ids.compare
  same : code ids.same = sameBody ids.compare

def pairsBudget (N k : ℕ) : ℕ := (arcPairBudget N + 45) * k + 23

/-- Arguments 0=coordinate row, 1=edge table, 2=null. -/
theorem pairs_compiled (code : Code p) (ids : Procedures p) (hcode : ids.Matches code)
    {h : Heap} (hh : Valid h) {xp tp : Ptr} {xs : List (BinaryRational.Word N)}
    {table : List (EdgeW W)} (hx : RowAt h xp xs) (ht : ListRep TableAt h tp table) :
    ∃ out q, Extends h out ∧ Valid out ∧ ListRep PairAt out q (pairsW xs table) ∧
      Within code h (initialRegisters [.pointer xp, .pointer tp, .pointer 0]) (code ids.zipArcs)
        [.pointer q] out (pairsBudget N (min xs.length table.length)) := by
  obtain ⟨out, q, e, v, hq, w⟩ := RegisterListZip.compiled_const code ids.zipArcs ids.arcPair
    hcode.zipArcs (fun heap ptr (x : BinaryRational.Word N) => At heap ptr x) TableAt
    (fun _ _ (_ : Unit) => True) PairAt (fun ext _ _ hx => hx.mono ext)
    (fun ext _ _ hx => hx.mono ext) (fun _ _ _ _ => trivial) (fun ext _ _ hx => hx.mono ext)
    (fun _ hx => hx.allocated) (fun _ x t => arcPairW x t) (arcPairBudget N) hh hx ht
    (data := ()) trivial
    (fun hv _ _ _ _ _ hxa hta _ => arcPair_compiled code ids.read ids.zero ids.compare
      ids.zeroTest ids.mkArc ids.mkPair ids.arcPair hcode.read hcode.zero hcode.compare
      hcode.zeroTest hcode.mkArc hcode.mkPair hcode.arcPair hv hxa hta)
  exact ⟨out, q, e, v, hq, w⟩

def arcsBudget (k : ℕ) : ℕ := 56 * k + 13

/-- Arguments 0=pair list, 1=null, 2=null. -/
theorem arcs_compiled (code : Code p) (ids : Procedures p) (hcode : ids.Matches code)
    {h : Heap} (hh : Valid h) {pp : Ptr} {pairs : List (ArcW W × ArcW W)}
    (hp : ListRep PairAt h pp pairs) :
    ∃ out q, Extends h out ∧ Valid out ∧ ListRep ArcWAt out q (arcsW pairs) ∧
      Within code h (initialRegisters [.pointer pp, .pointer 0, .pointer 0]) (code ids.flatArcs)
        [.pointer q] out (arcsBudget pairs.length) := by
  obtain ⟨out, q, e, v, hq, w⟩ := RegisterListFlatMap.compiled code ids.flatArcs ids.split
    hcode.flatArcs PairAt (fun _ _ (_ : Unit) => True) (ListRep ArcWAt)
    (fun ext _ _ hx => hx.mono ext) (fun _ _ _ _ => trivial)
    (fun _ pr => [pr.1, pr.2]) 29
    (fun hv _ _ _ _ _ _ hx _ ha => split_compiled code ids.split hcode.split hv hx ha)
    hh hp (data := ()) trivial (RegisterListCommon.listRep_null hh)
  refine ⟨out, q, e, v, by simpa [arcsW] using hq, w.mono (by simp [arcsBudget])⟩

end WeightedMIS.RegisterSupportArcs
