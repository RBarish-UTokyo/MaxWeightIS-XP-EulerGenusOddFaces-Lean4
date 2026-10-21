module

public import WeightedMIS.RegisterSupportCycle

/-!
# Compiled generator words, rational views and pivot test

Representations and item procedures of one decomposition round. The generator
item maps the arc pair of one edge to its signed generator word: two
comparator searches of the cycle decide the membership of both orientations,
the magnitude is the shared word `0`, `1` or `2`, and the sign is the leading
bit of the source state of the forward arc (`SupportCycleWords.genW`).

Integer rows are `SignedWords.ListAt` lists of signed words of width `N`; a
signed word cell `.bit negative magnitude` is exactly the sign cell of a stored
rational, so `intRow` converts an integer row into stored rationals with one
`pair` cell per coordinate and the shared denominator word `1`
(`SupportCycleWords.ratW`). The pivot test is the negated compiled binary zero
test on the second component of a stored pair `(x_e, g_e)`.
-/

@[expose] public section

namespace WeightedMIS.RegisterGeneratorWords

open PointerMemory RegisterMachine EfficientSearch EfficientSearch.Pointer StoredRational
open SupportCycleWords RegisterSupportArcs RegisterSupportCycle
open RegisterRationalRow (RowAt)
open SignedWords (SignedAt)

variable {p W N : ℕ}

/-! ## Representations -/

/-- The shared magnitude words `.pair one (.pair zero two)`. -/
def ConstsAt (h : Heap) (ptr : Ptr) (k : Bits N × Bits N × Bits N) : Prop :=
  ∃ op r zp tp, h[ptr]? = some (.pair op r) ∧ h[r]? = some (.pair zp tp) ∧
    BitsAt h zp k.1 ∧ BitsAt h op k.2.1 ∧ BitsAt h tp k.2.2

theorem ConstsAt.mono {h out : Heap} (ext : Extends h out) {ptr : Ptr}
    {k : Bits N × Bits N × Bits N} (hk : ConstsAt h ptr k) : ConstsAt out ptr k := by
  obtain ⟨op, r, zp, tp, c1, c2, hz, ho, ht⟩ := hk
  exact ⟨op, r, zp, tp, ext.lookup c1, ext.lookup c2, hz.mono ext, ho.mono ext, ht.mono ext⟩

theorem ConstsAt.allocated {h : Heap} {ptr : Ptr} {k : Bits N × Bits N × Bits N}
    (hk : ConstsAt h ptr k) : ptr < h.length := by
  obtain ⟨_, _, _, _, c1, _⟩ := hk
  exact List.getElem?_eq_some_iff.mp c1 |>.1

/-- Data of the generator map: `.pair cycle consts`. -/
def GenDataAt (h : Heap) (ptr : Ptr) (d : List (ArcW W) × (Bits N × Bits N × Bits N)) : Prop :=
  ∃ cp kp, h[ptr]? = some (.pair cp kp) ∧ ListRep ArcWAt h cp d.1 ∧ ConstsAt h kp d.2

theorem GenDataAt.mono {h out : Heap} (ext : Extends h out) {ptr : Ptr}
    {d : List (ArcW W) × (Bits N × Bits N × Bits N)} (hd : GenDataAt h ptr d) :
    GenDataAt out ptr d := by
  obtain ⟨cp, kp, c, hc, hk⟩ := hd
  exact ⟨cp, kp, ext.lookup c, hc.mono ext (fun _ _ hx => hx.mono ext), hk.mono ext⟩

/-- Data of the decomposition: `.pair edgeTable consts`. -/
def DataAt (h : Heap) (ptr : Ptr) (d : List (EdgeW W) × (Bits N × Bits N × Bits N)) : Prop :=
  ∃ tp kp, h[ptr]? = some (.pair tp kp) ∧ ListRep TableAt h tp d.1 ∧ ConstsAt h kp d.2

theorem DataAt.mono {h out : Heap} (ext : Extends h out) {ptr : Ptr}
    {d : List (EdgeW W) × (Bits N × Bits N × Bits N)} (hd : DataAt h ptr d) :
    DataAt out ptr d := by
  obtain ⟨tp, kp, c, ht, hk⟩ := hd
  exact ⟨tp, kp, ext.lookup c, ht.mono ext (fun _ _ hx => hx.mono ext), hk.mono ext⟩

/-- A pair of stored rationals `.pair x g`. -/
def PairWAt (h : Heap) (ptr : Ptr) (d : BinaryRational.Word N × BinaryRational.Word N) : Prop :=
  ∃ a b, h[ptr]? = some (.pair a b) ∧ At h a d.1 ∧ At h b d.2

theorem PairWAt.mono {h out : Heap} (ext : Extends h out) {ptr : Ptr}
    {d : BinaryRational.Word N × BinaryRational.Word N} (hd : PairWAt h ptr d) :
    PairWAt out ptr d := by
  obtain ⟨a, b, c, ha, hb⟩ := hd
  exact ⟨a, b, ext.lookup c, ha.mono ext, hb.mono ext⟩

/-- Lists of integer rows of signed words. -/
def IntRowsAt (h : Heap) (ptr : Ptr) (rows : List (List (RegisterPotentialStep.Word N))) : Prop :=
  ListRep SignedWords.ListAt h ptr rows

theorem IntRowsAt.mono {h out : Heap} (ext : Extends h out) {ptr : Ptr}
    {rows : List (List (RegisterPotentialStep.Word N))} (hr : IntRowsAt h ptr rows) :
    IntRowsAt out ptr rows :=
  ListRep.mono ext (fun _ _ hx => hx.mono ext) hr

/-! ## Generator words -/

/-- Read the sign of the source state of arc `a0` (register 2) and store the
signed word with the magnitude in register 12. -/
def genSign : Command p :=
  .load (.register 2) 13 14 15 { CompiledTrie.failCases with
    bit := .load (.register 13) 13 14 15 { CompiledTrie.failCases with
      pair := .load (.register 14) 13 14 15 { CompiledTrie.failCases with
        pair := .load (.register 13) 13 14 15 { CompiledTrie.failCases with
          bit := .allocate 14 (.bit (.register 15) (.register 12)) (.ret [.register 14]) } } } }

def genSelect : Command p :=
  .branch (.register 10)
    (.branch (.register 11) (.copy 12 (.register 9) genSign) (.copy 12 (.register 6) genSign))
    (.branch (.register 11) (.copy 12 (.register 6) genSign) (.copy 12 (.register 8) genSign))

/-- Map item: arguments 0=arc pair, 1=generator data `.pair cycle consts`. -/
def genItemBody (memFind : Fin p) : Command p :=
  RegisterPairReads.readPairs [(0, 2, 3), (1, 4, 5), (5, 6, 7), (7, 8, 9)]
    (.call memFind [.register 4, .register 2] [10, 11]
      (.call memFind [.register 4, .register 3] [11, 12] genSelect))

def genBudget (W c : ℕ) : ℕ := (2 * predBudget W + 60) * c + 150

theorem genSign_compiled (code : Code p) {h : Heap} (hh : Valid h) {regs : Registers}
    {a0p mp : Ptr} {a0 : ArcW W} {mag : Bits N} (ha : ArcWAt h a0p a0) (hm : BitsAt h mp mag)
    (h2 : regs 2 = .pointer a0p) (h12 : regs 12 = .pointer mp) :
    ∃ out ptr, Extends h out ∧ Valid out ∧ SignedAt out ptr (headBit a0.source, mag) ∧
      Within code h regs genSign [.pointer ptr] out 51 := by
  obtain ⟨bp, kp, sp, srcp, tgtp, c1, c2, -, c3, hs, -⟩ := ha
  obtain ⟨s, v, hsv⟩ : ∃ s v, a0.source = .cons s v := by
    cases a0.source with
    | cons s v => exact ⟨s, v, rfl⟩
  rw [hsv] at hs
  cases hs with
  | @cons _ vp _ _ _ c4 hv =>
  obtain ⟨e1, v1, l1⟩ := alloc hh (.bit s mp) (by
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact hm.allocated)
  refine ⟨h ++ [.bit s mp], h.length, e1, v1, ⟨mp, by rw [hsv]; exact l1,
    hm.mono e1⟩, ?_⟩
  let r1 := loadRegisters regs 13 14 15 (.bit a0.active bp)
  let r2 := loadRegisters r1 13 14 15 (.pair kp sp)
  let r3 := loadRegisters r2 13 14 15 (.pair srcp tgtp)
  let r4 := loadRegisters r3 13 14 15 (.bit s vp)
  have last := Within.allocate (h := h) (regs := r4) (dst := 14)
    (expr := .bit (.register 15) (.register 12)) (c := .bit s mp)
    (by simp [CellExpr.eval, Atom.eval, r4, r3, r2, r1, loadRegisters, decoded, h12,
      Value.asFlag, Value.asPointer])
    (by
      simpa [values, Atom.eval] using
        Within.ret code (h ++ [.bit s mp]) (Function.update r4 14 (.pointer h.length))
          [.register 14])
  have l4 := Within.load (address := .register 13) (first := 13) (second := 14) (bit := 15)
    (branches := { CompiledTrie.failCases with
      bit := .allocate 14 (.bit (.register 15) (.register 12)) (.ret [.register 14]) })
    (by simp [Atom.eval, r3, loadRegisters, decoded]) c4 last
  have l3 := Within.load (address := .register 14) (first := 13) (second := 14) (bit := 15)
    (branches := { CompiledTrie.failCases with
      pair := .load (.register 13) 13 14 15 { CompiledTrie.failCases with
        bit := .allocate 14 (.bit (.register 15) (.register 12)) (.ret [.register 14]) } })
    (by simp [Atom.eval, r2, loadRegisters, decoded]) c3 l4
  have l2 := Within.load (address := .register 13) (first := 13) (second := 14) (bit := 15)
    (branches := { CompiledTrie.failCases with
      pair := .load (.register 14) 13 14 15 { CompiledTrie.failCases with
        pair := .load (.register 13) 13 14 15 { CompiledTrie.failCases with
          bit := .allocate 14 (.bit (.register 15) (.register 12)) (.ret [.register 14]) } } })
    (by simp [Atom.eval, r1, loadRegisters, decoded]) c2 l3
  have l1 := Within.load (address := .register 2) (first := 13) (second := 14) (bit := 15)
    (branches := { CompiledTrie.failCases with
      bit := .load (.register 13) 13 14 15 { CompiledTrie.failCases with
        pair := .load (.register 14) 13 14 15 { CompiledTrie.failCases with
          pair := .load (.register 13) 13 14 15 { CompiledTrie.failCases with
            bit := .allocate 14 (.bit (.register 15) (.register 12)) (.ret [.register 14]) } } } })
    h2 c1 l2
  exact l1.mono (by simp [CellExpr.args])

theorem genItem_compiled (code : Code p) (ids : RegisterSupportCycle.Procedures p)
    (hcode : ids.Matches code) (self : Fin p) (hself : code self = genItemBody ids.memFind)
    {h : Heap} (hh : Valid h) {pp dp : Ptr} {pr : ArcW W × ArcW W} {C : List (ArcW W)}
    {k : Bits N × Bits N × Bits N} (hp : PairAt h pp pr) (hd : GenDataAt h dp (C, k)) :
    ∃ out ptr, Extends h out ∧ Valid out ∧ SignedAt out ptr (genW k C pr) ∧
      Within code h (initialRegisters [.pointer pp, .pointer dp]) (code self) [.pointer ptr] out
        (genBudget W C.length) := by
  obtain ⟨a0p, a1p, cp0, ha0, ha1⟩ := hp
  obtain ⟨cp, kp, cd, hC, op, r, zp, tp, ck1, ck2, hz, ho, ht⟩ := hd
  obtain ⟨m1, q1, e1, v1, -, -, run1⟩ := memFind_compiled code ids hcode hh hC ha0
  obtain ⟨m2, q2, e2, v2, -, -, run2⟩ := memFind_compiled code ids hcode v1
    (hC.mono e1 (fun _ _ hx => hx.mono e1)) (ha1.mono e1)
  have e12 := e1.trans e2
  let r0 := initialRegisters [Value.pointer pp, .pointer dp]
  let r1 := loadRegisters r0 2 3 15 (.pair a0p a1p)
  let r2 := loadRegisters r1 4 5 15 (.pair cp kp)
  let r3 := loadRegisters r2 6 7 15 (.pair op r)
  let r4 := loadRegisters r3 8 9 15 (.pair zp tp)
  have reads : RegisterPairReads.Reads h r0 [(0, 2, 3), (1, 4, 5), (5, 6, 7), (7, 8, 9)] r4 := by
    refine .cons (ptr := pp) (by simp [r0, initialRegisters]) cp0 ?_
    refine .cons (ptr := dp) (by simp [r0, loadRegisters, decoded, initialRegisters]) cd ?_
    refine .cons (ptr := kp) (by simp [loadRegisters, decoded]) ck1 ?_
    refine .cons (ptr := r) (by simp [loadRegisters, decoded]) ck2 ?_
    exact .nil _
  have a1 : values r4 [.register 4, .register 2] = [.pointer cp, .pointer a0p] := by
    simp [r4, r3, r2, r1, loadRegisters, decoded, values, Atom.eval]
  have hgen : genW k C pr = (headBit pr.1.source,
      if (C.find? (samePred pr.1)).isSome then
        (if (C.find? (samePred pr.2)).isSome then k.2.2 else k.2.1)
      else (if (C.find? (samePred pr.2)).isSome then k.2.1 else k.1)) := rfl
  rw [hgen]
  generalize (C.find? (samePred pr.1)).isSome = b0 at run1 ⊢
  generalize (C.find? (samePred pr.2)).isSome = b1 at run2 ⊢
  let r5 := bindResults r4 [10, 11] [Value.flag b0, .pointer q1]
  let r6 := bindResults r5 [11, 12] [Value.flag b1, .pointer q2]
  have a2 : values r5 [.register 4, .register 3] = [.pointer cp, .pointer a1p] := by
    simp [r5, r4, r3, r2, r1, bindResults, loadRegisters, decoded, values, Atom.eval]
  have g2 : r6 2 = .pointer a0p := by
    simp [r6, r5, r4, r3, r2, r1, bindResults, loadRegisters, decoded]
  have h10 : (Atom.register 10).eval r6 = .flag b0 := by simp [r6, r5, bindResults, Atom.eval]
  have h11 : (Atom.register 11).eval r6 = .flag b1 := by simp [r6, bindResults, Atom.eval]
  have h6 : r6 6 = .pointer op := by
    simp [r6, r5, r4, r3, bindResults, loadRegisters, decoded]
  have h8 : r6 8 = .pointer zp := by
    simp [r6, r5, r4, bindResults, loadRegisters, decoded]
  have h9 : r6 9 = .pointer tp := by
    simp [r6, r5, r4, bindResults, loadRegisters, decoded]
  let mag : Bits N := if b0 then (if b1 then k.2.2 else k.2.1) else (if b1 then k.2.1 else k.1)
  obtain ⟨mp, hmp, hsel⟩ : ∃ mp, BitsAt m2 mp mag ∧
      ∀ {o : List Value} {outH : Heap} {B : ℕ},
        Within code m2 (Function.update r6 12 (.pointer mp)) genSign o outH B →
        Within code m2 r6 genSelect o outH (3 + (3 + (3 + B))) := by
    cases b0 <;> cases b1
    · refine ⟨zp, by simpa [mag] using hz.mono e12, fun hw => ?_⟩
      refine Within.branch (b := false) h10 (Within.branch (b := false) h11 ?_)
      exact Within.copy (by simpa [Atom.eval, h8] using hw)
    · refine ⟨op, by simpa [mag] using ho.mono e12, fun hw => ?_⟩
      refine Within.branch (b := false) h10 (Within.branch (b := true) h11 ?_)
      exact Within.copy (by simpa [Atom.eval, h6] using hw)
    · refine ⟨op, by simpa [mag] using ho.mono e12, fun hw => ?_⟩
      refine Within.branch (b := true) h10 (Within.branch (b := false) h11 ?_)
      exact Within.copy (by simpa [Atom.eval, h6] using hw)
    · refine ⟨tp, by simpa [mag] using ht.mono e12, fun hw => ?_⟩
      refine Within.branch (b := true) h10 (Within.branch (b := true) h11 ?_)
      exact Within.copy (by simpa [Atom.eval, h9] using hw)
  obtain ⟨out, ptr, e3, v3, hout, signRun⟩ := genSign_compiled code v2 (ha0.mono e12) hmp
    (regs := Function.update r6 12 (.pointer mp)) (by simp [g2]) (by simp)
  refine ⟨out, ptr, e12.trans e3, v3, hout, ?_⟩
  have sel := hsel signRun
  have c2 := Within.call (procedure := ids.memFind) (regs := r5) (results := [11, 12])
    (arguments := [.register 4, .register 3]) (by simpa only [a2] using run2) sel
  have c1 := Within.call (procedure := ids.memFind) (regs := r4) (results := [10, 11])
    (arguments := [.register 4, .register 2]) (by simpa only [a1] using run1) c2
  have whole := reads.within c1
  rw [hself]
  refine whole.mono ?_
  simp only [genBudget, List.length_cons, List.length_nil]
  generalize predBudget W = B
  nlinarith

/-! ## Rational views and pivot search -/

/-- Map item: arguments 0=signed word, 1=denominator word `one`. -/
def ratItemBody : Command p :=
  .allocate 2 (.pair (.register 0) (.register 1)) (.ret [.register 2])

theorem ratItem_compiled (code : Code p) (self : Fin p) (hself : code self = ratItemBody)
    {h : Heap} (hh : Valid h) {gp op : Ptr} {g : RegisterPotentialStep.Word N} {one : Bits N}
    (hg : SignedAt h gp g) (ho : BitsAt h op one) :
    ∃ out ptr, Extends h out ∧ Valid out ∧ At out ptr (ratW one g) ∧
      Within code h (initialRegisters [.pointer gp, .pointer op]) (code self) [.pointer ptr] out
        11 := by
  obtain ⟨mp, cg, hm⟩ := hg
  obtain ⟨e1, v1, l1⟩ := alloc hh (.pair gp op) (by
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact List.getElem?_eq_some_iff.mp cg |>.1
    · exact ho.allocated)
  refine ⟨_, h.length, e1, v1, ⟨gp, mp, op, l1, e1.lookup cg, hm.mono e1, ho.mono e1⟩, ?_⟩
  rw [hself]
  exact (Within.allocate (h := h) (regs := initialRegisters [.pointer gp, .pointer op]) (dst := 2)
    (expr := .pair (.register 0) (.register 1)) (c := .pair gp op)
    (by simp [CellExpr.eval, Atom.eval, initialRegisters, Value.asPointer])
    (by
      simpa [values, Atom.eval] using
        Within.ret code (h ++ [.pair gp op]) (Function.update (initialRegisters [.pointer gp,
          .pointer op]) 2 (.pointer h.length)) [.register 2])).mono (by simp [CellExpr.args])

/-- Zip item: arguments 0=rational word, 1=rational word, 2=unused data. -/
def pairItemBody : Command p :=
  .allocate 3 (.pair (.register 0) (.register 1)) (.ret [.register 3])

theorem pairItem_compiled (code : Code p) (self : Fin p) (hself : code self = pairItemBody)
    {h : Heap} (hh : Valid h) {xp gp dp : Ptr} {x g : BinaryRational.Word N}
    (hx : At h xp x) (hg : At h gp g) :
    ∃ out ptr, Extends h out ∧ Valid out ∧ PairWAt out ptr (x, g) ∧
      Within code h (initialRegisters [.pointer xp, .pointer gp, .pointer dp]) (code self)
        [.pointer ptr] out 11 := by
  obtain ⟨e1, v1, l1⟩ := alloc hh (.pair xp gp) (by
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hx.allocated
    · exact hg.allocated)
  refine ⟨_, h.length, e1, v1, ⟨xp, gp, l1, hx.mono e1, hg.mono e1⟩, ?_⟩
  rw [hself]
  exact (Within.allocate (h := h) (regs := initialRegisters [.pointer xp, .pointer gp,
      .pointer dp]) (dst := 3)
    (expr := .pair (.register 0) (.register 1)) (c := .pair xp gp)
    (by simp [CellExpr.eval, Atom.eval, initialRegisters, Value.asPointer])
    (by
      simpa [values, Atom.eval] using
        Within.ret code (h ++ [.pair xp gp]) (Function.update (initialRegisters [.pointer xp,
          .pointer gp, .pointer dp]) 3 (.pointer h.length)) [.register 3])).mono
    (by simp [CellExpr.args])

/-- Find item: arguments 0=pair `(x, g)`, 1=unused data; the result is `g ≠ 0`. -/
def pivotTestBody (zeroTest : Fin p) : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    pair := .call zeroTest [.register 3] [4]
      (.branch (.register 4) (.ret [.flag false]) (.ret [.flag true])) }

def pivotBudget (N : ℕ) : ℕ := 60 * N + 100

theorem pivotTest_compiled (code : Code p) (ids : RegisterSupportArcs.Procedures p)
    (hcode : ids.Matches code) (self : Fin p) (hself : code self = pivotTestBody ids.zeroTest)
    {h : Heap} (hh : Valid h) {pp dp : Ptr} {pr : BinaryRational.Word N × BinaryRational.Word N}
    (hp : PairWAt h pp pr) :
    ∃ out, Extends h out ∧ Valid out ∧
      Within code h (initialRegisters [.pointer pp, .pointer dp]) (code self)
        [.flag (pivotPred pr)] out (pivotBudget N) := by
  obtain ⟨xp, gp, cell, -, hg⟩ := hp
  obtain ⟨out, e1, v1, tested⟩ := RegisterRationalZero.compiled code ids.read ids.zero
    ids.compare hcode.read hcode.zero hcode.compare hh hg
  refine ⟨out, e1, v1, ?_⟩
  let r0 := initialRegisters [Value.pointer pp, .pointer dp]
  let r1 := loadRegisters r0 2 3 15 (.pair xp gp)
  let z := (BinaryRational.isZero pr.2).1
  let r2 := bindResults r1 [4] [Value.flag z]
  have tail : Within code out r2 (.branch (.register 4) (.ret [.flag false]) (.ret [.flag true]))
      [.flag (pivotPred pr)] out (3 + 3) := by
    have h4 : (Atom.register 4).eval r2 = .flag z := by simp [r2, bindResults, Atom.eval]
    have hpp : pivotPred pr = !z := rfl
    rw [hpp]
    cases hz : z
    · refine Within.branch (b := false) (by rw [h4, hz]) ?_
      simpa [values, Atom.eval] using Within.ret code out r2 [.flag true]
    · refine Within.branch (b := true) (by rw [h4, hz]) ?_
      simpa [values, Atom.eval] using Within.ret code out r2 [.flag false]
  have zargs : values r1 [.register 3] = [.pointer gp] := by
    simp [r1, loadRegisters, decoded, values, Atom.eval]
  have zc := Within.call (procedure := ids.zeroTest) (regs := r1) (results := [4])
    (arguments := [.register 3]) (by simpa only [zargs, hcode.zeroTest] using tested) tail
  have loaded := Within.load (address := .register 0) (first := 2) (second := 3) (bit := 15)
    (branches := { CompiledTrie.failCases with
      pair := .call ids.zeroTest [.register 3] [4]
        (.branch (.register 4) (.ret [.flag false]) (.ret [.flag true])) })
    (by simp [Atom.eval, r0, initialRegisters]) cell zc
  rw [hself]
  exact loaded.mono (by simp [pivotBudget]; omega)

/-- Conversion of a stored integer row to a stored rational row (`intRowW`):
arguments 0=signed-word row, 1=denominator word `one`. -/
theorem intRow_compiled (code : Code p) (ratMap ratItem : Fin p)
    (hmap : code ratMap = RegisterListMap.body ratMap ratItem)
    (hitem : code ratItem = ratItemBody) {h : Heap} (hh : Valid h) {gp op : Ptr}
    {gs : List (RegisterPotentialStep.Word N)} {one : Bits N}
    (hg : SignedWords.ListAt h gp gs) (ho : BitsAt h op one) :
    ∃ out q, Extends h out ∧ Valid out ∧ RowAt out q (gs.map (ratW one)) ∧
      Within code h (initialRegisters [.pointer gp, .pointer op]) (code ratMap) [.pointer q] out
        (46 * gs.length + 13) := by
  obtain ⟨out, q, e, v, hq, w⟩ := RegisterListMap.compiled_const code ratMap ratItem hmap
    SignedAt (fun heap ptr (o : Bits N) => BitsAt heap ptr o)
    (fun heap ptr (x : BinaryRational.Word N) => At heap ptr x)
    (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext)
    (fun ext _ _ hx => hx.mono ext) (fun _ hx => hx.allocated) (fun o g => ratW o g) 11 hh hg ho
    (fun hv _ _ _ hx hd => ratItem_compiled code ratItem hitem hv hx hd)
  exact ⟨out, q, e, v, hq, w.mono (by omega)⟩

end WeightedMIS.RegisterGeneratorWords
