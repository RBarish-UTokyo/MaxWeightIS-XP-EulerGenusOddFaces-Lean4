module

public import WeightedMIS.EdgeCostWords
public import WeightedMIS.RegisterExpandedScalars

/-!
# Compiled integer edge costs from the stored residual table

Arguments: the stored edge records (`pair leftWord rightWord`), the residual
table and the large capacity word. The procedure first computes the zero word
`big - big` and then walks the edge records, carrying the reversed list of
earlier records (a list of shared record pointers). For each record it

1. scans the earlier records for one with the same endpoints
   (`RegisterAdjacencyScan`); if there is one, the cost word is the zero word;
2. otherwise builds the node words `10·a` and `11·b`, looks up the residual
   capacity of that arc (`RegisterArcLookup`) and subtracts it from `big`;
3. if the endpoints differ, adds the same term for the reversed orientation.

The output list is `EdgeCostWords.costWords table big (big - big) [] edges`.
-/

@[expose] public section

namespace WeightedMIS.RegisterEdgeCosts

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.ResidualWords
open WeightedMIS.NetworkWords WeightedMIS.RegisterAdjacencyScan WeightedMIS.EdgeCostWords
open WeightedMIS.RegisterNetworkWeights (allocate_fits bit_fits cons_fits null_lt)

structure Procedures (p : ℕ) where
  adj : RegisterAdjacencyScan.Procedures p
  lookup : Fin p
  complement : Fin p
  add : Fin p
  sub : Fin p
  term : Fin p
  item : Fin p
  loop : Fin p
  self : Fin p

variable {p : ℕ}

/-- Arguments: table, big, zero, words `x`, `y`. Result: `big - residual(10·x, 11·y)`. -/
def termBody (lookup sub : Fin p) : Command p :=
  .allocate 5 (.bit (.flag false) (.register 3))
    (.allocate 5 (.bit (.flag true) (.register 5))
      (.allocate 6 (.bit (.flag true) (.register 4))
        (.allocate 6 (.bit (.flag true) (.register 6))
          (.call lookup [.register 0, .register 5, .register 6, .register 2] [7]
            (.call sub [.register 1, .register 7] [8, 9] (.ret [.register 8]))))))

def pairBody (term add : Fin p) : Command p :=
  .call term [.register 2, .register 3, .register 4, .register 6, .register 5] [11]
    (.call add [.register 8, .register 11, .flag false] [12, 13] (.ret [.register 12]))

def freshBody (term cmp add : Fin p) : Command p :=
  .call term [.register 2, .register 3, .register 4, .register 5, .register 6] [8]
    (.call cmp [.register 5, .register 6] [9, 10]
      (.branch (.register 10) (.ret [.register 8]) (pairBody term add)))

/-- Arguments: edge record, earlier records, table, big, zero. Result: cost word. -/
def itemBody (adj term cmp add : Fin p) : Command p :=
  .load (.register 0) 5 6 15 { CompiledTrie.failCases with
    pair := .call adj [.register 1, .register 5, .register 6] [7]
      (.branch (.register 7) (.ret [.register 4]) (freshBody term cmp add)) }

/-- Arguments: edge records, earlier records, table, big, zero. Result: cost words. -/
def loopBody (item self : Fin p) : Command p :=
  .load (.register 0) 5 6 15 { CompiledTrie.failCases with
    nil := .allocate 7 .nil (.ret [.register 7])
    cons := .call item [.register 5, .register 1, .register 2, .register 3, .register 4] [7]
      (.allocate 8 (.cons (.register 5) (.register 1))
        (.call self [.register 6, .register 8, .register 2, .register 3, .register 4] [9]
          (.allocate 10 (.cons (.register 7) (.register 9)) (.ret [.register 10])))) }

/-- Arguments: edge records, table, big. Result: cost words. -/
def costsBody (sub loop : Fin p) : Command p :=
  .call sub [.register 2, .register 2] [3, 4]
    (.allocate 5 .nil
      (.call loop [.register 0, .register 5, .register 1, .register 2, .register 3] [6]
        (.ret [.register 6])))

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  d.adj.Matches code ∧
  code d.lookup = RegisterArcLookup.lookupBody d.lookup d.adj.cmp ∧
  code d.complement = RegisterComplement.complementBody d.complement ∧
  code d.add = RegisterAdder.adderBody d.add ∧
  code d.sub = RegisterSubtractor.subtractorBody d.complement d.add ∧
  code d.term = termBody d.lookup d.sub ∧
  code d.item = itemBody d.adj.self d.term d.adj.cmp d.add ∧
  code d.loop = loopBody d.item d.loop ∧
  code d.self = costsBody d.sub d.loop

theorem EdgeWordsAt.nil {W : ℕ} {h : Heap} {ptr : Ptr} (hc : h[ptr]? = some .nil) :
    EdgeWordsAt h ptr ([] : List (Bits W × Bits W)) := ⟨[], .nil hc, .nil⟩

theorem EdgeWordsAt.cons {W : ℕ} {h : Heap} {ptr head tail : Ptr} {e : Bits W × Bits W}
    {es : List (Bits W × Bits W)} (hc : h[ptr]? = some (.cons head tail))
    (hh : EdgeAt h head e) (ht : EdgeWordsAt h tail es) : EdgeWordsAt h ptr (e :: es) := by
  obtain ⟨ps, hp, hw⟩ := ht
  exact ⟨head :: ps, .cons hc hp, .cons hh hw⟩

/-! ## One term -/

def termBudget (W B len : ℕ) : ℕ := RegisterArcLookup.budget (W + 2) len + 137 * B + 120

theorem term_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {W B : ℕ} {h : Heap} (hh : Valid h) {tp bp zp xp yp : Ptr}
    {table : List (Arc (W + 2) B)} {big zero : Bits B} {x y : Bits W}
    (htab : TableAt h tp table) (hb : BitsAt h bp big) (hz : BitsAt h zp zero)
    (hx : BitsAt h xp x) (hy : BitsAt h yp y) :
    ∃ out r, Extends h out ∧ Valid out ∧ BitsAt out r (termWord table big zero x y) ∧
      Within code h (initialRegisters [.pointer tp, .pointer bp, .pointer zp, .pointer xp,
        .pointer yp]) (code d.term) [.pointer r] out (termBudget W B table.length) := by
  obtain ⟨⟨hcmp, -⟩, hlookup, hcomp, hadd, hsub, hterm, -⟩ := hm
  let H1 := h ++ [Cell.bit false xp]
  let H2 := H1 ++ [Cell.bit true h.length]
  let H3 := H2 ++ [Cell.bit true yp]
  let H4 := H3 ++ [Cell.bit true H2.length]
  obtain ⟨e1, v1, c1⟩ := allocate_fits hh (bit_fits (b := false) hx.allocated)
  obtain ⟨e2, v2, c2⟩ := allocate_fits v1 (bit_fits (b := true) (h := H1) (a := h.length)
    (by simp [H1]))
  obtain ⟨e3, v3, c3⟩ := allocate_fits v2 (bit_fits (b := true) (h := H2) (a := yp)
    (RegisterNetworkNodes.lt_of_ext (e1.trans e2) hy.allocated))
  obtain ⟨e4, v4, c4⟩ := allocate_fits v3 (bit_fits (b := true) (h := H3) (a := H2.length)
    (by simp [H3]))
  have e14 := e1.trans (e2.trans (e3.trans e4))
  have hL : BitsAt H4 H1.length (leftWord x) :=
    .cons ((e3.trans e4).lookup c2) (.cons ((e2.trans (e3.trans e4)).lookup c1) (hx.mono e14))
  have hR : BitsAt H4 H3.length (rightWord y) :=
    .cons c4 (.cons (e4.lookup c3) (hy.mono e14))
  obtain ⟨c, hc, lookRun⟩ := RegisterArcLookup.compiled code d.lookup d.adj.cmp hlookup hcmp
    (htab.mono e14) hL hR (hz.mono e14)
  obtain ⟨out, res, e5, v5, hres, subRun⟩ := RegisterSubtractor.compiled code d.complement d.add
    hcomp hadd v4 (hb.mono e14) hc
  refine ⟨out, res, e14.trans e5, v5, hres, ?_⟩
  let r0 := initialRegisters [Value.pointer tp, .pointer bp, .pointer zp, .pointer xp, .pointer yp]
  let r1 := Function.update r0 5 (.pointer h.length)
  let r2 := Function.update r1 5 (.pointer H1.length)
  let r3 := Function.update r2 6 (.pointer H2.length)
  let r4 := Function.update r3 6 (.pointer H3.length)
  let r5 := bindResults r4 [7] [.pointer c]
  let r6 := bindResults r5 [8, 9] [.pointer res,
    .flag (Bits.subtract big (RegisterArcLookup.lookup (leftWord x) (rightWord y) zero table)).2.1]
  have last : Within code out r6 (.ret [.register 8]) [.pointer res] out 3 :=
    RegisterNetworkTable.ret_reg code out (by simp [r6, bindResults])
  have aS : values r5 [.register 1, .register 7] = [.pointer bp, .pointer c] := by
    simp [values, Atom.eval, r5, r4, r3, r2, r1, r0, bindResults, initialRegisters]
  have cS := Within.call (procedure := d.sub) (regs := r5)
    (arguments := [.register 1, .register 7]) (results := [8, 9])
    (by rw [aS, hsub]; exact subRun) last
  have aL : values r4 [.register 0, .register 5, .register 6, .register 2] =
      [.pointer tp, .pointer H1.length, .pointer H3.length, .pointer zp] := by
    simp [values, Atom.eval, r4, r3, r2, r1, r0, initialRegisters]
  have cL := Within.call (procedure := d.lookup) (regs := r4)
    (arguments := [.register 0, .register 5, .register 6, .register 2]) (results := [7])
    (by simpa only [aL] using lookRun) cS
  have a4 := Within.allocate (regs := r3) (dst := 6) (h := H3)
    (expr := .bit (.flag true) (.register 6)) (c := .bit true H2.length)
    (by simp [CellExpr.eval, Atom.eval, r3, Value.asPointer, Value.asFlag]) cL
  have a3 := Within.allocate (regs := r2) (dst := 6) (h := H2)
    (expr := .bit (.flag true) (.register 4)) (c := .bit true yp)
    (by simp [CellExpr.eval, Atom.eval, r2, r1, r0, initialRegisters, Value.asPointer,
      Value.asFlag]) a4
  have a2 := Within.allocate (regs := r1) (dst := 5) (h := H1)
    (expr := .bit (.flag true) (.register 5)) (c := .bit true h.length)
    (by simp [CellExpr.eval, Atom.eval, r1, Value.asPointer, Value.asFlag]) a3
  have a1 := Within.allocate (regs := r0) (dst := 5) (h := h)
    (expr := .bit (.flag false) (.register 3)) (c := .bit false xp)
    (by simp [CellExpr.eval, Atom.eval, r0, initialRegisters, Value.asPointer, Value.asFlag]) a2
  rw [hterm]
  exact a1.mono (by simp [termBudget, CellExpr.args]; omega)

/-! ## One edge -/

def itemBudget (W B L len : ℕ) : ℕ :=
  RegisterAdjacencyScan.budget W L + 2 * termBudget W B len + 36 * W + 110 * B + 200

theorem adjBudget_mono (W a b : ℕ) (hab : a ≤ b) :
    RegisterAdjacencyScan.budget W a ≤ RegisterAdjacencyScan.budget W b := by
  unfold RegisterAdjacencyScan.budget
  have := Nat.mul_le_mul_left (RegisterAdjacencyScan.itemBudget W + 30) hab
  omega

theorem item_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {W B L : ℕ} {h : Heap} (hh : Valid h) {ep pp tp bp zp : Ptr}
    {table : List (Arc (W + 2) B)} {big zero : Bits B} {e : Bits W × Bits W}
    {pre : List (Bits W × Bits W)} (hL : pre.length ≤ L)
    (he : EdgeAt h ep e) (hpre : EdgeWordsAt h pp pre)
    (htab : TableAt h tp table) (hb : BitsAt h bp big) (hz : BitsAt h zp zero) :
    ∃ out r, Extends h out ∧ Valid out ∧ BitsAt out r (costWord table big zero pre e) ∧
      Within code h (initialRegisters [.pointer ep, .pointer pp, .pointer tp, .pointer bp,
        .pointer zp]) (code d.item) [.pointer r] out (itemBudget W B L table.length) := by
  have hm' := hm
  obtain ⟨hadjm, -, -, hadd, -, -, hitem, -⟩ := hm'
  obtain ⟨lp, rp, cell, hl, hr⟩ := he
  obtain ⟨H1, e1, v1, adjRun⟩ := RegisterAdjacencyScan.compiled code d.adj hadjm hh hpre hl hr
  let f := pre.any (edgeMatch e.1 e.2)
  let r0 := initialRegisters [Value.pointer ep, .pointer pp, .pointer tp, .pointer bp, .pointer zp]
  let r1 := loadRegisters r0 5 6 15 (.pair lp rp)
  let r2 := bindResults r1 [7] [.flag f]
  have g2 : r2 2 = .pointer tp := by
    simp [r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters]
  have g3 : r2 3 = .pointer bp := by
    simp [r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters]
  have g4 : r2 4 = .pointer zp := by
    simp [r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters]
  have g5 : r2 5 = .pointer lp := by simp [r2, r1, bindResults, loadRegisters, decoded]
  have g6 : r2 6 = .pointer rp := by simp [r2, r1, bindResults, loadRegisters, decoded]
  have g7 : r2 7 = .flag f := by simp [r2, bindResults]
  have tree : ∃ out r, Extends H1 out ∧ Valid out ∧ BitsAt out r (costWord table big zero pre e) ∧
      Within code H1 r2 (.branch (.register 7) (.ret [.register 4]) (freshBody d.term d.adj.cmp d.add))
        [.pointer r] out (2 * termBudget W B table.length + 36 * W + 110 * B + 120) := by
    by_cases hf : f = true
    · refine ⟨H1, zp, .refl _, v1, ?_, ?_⟩
      · have : costWord table big zero pre e = zero := by
          unfold costWord
          exact ite_eq_left hf
        rw [this]
        exact hz.mono e1
      · have run := RegisterNetworkTable.branch_reg (regs := r2) (r := 7) (b := true)
          (yes := .ret [.register 4]) (no := freshBody d.term d.adj.cmp d.add)
          (by rw [g7, hf]) (RegisterNetworkTable.ret_reg code H1 g4)
        exact run.mono (by omega)
    · have hf' : f = false := by simpa using hf
      obtain ⟨H2, t1, e2, v2, ht1, run1⟩ := term_compiled code d hm v1 (htab.mono e1)
        (hb.mono e1) (hz.mono e1) (hl.mono e1) (hr.mono e1)
      have cmpRun := cmp_run code d.adj.cmp hadjm.1 ((hl.mono e1).mono e2) ((hr.mono e1).mono e2)
      let r3 := bindResults r2 [8] [.pointer t1]
      let r4 := bindResults r3 [9, 10]
        [.flag (decide ((Bits.compare e.1 e.2).1 = .lt)), .flag (decide (e.1 = e.2))]
      have fresh : ∃ out r, Extends H2 out ∧ Valid out ∧
          BitsAt out r (costWord table big zero pre e) ∧
          Within code H2 r4 (.branch (.register 10) (.ret [.register 8])
            (pairBody d.term d.add)) [.pointer r] out
            (termBudget W B table.length + 110 * B + 60) := by
        by_cases hxy : e.1 = e.2
        · refine ⟨H2, t1, .refl _, v2, ?_, ?_⟩
          · have : costWord table big zero pre e = termWord table big zero e.1 e.2 := by
              unfold costWord
              rw [ite_eq_right (by simpa [f] using hf'), ite_eq_left hxy]
            rw [this]
            exact ht1
          · have g8 : r4 8 = .pointer t1 := by simp [r4, r3, bindResults]
            have run := RegisterNetworkTable.branch_reg (regs := r4) (r := 10) (b := true)
              (yes := .ret [.register 8]) (no := pairBody d.term d.add)
              (by simp [r4, bindResults, hxy]) (RegisterNetworkTable.ret_reg code H2 g8)
            exact run.mono (by omega)
        · obtain ⟨H3, t2, e3, v3, ht2, run2⟩ := term_compiled code d hm v2
            ((htab.mono e1).mono e2) ((hb.mono e1).mono e2) ((hz.mono e1).mono e2)
            ((hr.mono e1).mono e2) ((hl.mono e1).mono e2)
          obtain ⟨H4, res, e4, v4, hres, addRun⟩ :=
            RegisterExpandedParameters.addCarry_compiled code d.add hadd v3 (ht1.mono e3) ht2 false
          refine ⟨H4, res, e3.trans e4, v4, ?_, ?_⟩
          · have : costWord table big zero pre e = (Bits.addCarry (termWord table big zero e.1 e.2)
                (termWord table big zero e.2 e.1) false).1 := by
              unfold costWord
              rw [ite_eq_right (by simpa [f] using hf'), ite_eq_right hxy]
            rw [this]
            exact hres
          · let r5 := bindResults r4 [11] [.pointer t2]
            let r6 := bindResults r5 [12, 13] [.pointer res,
              .flag (Bits.addCarry (termWord table big zero e.1 e.2)
                (termWord table big zero e.2 e.1) false).2.1]
            have last : Within code H4 r6 (.ret [.register 12]) [.pointer res] H4 3 :=
              RegisterNetworkTable.ret_reg code H4 (by simp [r6, bindResults])
            have aA : values r5 [.register 8, .register 11, .flag false] =
                [.pointer t1, .pointer t2, .flag false] := by
              simp [values, Atom.eval, r5, r4, r3, bindResults]
            have cA := Within.call (procedure := d.add) (regs := r5)
              (arguments := [.register 8, .register 11, .flag false]) (results := [12, 13])
              (by simpa only [aA] using addRun) last
            have aT : values r4 [.register 2, .register 3, .register 4, .register 6, .register 5] =
                [.pointer tp, .pointer bp, .pointer zp, .pointer rp, .pointer lp] := by
              simp [values, Atom.eval, r4, r3, bindResults, g2, g3, g4, g5, g6]
            have cT := Within.call (procedure := d.term) (regs := r4)
              (arguments := [.register 2, .register 3, .register 4, .register 6, .register 5])
              (results := [11]) (by simpa only [aT] using run2) cA
            have run := RegisterNetworkTable.branch_reg (regs := r4) (r := 10) (b := false)
              (yes := .ret [.register 8]) (no := pairBody d.term d.add)
              (by simp [r4, bindResults, hxy]) cT
            exact run.mono (by unfold RegisterExpandedParameters.addBudget; simp; omega)
      obtain ⟨out, r, e5, v5, hres, freshRun⟩ := fresh
      refine ⟨out, r, e2.trans e5, v5, hres, ?_⟩
      have aC : values r3 [.register 5, .register 6] = [.pointer lp, .pointer rp] := by
        simp [values, Atom.eval, r3, bindResults, g5, g6]
      have cC := Within.call (procedure := d.adj.cmp) (regs := r3)
        (arguments := [.register 5, .register 6]) (results := [9, 10])
        (by simpa only [aC] using cmpRun) freshRun
      have aT : values r2 [.register 2, .register 3, .register 4, .register 5, .register 6] =
          [.pointer tp, .pointer bp, .pointer zp, .pointer lp, .pointer rp] := by
        simp [values, Atom.eval, g2, g3, g4, g5, g6]
      have cT := Within.call (procedure := d.term) (regs := r2)
        (arguments := [.register 2, .register 3, .register 4, .register 5, .register 6])
        (results := [8]) (by simpa only [aT] using run1) cC
      have run := RegisterNetworkTable.branch_reg (regs := r2) (r := 7) (b := false)
        (yes := .ret [.register 4]) (no := freshBody d.term d.adj.cmp d.add)
        (by rw [g7, hf']) cT
      exact run.mono (by simp; omega)
  obtain ⟨out, r, e2, v2, hres, treeRun⟩ := tree
  refine ⟨out, r, e1.trans e2, v2, hres, ?_⟩
  have aA : values r1 [.register 1, .register 5, .register 6] =
      [.pointer pp, .pointer lp, .pointer rp] := by
    simp [values, Atom.eval, r1, r0, loadRegisters, decoded, initialRegisters]
  have cA := Within.call (procedure := d.adj.self) (regs := r1)
    (arguments := [.register 1, .register 5, .register 6]) (results := [7])
    (by simpa only [aA] using adjRun) treeRun
  have l := Within.load (regs := r0) (address := .register 0) (first := 5) (second := 6)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .call d.adj.self [.register 1, .register 5, .register 6] [7]
        (.branch (.register 7) (.ret [.register 4]) (freshBody d.term d.adj.cmp d.add)) })
    (by simp [Atom.eval, r0, initialRegisters]) cell cA
  rw [hitem]
  have hab := adjBudget_mono W pre.length L hL
  exact l.mono (by simp [itemBudget]; omega)

/-! ## The edge walk -/

def loopBudget (W B L len k : ℕ) : ℕ := (itemBudget W B L len + 60) * k + 20

theorem loop_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {W B L : ℕ} {table : List (Arc (W + 2) B)} {big zero : Bits B}
    (es : List (Bits W × Bits W)) :
    ∀ {h : Heap}, Valid h → ∀ {ep pp tp bp zp : Ptr} {pre : List (Bits W × Bits W)},
      pre.length + es.length ≤ L →
      EdgeWordsAt h ep es → EdgeWordsAt h pp pre → TableAt h tp table →
      BitsAt h bp big → BitsAt h zp zero →
      ∃ out r, Extends h out ∧ Valid out ∧ WordsAt out r (costWords table big zero pre es) ∧
        Within code h (initialRegisters [.pointer ep, .pointer pp, .pointer tp, .pointer bp,
          .pointer zp]) (code d.loop) [.pointer r] out
          (loopBudget W B L table.length es.length) := by
  have hloop := hm.2.2.2.2.2.2.2.1
  induction es with
  | nil =>
    intro h hh ep pp tp bp zp pre _ hes _ _ _ _
    obtain ⟨ptrs, hlist, hrel⟩ := hes
    cases hrel
    cases hlist with
    | nil cell =>
      obtain ⟨e1, v1, c1⟩ := allocate_fits hh (c := .nil) (by intro q hq; simp [Cell.references] at hq)
      refine ⟨h ++ [.nil], h.length, e1, v1, WordsAt.nil c1, ?_⟩
      let r0 := initialRegisters [Value.pointer ep, .pointer pp, .pointer tp, .pointer bp,
        .pointer zp]
      let r1 := loadRegisters r0 5 6 15 .nil
      have last : Within code (h ++ [.nil]) (Function.update r1 7 (.pointer h.length))
          (.ret [.register 7]) [.pointer h.length] (h ++ [.nil]) 3 :=
        RegisterNetworkTable.ret_reg code _ (by simp)
      have a := Within.allocate (regs := r1) (dst := 7) (h := h) (expr := .nil) (c := .nil)
        (by simp [CellExpr.eval]) last
      have l := Within.load (regs := r0) (address := .register 0) (first := 5) (second := 6)
        (bit := 15) (branches := { CompiledTrie.failCases with
          nil := .allocate 7 .nil (.ret [.register 7])
          cons := .call d.item [.register 5, .register 1, .register 2, .register 3, .register 4]
            [7] (.allocate 8 (.cons (.register 5) (.register 1))
              (.call d.loop [.register 6, .register 8, .register 2, .register 3, .register 4] [9]
                (.allocate 10 (.cons (.register 7) (.register 9)) (.ret [.register 10])))) })
        (by simp [Atom.eval, r0, initialRegisters]) cell a
      rw [hloop]
      exact l.mono (by simp [loopBudget, CellExpr.args])
  | cons e es ih =>
    intro h hh ep pp tp bp zp pre hlen hes hpre htab hb hz
    obtain ⟨ptrs, hlist, hrel⟩ := hes
    cases hrel with
    | @cons head _ ps _ hhead hrest =>
    cases hlist with
    | @cons _ _ tail _ cell htail =>
    have hes' : EdgeWordsAt h tail es := ⟨ps, htail, hrest⟩
    obtain ⟨H1, c, e1, v1, hc, itemRun⟩ := item_compiled code d hm (L := L) hh
      (by simp at hlen; omega) hhead hpre htab hb hz
    obtain ⟨e2, v2, c2⟩ := allocate_fits v1 (cons_fits (RegisterNetworkNodes.lt_of_ext e1
      (by obtain ⟨_, _, c, -⟩ := hhead; exact (List.getElem?_eq_some_iff.mp c).1)) (RegisterNetworkNodes.lt_of_ext e1 hpre.allocated))
    let H2 := H1 ++ [Cell.cons head pp]
    have e12 := e1.trans e2
    have hpre' : EdgeWordsAt H2 H1.length (e :: pre) :=
      EdgeWordsAt.cons c2 (hhead.mono e12) (hpre.mono e12)
    obtain ⟨H3, rest, e3, v3, hrestw, restRun⟩ := ih v2 (by simp at hlen ⊢; omega)
      (hes'.mono e12) hpre' (htab.mono e12) (hb.mono e12) (hz.mono e12)
    obtain ⟨e4, v4, c4⟩ := allocate_fits v3 (cons_fits (RegisterNetworkNodes.lt_of_ext
      (e2.trans e3) hc.allocated) hrestw.allocated)
    let H4 := H3 ++ [Cell.cons c rest]
    refine ⟨H4, H3.length, e12.trans (e3.trans e4), v4,
      WordsAt.cons c4 ((hc.mono (e2.trans e3)).mono e4) (hrestw.mono e4), ?_⟩
    let r0 := initialRegisters [Value.pointer ep, .pointer pp, .pointer tp, .pointer bp,
      .pointer zp]
    let r1 := loadRegisters r0 5 6 15 (.cons head tail)
    let r2 := bindResults r1 [7] [.pointer c]
    let r3 := Function.update r2 8 (.pointer H1.length)
    let r4 := bindResults r3 [9] [.pointer rest]
    let r5 := Function.update r4 10 (.pointer H3.length)
    have last : Within code H4 r5 (.ret [.register 10]) [.pointer H3.length] H4 3 :=
      RegisterNetworkTable.ret_reg code H4 (by simp [r5])
    have a2 := Within.allocate (regs := r4) (dst := 10) (h := H3)
      (expr := .cons (.register 7) (.register 9)) (c := .cons c rest)
      (by simp [CellExpr.eval, Atom.eval, r4, r3, r2, bindResults, Value.asPointer]) last
    have aR : values r3 [.register 6, .register 8, .register 2, .register 3, .register 4] =
        [.pointer tail, .pointer H1.length, .pointer tp, .pointer bp, .pointer zp] := by
      simp [values, Atom.eval, r3, r2, r1, r0, bindResults, loadRegisters, decoded,
        initialRegisters]
    have cR := Within.call (procedure := d.loop) (regs := r3)
      (arguments := [.register 6, .register 8, .register 2, .register 3, .register 4])
      (results := [9]) (by simpa only [aR] using restRun) a2
    have a1 := Within.allocate (regs := r2) (dst := 8) (h := H1)
      (expr := .cons (.register 5) (.register 1)) (c := .cons head pp)
      (by simp [CellExpr.eval, Atom.eval, r2, r1, r0, bindResults, loadRegisters, decoded,
        initialRegisters, Value.asPointer]) cR
    have aI : values r1 [.register 5, .register 1, .register 2, .register 3, .register 4] =
        [.pointer head, .pointer pp, .pointer tp, .pointer bp, .pointer zp] := by
      simp [values, Atom.eval, r1, r0, loadRegisters, decoded, initialRegisters]
    have cI := Within.call (procedure := d.item) (regs := r1)
      (arguments := [.register 5, .register 1, .register 2, .register 3, .register 4])
      (results := [7]) (by simpa only [aI] using itemRun) a1
    have l := Within.load (regs := r0) (address := .register 0) (first := 5) (second := 6)
      (bit := 15) (branches := { CompiledTrie.failCases with
        nil := .allocate 7 .nil (.ret [.register 7])
        cons := .call d.item [.register 5, .register 1, .register 2, .register 3, .register 4]
          [7] (.allocate 8 (.cons (.register 5) (.register 1))
            (.call d.loop [.register 6, .register 8, .register 2, .register 3, .register 4] [9]
              (.allocate 10 (.cons (.register 7) (.register 9)) (.ret [.register 10])))) })
      (by simp [Atom.eval, r0, initialRegisters]) cell cI
    rw [hloop]
    exact l.mono (by simp [loopBudget, CellExpr.args, Nat.mul_add]; omega)

/-! ## The procedure -/

def budget (W B m len : ℕ) : ℕ := 137 * B + 100 + loopBudget W B m len m

theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {W B : ℕ} {h : Heap} (hh : Valid h) {ep tp bp : Ptr}
    {es : List (Bits W × Bits W)} {table : List (Arc (W + 2) B)} {big : Bits B}
    (hes : EdgeWordsAt h ep es) (htab : TableAt h tp table) (hb : BitsAt h bp big) :
    ∃ out r, Extends h out ∧ Valid out ∧
      WordsAt out r (costWords table big (Bits.subtract big big).1 [] es) ∧
      Within code h (initialRegisters [.pointer ep, .pointer tp, .pointer bp]) (code d.self)
        [.pointer r] out (budget W B es.length table.length) := by
  have hm' := hm
  obtain ⟨-, -, hcomp, hadd, hsub, -, -, -, hself⟩ := hm'
  obtain ⟨H1, zp, e1, v1, hz, subRun⟩ := RegisterSubtractor.compiled code d.complement d.add
    hcomp hadd hh hb hb
  obtain ⟨e2, v2, c2⟩ := allocate_fits v1 (c := .nil)
    (by intro q hq; simp [Cell.references] at hq)
  let H2 := H1 ++ [Cell.nil]
  have e12 := e1.trans e2
  obtain ⟨out, r, e3, v3, hr, loopRun⟩ := loop_compiled code d hm (L := es.length) es v2
    (pre := []) (by simp) (hes.mono e12) (EdgeWordsAt.nil c2) (htab.mono e12) (hb.mono e12)
    (hz.mono e2)
  refine ⟨out, r, e12.trans e3, v3, hr, ?_⟩
  let r0 := initialRegisters [Value.pointer ep, .pointer tp, .pointer bp]
  let r1 := bindResults r0 [3, 4] [.pointer zp, .flag (Bits.subtract big big).2.1]
  let r2 := Function.update r1 5 (.pointer H1.length)
  let r3 := bindResults r2 [6] [.pointer r]
  have last : Within code out r3 (.ret [.register 6]) [.pointer r] out 3 :=
    RegisterNetworkTable.ret_reg code out (by simp [r3, bindResults])
  have aL : values r2 [.register 0, .register 5, .register 1, .register 2, .register 3] =
      [.pointer ep, .pointer H1.length, .pointer tp, .pointer bp, .pointer zp] := by
    simp [values, Atom.eval, r2, r1, r0, bindResults, initialRegisters]
  have cL := Within.call (procedure := d.loop) (regs := r2)
    (arguments := [.register 0, .register 5, .register 1, .register 2, .register 3])
    (results := [6]) (by simpa only [aL] using loopRun) last
  have a := Within.allocate (regs := r1) (dst := 5) (h := H1) (expr := .nil) (c := .nil)
    (by simp [CellExpr.eval]) cL
  have aS : values r0 [.register 2, .register 2] = [.pointer bp, .pointer bp] := by
    simp [values, Atom.eval, r0, initialRegisters]
  have cS := Within.call (procedure := d.sub) (regs := r0)
    (arguments := [.register 2, .register 2]) (results := [3, 4])
    (by rw [aS, hsub]; exact subRun) a
  rw [hself]
  exact cS.mono (by simp [budget, CellExpr.args]; omega)

end WeightedMIS.RegisterEdgeCosts
