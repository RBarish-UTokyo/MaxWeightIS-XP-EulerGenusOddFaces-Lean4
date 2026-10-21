module

public import WeightedMIS.NetworkWeights
public import WeightedMIS.RegisterRationalRow
public import WeightedMIS.RegisterListFold
public import WeightedMIS.RegisterListMap
public import WeightedMIS.RegisterRemainder
public import WeightedMIS.RegisterWordArithmetic

/-!
# Register code for the integral network weights

The input is the stored row of canonical rational weight words of width `w`
(`RegisterRationalRow.RowAt`), with at least one vertex. The procedure

1. builds the zero padding word `Bits.pad den₀ (n + 1)` from a list of length
   `n + 1` (one fresh cell in front of the row) and the first denominator word,
2. widens the first denominator to obtain a shape word of the common width
   `NetworkWeights.width w n`, and builds the zero and unit words of that width,
3. folds the truncated denominators into their product `D` by multiplication,
4. maps every weight word to its scaled weight `truncMag * (D / truncDen)`,
5. folds the scaled weights into `1 + Σ μ` by addition.

It returns the scaled weight words, the large capacity word and the zero word,
all equal to the canonical encodings of `NetworkWeights.mu`, `NetworkWeights.big`
and `0`.
-/

@[expose] public section

namespace WeightedMIS.RegisterNetworkWeights

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords
open WeightedMIS.NetworkWeights

/-! ## Heap helpers -/

/-- One allocation of a cell whose references are allocated. -/
theorem allocate_fits {h : Heap} (hh : Valid h) {c : Cell} (hc : c.Fits h.length) :
    Extends h (h ++ [c]) ∧ Valid (h ++ [c]) ∧ (h ++ [c])[h.length]? = some c := by
  have hs := safe_allocate h hh c hc
  exact ⟨by simpa [Program.allocate] using hs.1, by simpa [Program.allocate] using hs.2.1,
    by simp⟩

theorem pair_fits {h : Heap} {a b : Ptr} (ha : a < h.length) (hb : b < h.length) :
    (Cell.pair a b).Fits h.length := by
  intro q hq
  simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ha
  · exact hb

theorem cons_fits {h : Heap} {a b : Ptr} (ha : a < h.length) (hb : b < h.length) :
    (Cell.cons a b).Fits h.length := by
  intro q hq
  simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ha
  · exact hb

theorem bit_fits {h : Heap} {b : Bool} {a : Ptr} (ha : a < h.length) :
    (Cell.bit b a).Fits h.length := by
  intro q hq
  simp only [Cell.references, List.mem_singleton] at hq
  exact hq ▸ ha

theorem null_lt {h : Heap} (hh : Valid h) : 0 < h.length :=
  (List.getElem?_eq_some_iff.mp hh.1).1

/-! ## Procedures -/

structure Procedures (p : ℕ) where
  div : RegisterDivision.Procedures p
  mulAcc : Fin p
  multiply : Fin p
  widen : Fin p
  pad : Fin p
  denItem : Fin p
  denFold : Fin p
  muItem : Fin p
  muMap : Fin p
  sumItem : Fin p
  sumFold : Fin p
  self : Fin p

variable {p : ℕ}

/-- Arguments: weight record, padding word, product so far. -/
def denItemBody (widen multiply : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    pair := .load (.register 3) 5 15 6 { CompiledTrie.failCases with
      bit := .branch (.register 6) (.ret [.register 2])
        (.call widen [.register 1, .register 4] [7]
          (.call multiply [.register 2, .register 7] [8] (.ret [.register 8]))) } }

/-- Arguments: weight record, data `((pad, D), zero)`. -/
def muItemBody (widen divide multiply : Fin p) : Command p :=
  .load (.register 1) 2 3 15 { CompiledTrie.failCases with
    pair := .load (.register 2) 4 5 15 { CompiledTrie.failCases with
      pair := .load (.register 0) 6 7 15 { CompiledTrie.failCases with
        pair := .load (.register 6) 8 15 9 { CompiledTrie.failCases with
          bit := .branch (.register 9) (.ret [.register 3])
            (.call widen [.register 4, .register 7] [10]
              (.call divide [.register 5, .register 10] [11, 12]
                (.call widen [.register 4, .register 8] [13]
                  (.call multiply [.register 13, .register 11] [14]
                    (.ret [.register 14]))))) } } } }

/-- Arguments: scaled weight word, unused data, sum so far. -/
def sumItemBody (add : Fin p) : Command p :=
  .call add [.register 2, .register 0, .flag false] [3, 4] (.ret [.register 3])

/-- Argument: the weight row. Results: scaled weights, `1 + Σ μ`, zero word. -/
def weightsBody (pad widen zero add denFold muMap sumFold : Fin p) : Command p :=
  .load (.register 0) 1 2 15 { CompiledTrie.failCases with
    cons := .load (.register 1) 3 4 15 { CompiledTrie.failCases with
      pair := .allocate 5 (.cons .null (.register 0))
        (.call pad [.register 5, .register 4] [6]
          (.call widen [.register 6, .register 4] [7]
            (.call zero [.register 7] [8]
              (.call add [.register 8, .register 8, .flag true] [9, 10]
                (.call denFold [.register 0, .register 6, .register 9] [11]
                  (.allocate 12 (.pair (.register 6) (.register 11))
                    (.allocate 13 (.pair (.register 12) (.register 8))
                      (.call muMap [.register 0, .register 13] [14]
                        (.call sumFold [.register 14, .null, .register 9] [15]
                          (.ret [.register 14, .register 15, .register 8])))))))))) } }

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  d.div.Matches code ∧
  code d.mulAcc = RegisterMultiplier.multiplyAccBody d.mulAcc d.div.shift d.div.add ∧
  code d.multiply = RegisterMultiplier.multiplyBody d.div.zero d.mulAcc ∧
  code d.widen = RegisterWiden.widenBody d.widen ∧
  code d.pad = RegisterWiden.padBody d.pad d.widen ∧
  code d.denItem = denItemBody d.widen d.multiply ∧
  code d.denFold = RegisterListFold.body d.denFold d.denItem ∧
  code d.muItem = muItemBody d.widen d.div.divide d.multiply ∧
  code d.muMap = RegisterListMap.body d.muMap d.muItem ∧
  code d.sumItem = sumItemBody d.div.add ∧
  code d.sumFold = RegisterListFold.body d.sumFold d.sumItem ∧
  code d.self = weightsBody d.pad d.widen d.div.zero d.div.add d.denFold d.muMap d.sumFold

/-! ## Arithmetic calls -/

def multiplyBudget (B : ℕ) : ℕ := (136 * B + 80) * B + 24 * B + 39

theorem multiply_run (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {B : ℕ} {h : Heap} (hh : Valid h) {ap bp : Ptr} {a b : Bits B}
    (ha : BitsAt h ap a) (hb : BitsAt h bp b) :
    ∃ out r, Extends h out ∧ Valid out ∧ BitsAt out r (Bits.multiply a b).1 ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp]) (code d.multiply)
        [.pointer r] out (multiplyBudget B) := by
  obtain ⟨⟨hz, hc, hx, hs, hsn, hsu, hco, had, hdv⟩, hmul, hmult, -⟩ := hm
  obtain ⟨out, r, he, hv, hr, run⟩ := RegisterMultiplier.multiply_compiled code d.div.zero
    d.mulAcc d.div.shift d.div.snoc d.div.add hz hmul hs hsn had hh ha hb
  exact ⟨out, r, he, hv, hr, by rw [hmult]; exact run⟩

theorem divide_run (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {B : ℕ} {h : Heap} (hh : Valid h) {ap bp : Ptr} {a b : Bits B}
    (ha : BitsAt h ap a) (hb : BitsAt h bp b) :
    ∃ out qp rp, Extends h out ∧ Valid out ∧ BitsAt out qp (Bits.divide a b).1 ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp]) (code d.div.divide)
        [.pointer qp, .pointer rp] out (400 * (B + 1) ^ 2) := by
  obtain ⟨⟨hz, hc, hx, hs, hsn, hsu, hco, had, hdv⟩, -⟩ := hm
  obtain ⟨out, qp, rp, he, hv, hq, -, run⟩ := RegisterDivision.divide_compiled code d.div.zero
    d.div.cmp d.div.aux d.div.shift d.div.snoc d.div.sub d.div.complement d.div.add
    hz hc hx hs hsn hsu hco had hh ha hb
  exact ⟨out, qp, rp, he, hv, hq, by rw [hdv]; exact run⟩

/-- Addition with an arbitrary incoming carry. -/
theorem addCarry_run (code : Code p) (add : Fin p) (body : code add = RegisterAdder.adderBody add)
    {B : ℕ} {h : Heap} (hh : Valid h) {ap bp : Ptr} {a b : Bits B} (carry : Bool)
    (ha : BitsAt h ap a) (hb : BitsAt h bp b) :
    ∃ out r, Extends h out ∧ Valid out ∧ BitsAt out r (Bits.addCarry a b carry).1 ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp, .flag carry]) (code add)
        [.pointer r, .flag (Bits.addCarry a b carry).2.1] out (110 * B + 30) := by
  let output := addCarryPointer B ap bp carry h
  have safe := addCarryPointer_refines hh ha hb carry
  have eval := addCarryPointer_eval hh ha hb carry
  have run := RegisterAdder.compiled code add body eval
  change Within code h (initialRegisters [.pointer ap, .pointer bp, .flag carry]) (code add)
    [.pointer output.value.1, .flag output.value.2] output.heap (10 * output.trace.length) at run
  have len : output.trace.length = 11 * B + 3 := safe.2.2.2
  have bit : output.value.2 = (Bits.addCarry a b carry).2.1 := safe.2.2.1
  rw [len, bit] at run
  exact ⟨output.heap, output.value.1, safe.1.1, safe.1.2.1, safe.2.1, run.mono (by omega)⟩

/-! ## Fold and map items -/

def denItemBudget (j B : ℕ) : ℕ := 26 * j + multiplyBudget B + 49

theorem denItem_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {w j : ℕ} {h : Heap} (hh : Valid h) {qp pp ap : Ptr} {q : BinaryRational.Word w}
    {P : Bits j} {acc : Bits (w + j)}
    (hq : StoredRational.At h qp q) (hp : BitsAt h pp P) (ha : BitsAt h ap acc) :
    ∃ out r, Extends h out ∧ Valid out ∧ BitsAt out r (denStep P acc q) ∧
      Within code h (initialRegisters [.pointer qp, .pointer pp, .pointer ap])
        (code d.denItem) [.pointer r] out (denItemBudget j (w + j)) := by
  have hbody := hm.2.2.2.2.2.1
  obtain ⟨sp, np, dp, hpair, hbit, hnum, hden⟩ := hq
  let regs := initialRegisters [Value.pointer qp, .pointer pp, .pointer ap]
  let r1 := loadRegisters regs 3 4 15 (.pair sp dp)
  let r2 := loadRegisters r1 5 15 6 (.bit q.negative np)
  have tail : ∃ out r, Extends h out ∧ Valid out ∧ BitsAt out r (denStep P acc q) ∧
      Within code h r2 (.branch (.register 6) (.ret [.register 2])
        (.call d.widen [.register 1, .register 4] [7]
          (.call d.multiply [.register 2, .register 7] [8] (.ret [.register 8]))))
        [.pointer r] out (26 * j + multiplyBudget (w + j) + 29) := by
    cases hneg : q.negative
    · obtain ⟨h1, wp, e1, v1, hw, wrun⟩ := RegisterWiden.widen_compiled code d.widen
        hm.2.2.2.1 hh hp hden
      obtain ⟨h2, mp, e2, v2, hmr, mrun⟩ := multiply_run code d hm v1 (ha.mono e1) hw
      refine ⟨h2, mp, e1.trans e2, v2, by simpa [denStep, hneg] using hmr, ?_⟩
      let r3 := bindResults r2 [7] [.pointer wp]
      let r4 := bindResults r3 [8] [.pointer mp]
      have last : Within code h2 r4 (.ret [.register 8]) [.pointer mp] h2 3 := by
        simpa [values, Atom.eval, r4, bindResults] using Within.ret code h2 r4 [.register 8]
      have margs : values r3 [.register 2, .register 7] = [.pointer ap, .pointer wp] := by
        simp [values, Atom.eval, r3, r2, r1, regs, bindResults, loadRegisters, decoded,
          initialRegisters]
      have mcall := Within.call (procedure := d.multiply) (regs := r3)
        (arguments := [.register 2, .register 7]) (results := [8])
        (by simpa only [margs] using mrun) last
      have wargs : values r2 [.register 1, .register 4] = [.pointer pp, .pointer dp] := by
        simp [values, Atom.eval, r2, r1, regs, loadRegisters, decoded, initialRegisters]
      have wcall := Within.call (procedure := d.widen) (regs := r2)
        (arguments := [.register 1, .register 4]) (results := [7])
        (by simpa only [wargs] using wrun) mcall
      have br := Within.branch (regs := r2) (test := .register 6) (b := false)
        (yes := .ret [.register 2])
        (by simp [Atom.eval, r2, loadRegisters, decoded, hneg]) wcall
      exact br.mono (by simp [RegisterWiden.widenBudget]; omega)
    · refine ⟨h, ap, .refl h, hh, by simpa [denStep, hneg] using ha, ?_⟩
      have last : Within code h r2 (.ret [.register 2]) [.pointer ap] h 3 := by
        simpa [values, Atom.eval, r2, r1, regs, loadRegisters, decoded, initialRegisters] using
          Within.ret code h r2 [.register 2]
      have br := Within.branch (regs := r2) (test := .register 6) (b := true)
        (no := .call d.widen [.register 1, .register 4] [7]
          (.call d.multiply [.register 2, .register 7] [8] (.ret [.register 8])))
        (by simp [Atom.eval, r2, loadRegisters, decoded, hneg]) last
      exact br.mono (by omega)
  obtain ⟨out, r, he, hv, hr, run⟩ := tail
  refine ⟨out, r, he, hv, hr, ?_⟩
  have l2 := Within.load (regs := r1) (address := .register 3) (first := 5) (second := 15)
    (bit := 6) (branches := { CompiledTrie.failCases with
      bit := .branch (.register 6) (.ret [.register 2])
        (.call d.widen [.register 1, .register 4] [7]
          (.call d.multiply [.register 2, .register 7] [8] (.ret [.register 8]))) })
    (by simp [Atom.eval, r1, loadRegisters, decoded]) hbit run
  have l1 := Within.load (regs := regs) (address := .register 0) (first := 3) (second := 4)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 3) 5 15 6 { CompiledTrie.failCases with
        bit := .branch (.register 6) (.ret [.register 2])
          (.call d.widen [.register 1, .register 4] [7]
            (.call d.multiply [.register 2, .register 7] [8] (.ret [.register 8]))) } })
    (by simp [Atom.eval, regs, initialRegisters]) hpair l2
  rw [hbody]
  exact l1.mono (by simp [denItemBudget]; omega)

/-- The data of the scaled-weight map: `((pad, D), zero)`. -/
def MuDataAt {j B : ℕ} (h : Heap) (dp : Ptr) (x : Bits j × Bits B × Bits B) : Prop :=
  ∃ pd zp pp Dp, h[dp]? = some (.pair pd zp) ∧ h[pd]? = some (.pair pp Dp) ∧
    BitsAt h pp x.1 ∧ BitsAt h Dp x.2.1 ∧ BitsAt h zp x.2.2

theorem MuDataAt.mono {j B : ℕ} {h h' : Heap} (he : Extends h h') {dp : Ptr}
    {x : Bits j × Bits B × Bits B} (hd : MuDataAt h dp x) : MuDataAt h' dp x := by
  obtain ⟨pd, zp, pp, Dp, c1, c2, h1, h2, h3⟩ := hd
  exact ⟨pd, zp, pp, Dp, he.lookup c1, he.lookup c2, h1.mono he, h2.mono he, h3.mono he⟩

def muItemBudget (j B : ℕ) : ℕ := 52 * j + 400 * (B + 1) ^ 2 + multiplyBudget B + 92

theorem muItem_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {w j : ℕ} {h : Heap} (hh : Valid h) {qp dp : Ptr} {q : BinaryRational.Word w}
    {x : Bits j × Bits (w + j) × Bits (w + j)}
    (hq : StoredRational.At h qp q) (hd : MuDataAt h dp x) :
    ∃ out r, Extends h out ∧ Valid out ∧ BitsAt out r (muWord x.1 x.2.1 x.2.2 q) ∧
      Within code h (initialRegisters [.pointer qp, .pointer dp])
        (code d.muItem) [.pointer r] out (muItemBudget j (w + j)) := by
  have hbody := hm.2.2.2.2.2.2.2.1
  obtain ⟨sp, np, denp, hpair, hbit, hnum, hden⟩ := hq
  obtain ⟨pd, zp, pp, Dp, c1, c2, hP, hD, hZ⟩ := hd
  let regs := initialRegisters [Value.pointer qp, .pointer dp]
  let r1 := loadRegisters regs 2 3 15 (.pair pd zp)
  let r2 := loadRegisters r1 4 5 15 (.pair pp Dp)
  let r3 := loadRegisters r2 6 7 15 (.pair sp denp)
  let r4 := loadRegisters r3 8 15 9 (.bit q.negative np)
  let rest : Command p := .call d.widen [.register 4, .register 7] [10]
    (.call d.div.divide [.register 5, .register 10] [11, 12]
      (.call d.widen [.register 4, .register 8] [13]
        (.call d.multiply [.register 13, .register 11] [14] (.ret [.register 14]))))
  have tail : ∃ out r, Extends h out ∧ Valid out ∧ BitsAt out r (muWord x.1 x.2.1 x.2.2 q) ∧
      Within code h r4 (.branch (.register 9) (.ret [.register 3]) rest)
        [.pointer r] out (52 * j + 400 * (w + j + 1) ^ 2 + multiplyBudget (w + j) + 52) := by
    cases hneg : q.negative
    · obtain ⟨h1, ap1, e1, v1, hw1, run1⟩ := RegisterWiden.widen_compiled code d.widen
        hm.2.2.2.1 hh hP hden
      obtain ⟨h2, qp2, rp2, e2, v2, hq2, run2⟩ := divide_run code d hm v1 (hD.mono e1) hw1
      obtain ⟨h3, ap3, e3, v3, hw3, run3⟩ := RegisterWiden.widen_compiled code d.widen
        hm.2.2.2.1 v2 (hP.mono (e1.trans e2)) (hnum.mono (e1.trans e2))
      obtain ⟨h4, mp, e4, v4, hm4, run4⟩ := multiply_run code d hm v3 hw3 (hq2.mono e3)
      refine ⟨h4, mp, e1.trans (e2.trans (e3.trans e4)), v4,
        by simpa [muWord, hneg] using hm4, ?_⟩
      let s1 := bindResults r4 [10] [.pointer ap1]
      let s2 := bindResults s1 [11, 12] [.pointer qp2, .pointer rp2]
      let s3 := bindResults s2 [13] [.pointer ap3]
      let s4 := bindResults s3 [14] [.pointer mp]
      have last : Within code h4 s4 (.ret [.register 14]) [.pointer mp] h4 3 := by
        simpa [values, Atom.eval, s4, bindResults] using Within.ret code h4 s4 [.register 14]
      have a4 : values s3 [.register 13, .register 11] = [.pointer ap3, .pointer qp2] := by
        simp [values, Atom.eval, s3, s2, bindResults]
      have c4 := Within.call (procedure := d.multiply) (regs := s3)
        (arguments := [.register 13, .register 11]) (results := [14])
        (by simpa only [a4] using run4) last
      have a3 : values s2 [.register 4, .register 8] = [.pointer pp, .pointer np] := by
        simp [values, Atom.eval, s2, s1, r4, r3, r2, r1, regs, bindResults, loadRegisters,
          decoded]
      have c3 := Within.call (procedure := d.widen) (regs := s2)
        (arguments := [.register 4, .register 8]) (results := [13])
        (by simpa only [a3] using run3) c4
      have a2 : values s1 [.register 5, .register 10] = [.pointer Dp, .pointer ap1] := by
        simp [values, Atom.eval, s1, r4, r3, r2, r1, regs, bindResults, loadRegisters,
          decoded]
      have c2 := Within.call (procedure := d.div.divide) (regs := s1)
        (arguments := [.register 5, .register 10]) (results := [11, 12])
        (by simpa only [a2] using run2) c3
      have a1 : values r4 [.register 4, .register 7] = [.pointer pp, .pointer denp] := by
        simp [values, Atom.eval, r4, r3, r2, r1, regs, loadRegisters, decoded]
      have c1 := Within.call (procedure := d.widen) (regs := r4)
        (arguments := [.register 4, .register 7]) (results := [10])
        (by simpa only [a1] using run1) c2
      have br := Within.branch (regs := r4) (test := .register 9) (b := false)
        (yes := .ret [.register 3])
        (by simp [Atom.eval, r4, loadRegisters, decoded, hneg]) c1
      exact br.mono (by simp [RegisterWiden.widenBudget]; omega)
    · refine ⟨h, zp, .refl h, hh, by simpa [muWord, hneg] using hZ, ?_⟩
      have last : Within code h r4 (.ret [.register 3]) [.pointer zp] h 3 := by
        simpa [values, Atom.eval, r4, r3, r2, r1, regs, loadRegisters, decoded,
          initialRegisters] using Within.ret code h r4 [.register 3]
      have br := Within.branch (regs := r4) (test := .register 9) (b := true) (no := rest)
        (by simp [Atom.eval, r4, loadRegisters, decoded, hneg]) last
      exact br.mono (by omega)
  obtain ⟨out, r, he, hv, hr, run⟩ := tail
  refine ⟨out, r, he, hv, hr, ?_⟩
  have l4 := Within.load (regs := r3) (address := .register 6) (first := 8) (second := 15)
    (bit := 9) (branches := { CompiledTrie.failCases with
      bit := .branch (.register 9) (.ret [.register 3]) rest })
    (by simp [Atom.eval, r3, r2, r1, loadRegisters, decoded]) hbit run
  have l3 := Within.load (regs := r2) (address := .register 0) (first := 6) (second := 7)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 6) 8 15 9 { CompiledTrie.failCases with
        bit := .branch (.register 9) (.ret [.register 3]) rest } })
    (by simp [Atom.eval, r2, r1, regs, loadRegisters, decoded, initialRegisters]) hpair l4
  have l2 := Within.load (regs := r1) (address := .register 2) (first := 4) (second := 5)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 0) 6 7 15 { CompiledTrie.failCases with
        pair := .load (.register 6) 8 15 9 { CompiledTrie.failCases with
          bit := .branch (.register 9) (.ret [.register 3]) rest } } })
    (by simp [Atom.eval, r1, loadRegisters, decoded]) c2 l3
  have l1 := Within.load (regs := regs) (address := .register 1) (first := 2) (second := 3)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 2) 4 5 15 { CompiledTrie.failCases with
        pair := .load (.register 0) 6 7 15 { CompiledTrie.failCases with
          pair := .load (.register 6) 8 15 9 { CompiledTrie.failCases with
            bit := .branch (.register 9) (.ret [.register 3]) rest } } } })
    (by simp [Atom.eval, regs, initialRegisters]) c1 l2
  rw [hbody]
  exact l1.mono (by simp [muItemBudget]; omega)

def sumItemBudget (B : ℕ) : ℕ := 110 * B + 40

theorem sumItem_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {B : ℕ} {h : Heap} (hh : Valid h) {mp dp ap : Ptr} {m acc : Bits B}
    (hmw : BitsAt h mp m) (ha : BitsAt h ap acc) :
    ∃ out r, Extends h out ∧ Valid out ∧ BitsAt out r (sumStep acc m) ∧
      Within code h (initialRegisters [.pointer mp, .pointer dp, .pointer ap])
        (code d.sumItem) [.pointer r] out (sumItemBudget B) := by
  have hbody := hm.2.2.2.2.2.2.2.2.2.1
  have hadd := hm.1.2.2.2.2.2.2.2.1
  obtain ⟨out, r, he, hv, hr, run⟩ := addCarry_run code d.div.add hadd hh false ha hmw
  refine ⟨out, r, he, hv, hr, ?_⟩
  let regs := initialRegisters [Value.pointer mp, .pointer dp, .pointer ap]
  let r1 := bindResults regs [3, 4] [.pointer r, .flag (Bits.addCarry acc m false).2.1]
  have last : Within code out r1 (.ret [.register 3]) [.pointer r] out 3 := by
    simpa [values, Atom.eval, r1, bindResults] using Within.ret code out r1 [.register 3]
  have args : values regs [.register 2, .register 0, .flag false] =
      [.pointer ap, .pointer mp, .flag false] := by
    simp [values, Atom.eval, regs, initialRegisters]
  have c := Within.call (procedure := d.div.add) (regs := regs)
    (arguments := [.register 2, .register 0, .flag false]) (results := [3, 4])
    (by simpa only [args] using run) last
  rw [hbody]
  exact c.mono (by simp [sumItemBudget]; omega)

/-! ## The weights procedure -/

def budget (w n : ℕ) : ℕ :=
  let j := (w + 1) * (n + 1)
  let B := w + j
  80 + RegisterWiden.padBudget w (n + 1) + RegisterWiden.widenBudget j + 24 * B + 110 * B +
    (denItemBudget j B + 30) * n + (muItemBudget j B + 35) * n + (sumItemBudget B + 30) * n + 100

theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {w n : ℕ} (q : Fin n → BinaryRational.Word w) (hq : ∀ v, BinaryRational.Canonical (q v))
    (hn : 0 < n) {h : Heap} (hh : Valid h) {wp : Ptr}
    (hw : RegisterRationalRow.RowAt h wp ((List.finRange n).map q)) :
    ∃ out musp bigp zerop, Extends h out ∧ Valid out ∧
      WordsAt out musp (muWords q) ∧
      BitsAt out bigp (GraphReachEncoded.word (width w n) (big q)) ∧
      BitsAt out zerop (GraphReachEncoded.word (width w n) 0) ∧
      Within code h (initialRegisters [.pointer wp]) (code d.self)
        [.pointer musp, .pointer bigp, .pointer zerop] out (budget w n) := by
  have hwiden := hm.2.2.2.1
  have hpad := hm.2.2.2.2.1
  have hdenFold := hm.2.2.2.2.2.2.1
  have hmuMap := hm.2.2.2.2.2.2.2.2.1
  have hsumFold := hm.2.2.2.2.2.2.2.2.2.2.1
  have hself := hm.2.2.2.2.2.2.2.2.2.2.2
  have hzero := hm.1.1
  have hadd := hm.1.2.2.2.2.2.2.2.1
  -- the first weight record
  obtain ⟨ptrs, hl, hr⟩ := id hw
  have hlen : ptrs.length = n := by simpa using hr.length_eq
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hwpos : 0 < w := width_pos_of_canonical (q 0) (hq 0)
  rw [List.finRange_succ, List.map_cons] at hr
  obtain ⟨rec0, tail, cell0, hrec0⟩ : ∃ rec0 tail, h[wp]? = some (.cons rec0 tail) ∧
      StoredRational.At h rec0 (q 0) := by
    cases hr with
    | cons hhead _ =>
      cases hl with
      | cons cell _ => exact ⟨_, _, cell, hhead⟩
  obtain ⟨sp, np, dp, hpair0, hbit0, hnum0, hden0⟩ := hrec0
  -- a list of length `n + 1`
  obtain ⟨e1, v1, c1⟩ := allocate_fits hh (cons_fits (null_lt hh) hl.allocated)
  have hl1 : ListAt (h ++ [.cons 0 wp]) h.length (0 :: ptrs) := .cons c1 (hl.mono e1)
  obtain ⟨h2, Pp, e2, v2, hP, padRun⟩ := RegisterWiden.pad_compiled code d.pad d.widen hpad
    hwiden v1 hl1 (hden0.mono e1)
  have hlen1 : (0 :: ptrs).length = k + 1 + 1 := by simp [hlen]
  rw [hlen1] at hP padRun
  set P := Bits.pad (q 0).denominator (k + 1 + 1) with hPdef
  obtain ⟨h3, shp, e3, v3, hsh, widenRun⟩ := RegisterWiden.widen_compiled code d.widen hwiden
    v2 hP (hden0.mono (e1.trans e2))
  obtain ⟨h4, zp, e4, v4, hz, -, zeroRun⟩ := RegisterZero.compiled code d.div.zero hzero v3 hsh
  obtain ⟨h5, op, e5, v5, hone, oneRun⟩ := addCarry_run code d.div.add hadd v4 true hz hz
  have e15 := e1.trans (e2.trans (e3.trans (e4.trans e5)))
  -- the denominator product
  obtain ⟨h6, Dp, e6, v6, hD, denRun⟩ := RegisterListFold.compiled_const code d.denFold d.denItem
    hdenFold (fun heap ptr (x : BinaryRational.Word w) => StoredRational.At heap ptr x)
    (fun heap ptr (x : Bits ((w + 1) * (k + 1 + 1))) => BitsAt heap ptr x)
    (fun heap ptr (x : Bits (width w (k + 1))) => BitsAt heap ptr x)
    (fun he _ _ hx => StoredRational.At.mono he hx) (fun he _ _ hx => hx.mono he)
    (fun P acc x => denStep P acc x) (denItemBudget ((w + 1) * (k + 1 + 1)) (width w (k + 1)))
    v5 (hw.mono e15) (hP.mono (e3.trans (e4.trans e5))) hone
    (fun _ _ _ _ _ hv _ _ hx hd hs => denItem_compiled code d hm hv hx hd hs)
  have hDw : ((List.finRange (k + 1)).map q).foldl (denStep P)
      (Bits.addCarry (Bits.zero (width w (k + 1))) (Bits.zero (width w (k + 1))) true).1 =
      denWord P q := rfl
  rw [hDw] at hD
  -- the data record `((P, D), zero)`
  obtain ⟨e7, v7, c7⟩ := allocate_fits v6
    (pair_fits ((hP.mono (e3.trans (e4.trans (e5.trans e6)))).allocated) hD.allocated)
  obtain ⟨e8, v8, c8⟩ := allocate_fits v7
    (pair_fits (h := h6 ++ [Cell.pair Pp Dp]) (a := h6.length) (by simp)
      ((hz.mono (e5.trans (e6.trans e7))).allocated))
  have hdata : MuDataAt (h6 ++ [Cell.pair Pp Dp] ++ [Cell.pair h6.length zp])
      (h6 ++ [Cell.pair Pp Dp]).length
      (P, denWord P q, Bits.zero (width w (k + 1))) :=
    ⟨h6.length, zp, Pp, Dp, c8, e8.lookup c7,
      hP.mono (e3.trans (e4.trans (e5.trans (e6.trans (e7.trans e8))))),
      hD.mono (e7.trans e8), hz.mono (e5.trans (e6.trans (e7.trans e8)))⟩
  have e18 := e15.trans (e6.trans (e7.trans e8))
  -- the scaled weights
  obtain ⟨h9, musp, e9, v9, hmus, muRun⟩ := RegisterListMap.compiled_const code d.muMap d.muItem
    hmuMap (fun heap ptr (x : BinaryRational.Word w) => StoredRational.At heap ptr x)
    (fun heap ptr (x : Bits ((w + 1) * (k + 1 + 1)) × Bits (width w (k + 1)) ×
      Bits (width w (k + 1))) => MuDataAt heap ptr x)
    (fun heap ptr (x : Bits (width w (k + 1))) => BitsAt heap ptr x)
    (fun he _ _ hx => StoredRational.At.mono he hx) (fun he _ _ hx => hx.mono he)
    (fun he _ _ hx => hx.mono he) (fun _ hx => hx.allocated)
    (fun x qv => muWord x.1 x.2.1 x.2.2 qv) (muItemBudget ((w + 1) * (k + 1 + 1)) (width w (k + 1)))
    v8 (hw.mono e18) hdata (fun hv _ _ _ hx hd => muItem_compiled code d hm hv hx hd)
  have hmusEq : ((List.finRange (k + 1)).map q).map
      (fun qv => muWord P (denWord P q) (Bits.zero (width w (k + 1))) qv) = muWords q :=
    map_muWord P q hq hwpos
  rw [hmusEq] at hmus
  -- the large capacity
  obtain ⟨h10, bigp, e10, v10, hbig, sumRun⟩ := RegisterListFold.compiled_const code d.sumFold
    d.sumItem hsumFold (fun heap ptr (x : Bits (width w (k + 1))) => BitsAt heap ptr x)
    (fun _ _ (_ : Unit) => True) (fun heap ptr (x : Bits (width w (k + 1))) => BitsAt heap ptr x)
    (fun he _ _ hx => hx.mono he) (fun _ _ _ _ => trivial)
    (fun _ acc m => sumStep acc m) (sumItemBudget (width w (k + 1))) (dataPtr := 0) (data := ())
    v9 hmus trivial (hone.mono (e6.trans (e7.trans (e8.trans e9))))
    (fun _ _ _ _ _ hv _ _ hx _ hs => sumItem_compiled code d hm hv hx hs)
  have hbigEq : (muWords q).foldl (fun acc m => sumStep acc m)
      (Bits.addCarry (Bits.zero (width w (k + 1))) (Bits.zero (width w (k + 1))) true).1 =
      GraphReachEncoded.word (width w (k + 1)) (big q) := bigWord_eq q hq hwpos
  rw [hbigEq] at hbig
  refine ⟨h10, musp, bigp, zp, e18.trans (e9.trans e10), v10, WordsAt.mono e10 hmus, hbig,
    by rw [← zero_eq_word]; exact hz.mono (e5.trans (e6.trans (e7.trans (e8.trans (e9.trans e10))))),
    ?_⟩
  -- the derivation
  let r0 := initialRegisters [Value.pointer wp]
  let r1 := loadRegisters r0 1 2 15 (.cons rec0 tail)
  let r2 := loadRegisters r1 3 4 15 (.pair sp dp)
  let r3 := Function.update r2 5 (.pointer h.length)
  let r4 := bindResults r3 [6] [.pointer Pp]
  let r5 := bindResults r4 [7] [.pointer shp]
  let r6 := bindResults r5 [8] [.pointer zp]
  let r7 := bindResults r6 [9, 10] [.pointer op, .flag (Bits.addCarry (Bits.zero (width w (k + 1)))
    (Bits.zero (width w (k + 1))) true).2.1]
  let r8 := bindResults r7 [11] [.pointer Dp]
  let r9 := Function.update r8 12 (.pointer h6.length)
  let r10 := Function.update r9 13 (.pointer (h6 ++ [Cell.pair Pp Dp]).length)
  let r11 := bindResults r10 [14] [.pointer musp]
  let r12 := bindResults r11 [15] [.pointer bigp]
  have last : Within code h10 r12 (.ret [.register 14, .register 15, .register 8])
      [.pointer musp, .pointer bigp, .pointer zp] h10 7 := by
    simpa [values, Atom.eval, r12, r11, r10, r9, r8, r7, r6, bindResults] using
      Within.ret code h10 r12 [.register 14, .register 15, .register 8]
  have aS : values r11 [.register 14, .null, .register 9] =
      [.pointer musp, .pointer 0, .pointer op] := by
    simp [values, Atom.eval, r11, r10, r9, r8, r7, bindResults]
  have cS := Within.call (procedure := d.sumFold) (regs := r11)
    (arguments := [.register 14, .null, .register 9]) (results := [15])
    (by simpa only [aS] using sumRun) last
  have aM : values r10 [.register 0, .register 13] =
      [.pointer wp, .pointer (h6 ++ [Cell.pair Pp Dp]).length] := by
    simp [values, Atom.eval, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, r0, bindResults,
      loadRegisters, decoded, initialRegisters]
  have cM := Within.call (procedure := d.muMap) (regs := r10)
    (arguments := [.register 0, .register 13]) (results := [14])
    (by simpa only [aM] using muRun) cS
  have a13 := Within.allocate (regs := r9) (dst := 13) (h := h6 ++ [Cell.pair Pp Dp])
    (expr := .pair (.register 12) (.register 8)) (c := .pair h6.length zp)
    (by simp [CellExpr.eval, Atom.eval, r9, r8, r7, r6, bindResults, Value.asPointer]) cM
  have a12 := Within.allocate (regs := r8) (dst := 12) (h := h6)
    (expr := .pair (.register 6) (.register 11)) (c := .pair Pp Dp)
    (by simp [CellExpr.eval, Atom.eval, r8, r7, r6, r5, r4, bindResults, Value.asPointer]) a13
  have aD : values r7 [.register 0, .register 6, .register 9] =
      [.pointer wp, .pointer Pp, .pointer op] := by
    simp [values, Atom.eval, r7, r6, r5, r4, r3, r2, r1, r0, bindResults, loadRegisters,
      decoded, initialRegisters]
  have cD := Within.call (procedure := d.denFold) (regs := r7)
    (arguments := [.register 0, .register 6, .register 9]) (results := [11])
    (by simpa only [aD] using denRun) a12
  have aA : values r6 [.register 8, .register 8, .flag true] =
      [.pointer zp, .pointer zp, .flag true] := by
    simp [values, Atom.eval, r6, bindResults]
  have cA := Within.call (procedure := d.div.add) (regs := r6)
    (arguments := [.register 8, .register 8, .flag true]) (results := [9, 10])
    (by simpa only [aA] using oneRun) cD
  have aZ : values r5 [.register 7] = [.pointer shp] := by
    simp [values, Atom.eval, r5, bindResults]
  have cZ := Within.call (procedure := d.div.zero) (regs := r5)
    (arguments := [.register 7]) (results := [8]) (by simpa only [aZ] using zeroRun) cA
  have aW : values r4 [.register 6, .register 4] = [.pointer Pp, .pointer dp] := by
    simp [values, Atom.eval, r4, r3, r2, r1, r0, bindResults, loadRegisters, decoded]
  have cW := Within.call (procedure := d.widen) (regs := r4)
    (arguments := [.register 6, .register 4]) (results := [7])
    (by simpa only [aW] using widenRun) cZ
  have aP : values r3 [.register 5, .register 4] = [.pointer h.length, .pointer dp] := by
    simp [values, Atom.eval, r3, r2, r1, r0, loadRegisters, decoded]
  have cP := Within.call (procedure := d.pad) (regs := r3)
    (arguments := [.register 5, .register 4]) (results := [6])
    (by simpa only [aP] using padRun) cW
  have a5 := Within.allocate (regs := r2) (dst := 5) (h := h)
    (expr := .cons .null (.register 0)) (c := .cons 0 wp)
    (by simp [CellExpr.eval, Atom.eval, r2, r1, r0, loadRegisters, decoded, initialRegisters,
      Value.asPointer]) cP
  have l2 := Within.load (regs := r1) (address := .register 1) (first := 3) (second := 4)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .allocate 5 (.cons .null (.register 0))
        (.call d.pad [.register 5, .register 4] [6]
          (.call d.widen [.register 6, .register 4] [7]
            (.call d.div.zero [.register 7] [8]
              (.call d.div.add [.register 8, .register 8, .flag true] [9, 10]
                (.call d.denFold [.register 0, .register 6, .register 9] [11]
                  (.allocate 12 (.pair (.register 6) (.register 11))
                    (.allocate 13 (.pair (.register 12) (.register 8))
                      (.call d.muMap [.register 0, .register 13] [14]
                        (.call d.sumFold [.register 14, .null, .register 9] [15]
                          (.ret [.register 14, .register 15, .register 8])))))))))) })
    (by simp [Atom.eval, r1, loadRegisters, decoded]) hpair0 a5
  have l1 := Within.load (regs := r0) (address := .register 0) (first := 1) (second := 2)
    (bit := 15) (branches := { CompiledTrie.failCases with
      cons := .load (.register 1) 3 4 15 { CompiledTrie.failCases with
        pair := .allocate 5 (.cons .null (.register 0))
          (.call d.pad [.register 5, .register 4] [6]
            (.call d.widen [.register 6, .register 4] [7]
              (.call d.div.zero [.register 7] [8]
                (.call d.div.add [.register 8, .register 8, .flag true] [9, 10]
                  (.call d.denFold [.register 0, .register 6, .register 9] [11]
                    (.allocate 12 (.pair (.register 6) (.register 11))
                      (.allocate 13 (.pair (.register 12) (.register 8))
                        (.call d.muMap [.register 0, .register 13] [14]
                          (.call d.sumFold [.register 14, .null, .register 9] [15]
                            (.ret [.register 14, .register 15, .register 8])))))))))) } })
    (by simp [Atom.eval, r0, initialRegisters]) cell0 l2
  rw [hself]
  refine l1.mono ?_
  simp only [budget, List.length_cons, List.length_nil, CellExpr.args, List.length_finRange,
    List.length_map, muWords, width]
  omega

theorem budget_le (w n : ℕ) : budget w n ≤ 1200 * (width w n + 1) ^ 2 * (n + 1) := by
  simp only [budget, width, RegisterWiden.padBudget, RegisterWiden.widenBudget,
    denItemBudget, muItemBudget, sumItemBudget, multiplyBudget]
  generalize hj : (w + 1) * (n + 1) = j
  have hwj : w ≤ j := by rw [← hj]; nlinarith
  nlinarith [Nat.zero_le (j * j * n), Nat.zero_le (w * j * n), Nat.zero_le (j * n),
    Nat.zero_le (w * n), Nat.zero_le (w * w * n), Nat.zero_le (j * j), Nat.zero_le (w * j)]

theorem width_succ_le (w n : ℕ) : width w n + 1 ≤ (w + 2) * (n + 2) := by
  simp only [width]
  nlinarith

end WeightedMIS.RegisterNetworkWeights
