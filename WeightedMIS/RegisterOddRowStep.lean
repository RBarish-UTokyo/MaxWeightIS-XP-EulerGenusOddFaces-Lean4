module

public import WeightedMIS.RegisterParityTable
public import WeightedMIS.RegisterResidualSearch
public import WeightedMIS.RegisterListFold
public import WeightedMIS.RegisterListMap
public import WeightedMIS.RegisterSignedAdd
public import WeightedMIS.SignedWords

/-!
# Procedures of the compiled odd row and the route-arc step

The step procedure processes one stored parity route arc: it strips the parity
bits of both endpoints, searches the first edge-index record joining the two
vertex words, compares its index word with the current index word and, on a
match, adds the signed unit given by the parity bit of the arc source to the
signed state. It refines `ParityReachRefinement.stepW`. The whole procedure
table of the odd row is declared here; `RegisterOddRow` composes it.
-/

@[expose] public section

namespace WeightedMIS.RegisterOddRow

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.ResidualWords
open WeightedMIS.RegisterPotentialStep WeightedMIS.GraphReachEncoded WeightedMIS.RegisterFirstEdge
open WeightedMIS.ParityReachRefinement WeightedMIS.SignedWords
open WeightedMIS.RegisterIncidenceRows (EdgeAt eqb)

variable {W K G : ℕ}

/-! ## Data records -/

/-- Fold data `.pair records (.pair index one)`, with a fixed record count. -/
def StepDataAt (M : ℕ) (h : Heap) (p : Ptr) (d : List (Record W K) × Bits K × Bits G) : Prop :=
  ∃ rp rest ip op, h[p]? = some (.pair rp rest) ∧ h[rest]? = some (.pair ip op) ∧
    RecordsAt h rp d.1 ∧ BitsAt h ip d.2.1 ∧ BitsAt h op d.2.2 ∧ d.1.length = M

theorem StepDataAt.mono {M : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr}
    {d : List (Record W K) × Bits K × Bits G} (hd : StepDataAt M h p d) : StepDataAt M h' p d := by
  obtain ⟨rp, rest, ip, op, c1, c2, hr, hi, ho, hl⟩ := hd
  exact ⟨rp, rest, ip, op, he.lookup c1, he.lookup c2, hr.mono he, hi.mono he, ho.mono he, hl⟩

/-- Row data `.pair records (.pair route (.pair one signedZero))`. -/
def RowDataAt (M L : ℕ) (h : Heap) (p : Ptr)
    (d : List (Record W K) × List (Arc (W + 1) 1) × Bits G × Bits G) : Prop :=
  ∃ rp r1 tp r2 op zp, h[p]? = some (.pair rp r1) ∧ h[r1]? = some (.pair tp r2) ∧
    h[r2]? = some (.pair op zp) ∧ RecordsAt h rp d.1 ∧ TableAt h tp d.2.1 ∧
    BitsAt h op d.2.2.1 ∧ SignedAt h zp ((false, d.2.2.2) : Word G) ∧ d.1.length = M ∧
    d.2.1.length ≤ L

theorem RowDataAt.mono {M L : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr}
    {d : List (Record W K) × List (Arc (W + 1) 1) × Bits G × Bits G}
    (hd : RowDataAt M L h p d) : RowDataAt M L h' p d := by
  obtain ⟨rp, r1, tp, r2, op, zp, c1, c2, c3, hr, ht, ho, hz, hl, hL⟩ := hd
  exact ⟨rp, r1, tp, r2, op, zp, he.lookup c1, he.lookup c2, he.lookup c3, hr.mono he,
    ht.mono he, ho.mono he, hz.mono he, hl, hL⟩

/-! ## Procedures -/

variable {p : ℕ}

/-- The signed addition of the unit and the final result. -/
def addCase (sadd : Fin p) : Command p :=
  .load (.register 2) 10 11 12 { CompiledTrie.failCases with
    bit := .call sadd [.register 12, .register 10, .register 9, .register 6] [13, 14]
      (.allocate 15 (.bit (.register 13) (.register 14)) (.ret [.register 15])) }

/-- The index comparison after a successful first-edge search. -/
def foundCase (cmp sadd : Fin p) : Command p :=
  .load (.register 15) 3 4 6 { CompiledTrie.failCases with
    pair := .load (.register 13) 5 6 11 { CompiledTrie.failCases with
      pair := .call cmp [.register 4, .register 5] [7, 8]
        (.branch (.register 8) (addCase sadd) (.ret [.register 2])) } }

/-- The search part after the arc and the data have been loaded. -/
def searchCase (find cmp sadd : Fin p) : Command p :=
  .allocate 11 (.pair (.register 7) (.register 10))
    (.load (.register 1) 12 13 15 { CompiledTrie.failCases with
      pair := .call find [.register 12, .register 11] [14, 15]
        (.branch (.register 14) (foundCase cmp sadd) (.ret [.register 2])) })

/-- Arguments: route arc, fold data, signed state. Result: the new state. -/
def stepBody (find cmp sadd : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    pair := .load (.register 4) 5 6 15 { CompiledTrie.failCases with
      pair := .load (.register 3) 7 8 9 { CompiledTrie.failCases with
        bit := .load (.register 5) 10 11 12 { CompiledTrie.failCases with
          bit := searchCase find cmp sadd } } } }

/-- Arguments: index word, row data. Result: the signed row word. -/
def rowBody (fold : Fin p) : Command p :=
  .load (.register 1) 2 3 15 { CompiledTrie.failCases with
    pair := .load (.register 3) 4 5 15 { CompiledTrie.failCases with
      pair := .load (.register 5) 6 7 15 { CompiledTrie.failCases with
        pair := .allocate 8 (.pair (.register 0) (.register 6))
          (.allocate 9 (.pair (.register 2) (.register 8))
            (.call fold [.register 4, .register 9, .register 7] [10] (.ret [.register 10]))) } } }

/-- Arguments: edges, index words, vertex words, root word, unit word of width
one, unit word, zero word. Results: the signed row words and the parity flag. -/
def oddRowBody (ptable search member lookup rows : Fin p) : Command p :=
  .call ptable [.register 0, .register 1, .register 2, .register 4] [7, 8, 9]
  (.allocate 10 (.bit (.flag false) (.register 3))
  (.call search [.register 7, .register 4, .register 9, .register 10] [11, 12]
  (.allocate 10 (.bit (.flag true) (.register 3))
  (.call member [.register 10, .register 11] [13]
  (.call lookup [.register 10, .register 12] [14]
  (.allocate 15 (.bit (.flag false) (.register 6))
  (.allocate 12 (.pair (.register 5) (.register 15))
  (.allocate 11 (.pair (.register 14) (.register 12))
  (.allocate 10 (.pair (.register 8) (.register 11))
  (.call rows [.register 1, .register 10] [12]
  (.ret [.register 12, .register 13])))))))))))

structure Procedures (p : ℕ) where
  ptable : RegisterParityTable.Procedures p
  search : RegisterResidualSearch.Procedures p
  searchEntry : Fin p
  add : Fin p
  complement : Fin p
  sub : Fin p
  signedAdd : Fin p
  step : Fin p
  fold : Fin p
  row : Fin p
  rows : Fin p
  self : Fin p

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  d.ptable.Matches code ∧ d.search.Matches code ∧
  code d.searchEntry = RegisterResidualSearch.searchBody d.search.reach d.search.prepend ∧
  code d.add = RegisterAdder.adderBody d.add ∧
  code d.complement = RegisterComplement.complementBody d.complement ∧
  code d.sub = RegisterSubtractor.subtractorBody d.complement d.add ∧
  code d.signedAdd = RegisterSignedAdd.signedAddBody d.add d.ptable.table.edge.cmp d.sub ∧
  code d.step = stepBody d.ptable.table.edge.find d.ptable.table.edge.cmp d.signedAdd ∧
  code d.fold = RegisterListFold.body d.fold d.step ∧
  code d.row = rowBody d.fold ∧
  code d.rows = RegisterListMap.body d.rows d.row ∧
  code d.self = oddRowBody d.ptable.self d.searchEntry d.search.member d.search.lookup d.rows

def stepBudget (W K G M : ℕ) : ℕ := findBudget W M + 36 * K + 180 * G + 300

theorem step_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code) {M : ℕ}
    {h : Heap} (hh : Valid h) {ap dp sp : Ptr} {a : Arc (W + 1) 1}
    {data : List (Record W K) × Bits K × Bits G} {acc : Word G}
    (ha : ArcAt h ap a) (hd : StepDataAt M h dp data) (hs : SignedAt h sp acc) :
    ∃ out q, Extends h out ∧ Valid out ∧
      SignedAt out q (stepW data.1 data.2.1 data.2.2 acc a) ∧
      Within code h (initialRegisters [.pointer ap, .pointer dp, .pointer sp])
        (code d.step) [.pointer q] out (stepBudget W K G M) := by
  obtain ⟨hpt, -, -, hadd, hcomp, hsub, hsadd, hstep, -⟩ := hm
  have hedge := hpt.1.1
  have hcmp := hedge.1
  obtain ⟨src, tgt, cap⟩ := a
  obtain ⟨sa, tl, ta, ca, c1, c2, hsrc, htgt, -⟩ := ha
  cases src with
  | cons b sv =>
  cases tgt with
  | cons c tv =>
  cases hsrc with
  | cons c3 hsv =>
  rename_i sb
  cases htgt with
  | cons c4 htv =>
  rename_i tb
  obtain ⟨recs, idx, oneG⟩ := data
  obtain ⟨rp, rest, ip, op, c5, c6, hr, hi, ho, hl⟩ := hd
  obtain ⟨s, mag⟩ := acc
  obtain ⟨mp, c7, hmag⟩ := hs
  simp only at hr hi ho hl hmag
  -- the query cell
  let H1 := h ++ [Cell.pair sb tb]
  obtain ⟨e1, v1, q1⟩ := allocate_fits hh (pair_fits hsv.allocated htv.allocated)
  have hq : QueryAt H1 h.length (sv, tv) := ⟨sb, tb, q1, hsv.mono e1, htv.mono e1⟩
  obtain ⟨H2, r, e2, v2, hfound, frun⟩ := find_compiled code d.ptable.table.edge hedge v1
    (hr.mono e1) hq
  have e12 := e1.trans e2
  let regs := initialRegisters [Value.pointer ap, .pointer dp, .pointer sp]
  let s1 := loadRegisters regs 3 4 15 (.pair sa tl)
  let s2 := loadRegisters s1 5 6 15 (.pair ta ca)
  let s3 := loadRegisters s2 7 8 9 (.bit b sb)
  let s4 := loadRegisters s3 10 11 12 (.bit c tb)
  let s5 := Function.update s4 11 (.pointer h.length)
  let s6 := loadRegisters s5 12 13 15 (.pair rp rest)
  let s7 := bindResults s6 [14, 15] [.flag (recs.find? (pred (sv, tv))).isSome, .pointer r]
  have hstate : ∀ heap : Heap, Within code heap s7 (.ret [.register 2]) [.pointer sp] heap 3 := by
    intro heap
    simpa [s7, s6, s5, s4, s3, s2, s1, regs, bindResults, loadRegisters, decoded,
      initialRegisters, values, Atom.eval] using Within.ret code heap s7 [.register 2]
  -- the run after the search call
  have tailRun : ∃ out q, Extends H2 out ∧ Valid out ∧
      SignedAt out q (stepW recs idx oneG (s, mag) ⟨.cons b sv, .cons c tv, cap⟩) ∧
      Within code H2 s7 (.branch (.register 14) (foundCase d.ptable.table.edge.cmp d.signedAdd)
        (.ret [.register 2])) [.pointer q] out (36 * K + 180 * G + 220) := by
    cases hx : recs.find? (pred (sv, tv)) with
    | none =>
      refine ⟨H2, sp, .refl _, v2, ?_, ?_⟩
      · simp only [stepW, base, hx]
        exact ⟨mp, e12.lookup c7, hmag.mono e12⟩
      · have br := Within.branch (b := false) (test := .register 14) (regs := s7)
          (yes := foundCase d.ptable.table.edge.cmp d.signedAdd)
          (by simp [s7, bindResults, Atom.eval, hx]) (hstate H2)
        exact br.mono (by omega)
    | some x =>
      obtain ⟨⟨xl, xr⟩, xi⟩ := x
      obtain ⟨xe, xc, c8, -, hxi⟩ := hfound _ hx
      simp only at hxi
      let s8 := loadRegisters s7 3 4 6 (.pair xe xc)
      let s9 := loadRegisters s8 5 6 11 (.pair ip op)
      let s10 := bindResults s9 [7, 8] (RegisterComparator.flags (Bits.compare xi idx).1)
      have ccmp := RegisterComparator.compiled code d.ptable.table.edge.cmp hcmp hxi
        (hi.mono e12)
      have cargs : values s9 [.register 4, .register 5] = [.pointer xc, .pointer ip] := by
        simp [s9, s8, loadRegisters, decoded, values, Atom.eval]
      have inner : ∃ out q, Extends H2 out ∧ Valid out ∧
          SignedAt out q (stepW recs idx oneG (s, mag) ⟨.cons b sv, .cons c tv, cap⟩) ∧
          Within code H2 s10 (.branch (.register 8) (addCase d.signedAdd) (.ret [.register 2]))
            [.pointer q] out (180 * G + 160) := by
        by_cases heq : eqb xi idx = true
        · let s11 := loadRegisters s10 10 11 12 (.bit s mp)
          obtain ⟨H3, res, e3, v3, hres, srun⟩ := RegisterSignedAdd.compiled code
            d.ptable.table.edge.cmp d.sub d.complement d.add hcmp hsub hcomp hadd v2
            (hmag.mono e12) (ho.mono e12) s b
          let sum := (BinaryRational.signedAdd s b mag oneG).1
          let s12 := bindResults s11 [13, 14] [.flag sum.1, .pointer res]
          let H4 := H3 ++ [Cell.bit sum.1 res]
          obtain ⟨e4, v4, q4⟩ := allocate_fits v3 (bit_fits (b := sum.1) hres.allocated)
          refine ⟨H4, H3.length, e3.trans e4, v4, ?_, ?_⟩
          · simp only [stepW, base, hx, lead]
            simp only [eqb] at heq
            simp only [eqb, heq, ↓reduceIte]
            exact ⟨res, q4, hres.mono e4⟩
          · have last : Within code H4 (Function.update s12 15 (.pointer H3.length))
                (.ret [.register 15]) [.pointer H3.length] H4 3 := by
              simpa [values, Atom.eval] using
                Within.ret code H4 (Function.update s12 15 (.pointer H3.length)) [.register 15]
            have al := Within.allocate (regs := s12) (dst := 15) (h := H3)
              (expr := .bit (.register 13) (.register 14)) (c := .bit sum.1 res)
              (by simp [CellExpr.eval, Atom.eval, s12, bindResults, Value.asPointer,
                Value.asFlag]) last
            have sargs : values s11 [.register 12, .register 10, .register 9, .register 6] =
                [.flag s, .pointer mp, .flag b, .pointer op] := by
              simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, bindResults, loadRegisters, decoded,
                values, Atom.eval, RegisterComparator.flags]
            have scall := Within.call (procedure := d.signedAdd) (regs := s11)
              (arguments := [.register 12, .register 10, .register 9, .register 6])
              (results := [13, 14]) (by rw [sargs, hsadd]; exact srun) al
            have ld := Within.load (regs := s10) (address := .register 2) (first := 10)
              (second := 11) (bit := 12) (branches := { CompiledTrie.failCases with
                bit := .call d.signedAdd [.register 12, .register 10, .register 9, .register 6]
                  [13, 14] (.allocate 15 (.bit (.register 13) (.register 14))
                    (.ret [.register 15])) })
              (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, regs, bindResults,
                loadRegisters, decoded, initialRegisters, Atom.eval, RegisterComparator.flags])
              (e12.lookup c7) scall
            have br := Within.branch (b := true) (test := .register 8) (regs := s10)
              (no := .ret [.register 2])
              (by simp only [eqb] at heq
                  simp [s10, bindResults, Atom.eval, RegisterComparator.flags, heq]) ld
            exact br.mono (by simp [CellExpr.args]; omega)
        · have hf : eqb xi idx = false := by simpa using heq
          refine ⟨H2, sp, .refl _, v2, ?_, ?_⟩
          · simp only [stepW, base, hx, hf]
            exact ⟨mp, e12.lookup c7, hmag.mono e12⟩
          · have last : Within code H2 s10 (.ret [.register 2]) [.pointer sp] H2 3 := by
              simpa [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, regs, bindResults, loadRegisters,
                decoded, initialRegisters, values, Atom.eval, RegisterComparator.flags] using
                Within.ret code H2 s10 [.register 2]
            have br := Within.branch (b := false) (test := .register 8) (regs := s10)
              (yes := addCase d.signedAdd)
              (by simp only [eqb] at hf
                  simp [s10, bindResults, Atom.eval, RegisterComparator.flags, hf]) last
            exact br.mono (by omega)
      obtain ⟨out, q, e3, v3, hq3, irun⟩ := inner
      refine ⟨out, q, e3, v3, hq3, ?_⟩
      have kcall := Within.call (procedure := d.ptable.table.edge.cmp) (regs := s9)
        (arguments := [.register 4, .register 5]) (results := [7, 8])
        (by simpa only [cargs] using ccmp) irun
      have l2 := Within.load (regs := s8) (address := .register 13) (first := 5) (second := 6)
        (bit := 11) (branches := { CompiledTrie.failCases with
          pair := .call d.ptable.table.edge.cmp [.register 4, .register 5] [7, 8]
            (.branch (.register 8) (addCase d.signedAdd) (.ret [.register 2])) })
        (by simp [s8, s7, s6, bindResults, loadRegisters, decoded, Atom.eval])
        (e12.lookup c6) kcall
      have l1 := Within.load (regs := s7) (address := .register 15) (first := 3) (second := 4)
        (bit := 6) (branches := { CompiledTrie.failCases with
          pair := .load (.register 13) 5 6 11 { CompiledTrie.failCases with
            pair := .call d.ptable.table.edge.cmp [.register 4, .register 5] [7, 8]
              (.branch (.register 8) (addCase d.signedAdd) (.ret [.register 2])) } })
        (by simp [s7, bindResults, Atom.eval]) c8 l2
      have br := Within.branch (b := true) (test := .register 14) (regs := s7)
        (no := .ret [.register 2]) (by simp [s7, bindResults, Atom.eval, hx]) l1
      exact br.mono (by simp; omega)
  obtain ⟨out, q, e3, v3, hout, trun⟩ := tailRun
  refine ⟨out, q, e12.trans e3, v3, hout, ?_⟩
  have fargs : values s6 [.register 12, .register 11] = [.pointer rp, .pointer h.length] := by
    simp [s6, s5, loadRegisters, decoded, values, Atom.eval]
  have fcall := Within.call (procedure := d.ptable.table.edge.find) (regs := s6)
    (arguments := [.register 12, .register 11]) (results := [14, 15])
    (by simpa only [fargs] using frun) trun
  have l5 := Within.load (regs := s5) (address := .register 1) (first := 12) (second := 13)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .call d.ptable.table.edge.find [.register 12, .register 11] [14, 15]
        (.branch (.register 14) (foundCase d.ptable.table.edge.cmp d.signedAdd)
          (.ret [.register 2])) })
    (by simp [s5, s4, s3, s2, s1, regs, loadRegisters, decoded, initialRegisters, Atom.eval])
    (e1.lookup c5) fcall
  have al := Within.allocate (regs := s4) (dst := 11) (h := h)
    (expr := .pair (.register 7) (.register 10)) (c := .pair sb tb)
    (by simp [CellExpr.eval, Atom.eval, s4, s3, loadRegisters, decoded, Value.asPointer]) l5
  have l4 := Within.load (regs := s3) (address := .register 5) (first := 10) (second := 11)
    (bit := 12) (branches := { CompiledTrie.failCases with
      bit := searchCase d.ptable.table.edge.find d.ptable.table.edge.cmp d.signedAdd })
    (by simp [s3, s2, loadRegisters, decoded, Atom.eval]) c4 al
  have l3 := Within.load (regs := s2) (address := .register 3) (first := 7) (second := 8)
    (bit := 9) (branches := { CompiledTrie.failCases with
      bit := .load (.register 5) 10 11 12 { CompiledTrie.failCases with
        bit := searchCase d.ptable.table.edge.find d.ptable.table.edge.cmp d.signedAdd } })
    (by simp [s2, s1, loadRegisters, decoded, Atom.eval]) c3 l4
  have l2 := Within.load (regs := s1) (address := .register 4) (first := 5) (second := 6)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 3) 7 8 9 { CompiledTrie.failCases with
        bit := .load (.register 5) 10 11 12 { CompiledTrie.failCases with
          bit := searchCase d.ptable.table.edge.find d.ptable.table.edge.cmp d.signedAdd } } })
    (by simp [s1, loadRegisters, decoded, Atom.eval]) c2 l3
  have l1 := Within.load (regs := regs) (address := .register 0) (first := 3) (second := 4)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 4) 5 6 15 { CompiledTrie.failCases with
        pair := .load (.register 3) 7 8 9 { CompiledTrie.failCases with
          bit := .load (.register 5) 10 11 12 { CompiledTrie.failCases with
            bit := searchCase d.ptable.table.edge.find d.ptable.table.edge.cmp
              d.signedAdd } } } })
    (by simp [regs, initialRegisters, Atom.eval]) c1 l2
  rw [hstep]
  exact l1.mono (by simp [stepBudget, CellExpr.args, hl]; omega)

end WeightedMIS.RegisterOddRow
