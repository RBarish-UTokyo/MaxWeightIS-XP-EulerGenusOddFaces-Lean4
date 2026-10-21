module

public import WeightedMIS.RationalWordRows
public import WeightedMIS.RegisterRationalZero
public import WeightedMIS.RegisterListCommon
public import WeightedMIS.RegisterPairReads

/-!
# Compiled projection of one stored rational vector

`scaleSub` follows two linked rows of stored rationals and builds the row of
`v_i - coef * p_i` with the compiled multiply and subtract procedures.
`project` reads a three-cell data record `(c, (p, (pv, zero)))`, computes the
coefficient `dot(c, v) / pv` with the compiled dot product and division, and
calls `scaleSub`. The output is exactly `RationalWordRows.projectW`.
-/

@[expose] public section

namespace WeightedMIS.RegisterRationalProject

open PointerMemory RegisterMachine EfficientSearch EfficientSearch.Pointer StoredRational
open RegisterRationalRow (RowAt)

variable {p N : ℕ}

/-- Arguments 0=v, 1=p, 2=coef; the result is the row `v - coef * p`. -/
def scaleSubBody (self multiply subtract : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := .load (.register 1) 5 6 15 { CompiledTrie.failCases with
      nil := .ret [.null]
      cons := .call self [.register 4, .register 6, .register 2] [7]
        (.call multiply [.register 2, .register 5] [8]
          (.call subtract [.register 3, .register 8] [9]
            (.allocate 10 (.cons (.register 9) (.register 7)) (.ret [.register 10])))) } }

/-- The data record of a projection: `(c, (p, (pv, zero)))`. -/
def DataAt (h : Heap) (ptr : Ptr)
    (d : List (BinaryRational.Word N) × List (BinaryRational.Word N) ×
      BinaryRational.Word N × BinaryRational.Word N) : Prop :=
  ∃ cp r1 pp r2 pvp zp, h[ptr]? = some (.pair cp r1) ∧ h[r1]? = some (.pair pp r2) ∧
    h[r2]? = some (.pair pvp zp) ∧ RowAt h cp d.1 ∧ RowAt h pp d.2.1 ∧
    At h pvp d.2.2.1 ∧ At h zp d.2.2.2

theorem DataAt.mono {h out : Heap} (ext : Extends h out) {ptr : Ptr}
    {d : List (BinaryRational.Word N) × List (BinaryRational.Word N) ×
      BinaryRational.Word N × BinaryRational.Word N}
    (hd : DataAt h ptr d) : DataAt out ptr d := by
  obtain ⟨cp, r1, pp, r2, pvp, zp, c1, c2, c3, hc, hp, hpv, hz⟩ := hd
  exact ⟨cp, r1, pp, r2, pvp, zp, ext.lookup c1, ext.lookup c2, ext.lookup c3,
    hc.mono ext, hp.mono ext, hpv.mono ext, hz.mono ext⟩

/-- Arguments 0=v, 1=data record; the result is the projected row. -/
def projectBody (dot divide scaleSub : Fin p) : Command p :=
  RegisterPairReads.readPairs [(1, 2, 3), (3, 4, 5), (5, 6, 7)]
    (.call dot [.register 2, .register 0, .register 7] [8]
      (.call divide [.register 8, .register 6] [9]
        (.call scaleSub [.register 0, .register 4, .register 9] [10] (.ret [.register 10]))))

structure Procedures (p : ℕ) where
  row : RegisterRationalRow.Procedures p
  subtract : Fin p
  rawSubtract : Fin p
  divide : Fin p
  rawDivide : Fin p
  scaleSub : Fin p
  project : Fin p

structure Procedures.Matches (ids : Procedures p) (code : Code p)
    (d : RegisterRationalProducts.Procedures p) : Prop where
  row : ids.row.Matches code d
  subtract : code ids.subtract =
    RegisterStoredRational.binaryBody ids.row.read ids.rawSubtract ids.row.store
  rawSubtract : code ids.rawSubtract = RegisterRationalAdd.subtractBody ids.row.rawAdd
  divide : code ids.divide =
    RegisterStoredRational.binaryBody ids.row.read ids.rawDivide ids.row.store
  rawDivide : code ids.rawDivide = RegisterRationalProducts.divideBody ids.row.rawMultiply
  scaleSub : code ids.scaleSub = scaleSubBody ids.scaleSub ids.row.multiply ids.subtract
  project : code ids.project = projectBody ids.row.self ids.divide ids.scaleSub

theorem subtract_compiled (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d)
    {h : Heap} (hh : Valid h) {qp rp : Ptr} {q r : BinaryRational.Word N}
    (hq : At h qp q) (hr : At h rp r) :
    ∃ out result, Extends h out ∧ Valid out ∧ At out result (BinaryRational.subtract q r).1 ∧
      Within code h (initialRegisters [.pointer qp, .pointer rp]) (code ids.subtract)
        [.pointer result] out (RegisterStoredRational.scalarBudget N) := by
  rw [hcode.subtract]
  exact RegisterStoredRational.subtract_compiled code ids.row.read ids.rawSubtract ids.row.store
    ids.row.signedAdd ids.row.rawAdd d hcode.row.arithmetic hcode.row.read hcode.row.store
    hcode.row.signedAdd hcode.row.rawAdd hcode.rawSubtract hh hq hr

theorem divide_compiled (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d)
    {h : Heap} (hh : Valid h) {qp rp : Ptr} {q r : BinaryRational.Word N}
    (hq : At h qp q) (hr : At h rp r) :
    ∃ out result, Extends h out ∧ Valid out ∧ At out result (BinaryRational.divide q r).1 ∧
      Within code h (initialRegisters [.pointer qp, .pointer rp]) (code ids.divide)
        [.pointer result] out (RegisterStoredRational.scalarBudget N) := by
  rw [hcode.divide]
  exact RegisterStoredRational.divide_compiled code ids.row.read ids.rawDivide ids.row.store
    ids.row.rawMultiply d hcode.row.arithmetic hcode.row.read hcode.row.store
    hcode.row.rawMultiply hcode.rawDivide hh hq hr

theorem multiply_compiled (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d)
    {h : Heap} (hh : Valid h) {qp rp : Ptr} {q r : BinaryRational.Word N}
    (hq : At h qp q) (hr : At h rp r) :
    ∃ out result, Extends h out ∧ Valid out ∧ At out result (BinaryRational.multiply q r).1 ∧
      Within code h (initialRegisters [.pointer qp, .pointer rp]) (code ids.row.multiply)
        [.pointer result] out (RegisterStoredRational.scalarBudget N) := by
  rw [hcode.row.multiply]
  exact RegisterStoredRational.multiply_compiled code ids.row.read ids.row.rawMultiply
    ids.row.store d hcode.row.arithmetic hcode.row.read hcode.row.store hcode.row.rawMultiply
    hh hq hr

def scaleSubBudget (N length : ℕ) : ℕ :=
  (2 * RegisterStoredRational.scalarBudget N + 50) * length + 23

theorem scaleSub_compiled (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d)
    {h : Heap} (hh : Valid h) {vp pp cp : Ptr}
    {vs ps : List (BinaryRational.Word N)} {coef : BinaryRational.Word N}
    (hv : RowAt h vp vs) (hp : RowAt h pp ps) (hc : At h cp coef) :
    ∃ out result, Extends h out ∧ Valid out ∧
      RowAt out result (RationalWordRows.scaleSubW coef vs ps) ∧
      Within code h (initialRegisters [.pointer vp, .pointer pp, .pointer cp])
        (code ids.scaleSub) [.pointer result] out (scaleSubBudget N vs.length) := by
  obtain ⟨vps, hvl, hvr⟩ := hv
  induction hvl generalizing vs pp ps with
  | @nil vp cell =>
    cases hvr
    refine ⟨h, 0, .refl h, hh, RegisterListCommon.listRep_null hh, ?_⟩
    let regs := initialRegisters [Value.pointer vp, .pointer pp, .pointer cp]
    let loaded := loadRegisters regs 3 4 15 .nil
    have last : Within code h loaded (.ret [.null]) [.pointer 0] h 3 := by
      simpa [values, Atom.eval] using Within.ret code h loaded [.null]
    rw [hcode.scaleSub]
    apply Within.mono (a := 13) ?_ (by simp [scaleSubBudget])
    exact Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
      (branches := {CompiledTrie.failCases with
        nil := .ret [.null],
        cons := .load (.register 1) 5 6 15 {CompiledTrie.failCases with
          nil := .ret [.null],
          cons := .call ids.scaleSub [.register 4, .register 6, .register 2] [7]
            (.call ids.row.multiply [.register 2, .register 5] [8]
              (.call ids.subtract [.register 3, .register 8] [9]
                (.allocate 10 (.cons (.register 9) (.register 7))
                  (.ret [.register 10]))))}})
      (by simp [Atom.eval, regs, initialRegisters]) cell last
  | @cons vp ap vt vps cell tail ih =>
    cases hvr with
    | @cons _ v _ vs hva hvs =>
      obtain ⟨pps, hpl, hpr⟩ := hp
      cases hpl with
      | nil pcell =>
        cases hpr
        refine ⟨h, 0, .refl h, hh, RegisterListCommon.listRep_null hh, ?_⟩
        let regs := initialRegisters [Value.pointer vp, .pointer pp, .pointer cp]
        let lv := loadRegisters regs 3 4 15 (.cons ap vt)
        let lp := loadRegisters lv 5 6 15 .nil
        have last : Within code h lp (.ret [.null]) [.pointer 0] h 3 := by
          simpa [values, Atom.eval] using Within.ret code h lp [.null]
        have right := Within.load (address := .register 1) (first := 5) (second := 6) (bit := 15)
          (branches := {CompiledTrie.failCases with
            nil := .ret [.null],
            cons := .call ids.scaleSub [.register 4, .register 6, .register 2] [7]
              (.call ids.row.multiply [.register 2, .register 5] [8]
                (.call ids.subtract [.register 3, .register 8] [9]
                  (.allocate 10 (.cons (.register 9) (.register 7))
                    (.ret [.register 10]))))})
          (by simp [Atom.eval, lv, loadRegisters, decoded, regs, initialRegisters]) pcell last
        have left := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
          (branches := {CompiledTrie.failCases with
            nil := .ret [.null],
            cons := .load (.register 1) 5 6 15 {CompiledTrie.failCases with
              nil := .ret [.null],
              cons := .call ids.scaleSub [.register 4, .register 6, .register 2] [7]
                (.call ids.row.multiply [.register 2, .register 5] [8]
                  (.call ids.subtract [.register 3, .register 8] [9]
                    (.allocate 10 (.cons (.register 9) (.register 7))
                      (.ret [.register 10]))))}})
          (by simp [Atom.eval, regs, initialRegisters]) cell right
        rw [hcode.scaleSub]
        exact left.mono (by simp [scaleSubBudget])
      | @cons pp bp pt pps pcell ptail =>
        cases hpr with
        | @cons _ q _ qs hpa hps =>
          obtain ⟨mid, suffix, e1, v1, hsuffix, recurse⟩ := ih ⟨pps, ptail, hps⟩ hvs
          obtain ⟨mid2, product, e2, v2, hproduct, multiplied⟩ :=
            multiply_compiled code ids d hcode v1 (hc.mono e1) (hpa.mono e1)
          obtain ⟨mid3, diff, e3, v3, hdiff, subtracted⟩ :=
            subtract_compiled code ids d hcode v2 ((hva.mono e1).mono e2) hproduct
          have hsuffix3 : RowAt mid3 suffix (RationalWordRows.scaleSubW coef vs qs) :=
            (hsuffix.mono e2).mono e3
          obtain ⟨e4, v4, hout⟩ := RegisterListCommon.allocate_consRep
            (R := fun heap ptr (q : BinaryRational.Word N) => At heap ptr q)
            (fun ext _ _ hq => At.mono ext hq) v3 hdiff hdiff.allocated hsuffix3
          refine ⟨mid3 ++ [.cons diff suffix], mid3.length, e1.trans (e2.trans (e3.trans e4)),
            v4, by rw [RationalWordRows.scaleSubW]; exact hout, ?_⟩
          let r0 := initialRegisters [Value.pointer vp, .pointer pp, .pointer cp]
          let r1 := loadRegisters r0 3 4 15 (.cons ap vt)
          let r2 := loadRegisters r1 5 6 15 (.cons bp pt)
          let r3 := bindResults r2 [7] [Value.pointer suffix]
          let r4 := bindResults r3 [8] [Value.pointer product]
          let r5 := bindResults r4 [9] [Value.pointer diff]
          have last := RegisterListCommon.within_consRet code mid3 (regs := r5) (dst := 10)
            (head := 9) (tail := 7) (a := diff) (t := suffix)
            (by simp [r5, bindResults]) (by simp [r5, r4, r3, bindResults])
          have subArgs : values r4 [.register 3, .register 8] = [.pointer ap, .pointer product] := by
            simp [r4, r3, r2, r1, bindResults, loadRegisters, decoded, values, Atom.eval]
          have subCall := Within.call (procedure := ids.subtract)
            (arguments := [.register 3, .register 8]) (results := [9]) (regs := r4)
            (by simpa only [subArgs] using subtracted) last
          have mulArgs : values r3 [.register 2, .register 5] = [.pointer cp, .pointer bp] := by
            simp [r3, r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters, values,
              Atom.eval]
          have mulCall := Within.call (procedure := ids.row.multiply)
            (arguments := [.register 2, .register 5]) (results := [8]) (regs := r3)
            (by simpa only [mulArgs] using multiplied) subCall
          have recArgs : values r2 [.register 4, .register 6, .register 2] =
              [.pointer vt, .pointer pt, .pointer cp] := by
            simp [r2, r1, r0, loadRegisters, decoded, initialRegisters, values, Atom.eval]
          have recCall := Within.call (procedure := ids.scaleSub)
            (arguments := [.register 4, .register 6, .register 2]) (results := [7]) (regs := r2)
            (by simpa only [recArgs] using recurse) mulCall
          have right := Within.load (address := .register 1) (first := 5) (second := 6) (bit := 15)
            (branches := {CompiledTrie.failCases with
              nil := .ret [.null],
              cons := .call ids.scaleSub [.register 4, .register 6, .register 2] [7]
                (.call ids.row.multiply [.register 2, .register 5] [8]
                  (.call ids.subtract [.register 3, .register 8] [9]
                    (.allocate 10 (.cons (.register 9) (.register 7))
                      (.ret [.register 10]))))})
            (by simp [Atom.eval, r1, r0, loadRegisters, decoded, initialRegisters]) pcell recCall
          have left := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
            (branches := {CompiledTrie.failCases with
              nil := .ret [.null],
              cons := .load (.register 1) 5 6 15 {CompiledTrie.failCases with
                nil := .ret [.null],
                cons := .call ids.scaleSub [.register 4, .register 6, .register 2] [7]
                  (.call ids.row.multiply [.register 2, .register 5] [8]
                    (.call ids.subtract [.register 3, .register 8] [9]
                      (.allocate 10 (.cons (.register 9) (.register 7))
                        (.ret [.register 10]))))}})
            (by simp [Atom.eval, r0, initialRegisters]) cell right
          rw [hcode.scaleSub]
          exact left.mono (by
            simp only [scaleSubBudget, List.length_cons, List.length_nil, Nat.mul_add]
            omega)

def projectBudget (N cLength vLength : ℕ) : ℕ :=
  RegisterRationalRow.budget N cLength + RegisterStoredRational.scalarBudget N +
    scaleSubBudget N vLength + 70

theorem project_compiled (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d)
    {h : Heap} (hh : Valid h) {vp dp : Ptr}
    {v c ps : List (BinaryRational.Word N)} {pv zero : BinaryRational.Word N}
    (hv : RowAt h vp v) (hd : DataAt h dp (c, ps, pv, zero)) :
    ∃ out result, Extends h out ∧ Valid out ∧
      RowAt out result (RationalWordRows.projectW zero c ps pv v) ∧
      Within code h (initialRegisters [.pointer vp, .pointer dp])
        (code ids.project) [.pointer result] out (projectBudget N c.length v.length) := by
  obtain ⟨cp, q1, pp, q2, pvp, zp, c1, c2, c3, hc, hp, hpv, hz⟩ := hd
  obtain ⟨mid, dotp, e1, v1, hdot, dotted⟩ :=
    RegisterRationalRow.compiled code ids.row d hcode.row hh hc hv hz
  obtain ⟨mid2, coefp, e2, v2, hcoef, divided⟩ :=
    divide_compiled code ids d hcode v1 hdot (hpv.mono e1)
  obtain ⟨out, result, e3, v3, hres, scaled⟩ :=
    scaleSub_compiled code ids d hcode v2 ((hv.mono e1).mono e2) ((hp.mono e1).mono e2) hcoef
  refine ⟨out, result, e1.trans (e2.trans e3), v3, hres, ?_⟩
  let r0 := initialRegisters [Value.pointer vp, .pointer dp]
  let r1 := loadRegisters r0 2 3 15 (.pair cp q1)
  let r2 := loadRegisters r1 4 5 15 (.pair pp q2)
  let r3 := loadRegisters r2 6 7 15 (.pair pvp zp)
  have reads : RegisterPairReads.Reads h r0 [(1, 2, 3), (3, 4, 5), (5, 6, 7)] r3 := by
    refine .cons (ptr := dp) (by simp [r0, initialRegisters]) c1 ?_
    refine .cons (ptr := q1) (by simp [loadRegisters, decoded]) c2 ?_
    refine .cons (ptr := q2) (by simp [loadRegisters, decoded]) c3 ?_
    exact .nil _
  let r4 := bindResults r3 [8] [Value.pointer dotp]
  let r5 := bindResults r4 [9] [Value.pointer coefp]
  let r6 := bindResults r5 [10] [Value.pointer result]
  have last : Within code out r6 (.ret [.register 10]) [.pointer result] out 3 := by
    simpa [r6, bindResults, values, Atom.eval] using Within.ret code out r6 [.register 10]
  have scaleArgs : values r5 [.register 0, .register 4, .register 9] =
      [.pointer vp, .pointer pp, .pointer coefp] := by
    simp [r5, r4, r3, r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters,
      values, Atom.eval]
  have scaleCall := Within.call (procedure := ids.scaleSub)
    (arguments := [.register 0, .register 4, .register 9]) (results := [10]) (regs := r5)
    (by simpa only [scaleArgs] using scaled) last
  have divArgs : values r4 [.register 8, .register 6] = [.pointer dotp, .pointer pvp] := by
    simp [r4, r3, bindResults, loadRegisters, decoded, values, Atom.eval]
  have divCall := Within.call (procedure := ids.divide)
    (arguments := [.register 8, .register 6]) (results := [9]) (regs := r4)
    (by simpa only [divArgs] using divided) scaleCall
  have dotArgs : values r3 [.register 2, .register 0, .register 7] =
      [.pointer cp, .pointer vp, .pointer zp] := by
    simp [r3, r2, r1, r0, loadRegisters, decoded, initialRegisters, values, Atom.eval]
  have dotCall := Within.call (procedure := ids.row.self)
    (arguments := [.register 2, .register 0, .register 7]) (results := [8]) (regs := r3)
    (by simpa only [dotArgs] using dotted) divCall
  have whole := reads.within dotCall
  rw [hcode.project]
  refine whole.mono ?_
  simp only [projectBudget, List.length_cons, List.length_nil]
  omega

end WeightedMIS.RegisterRationalProject
