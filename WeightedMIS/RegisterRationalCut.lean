module

public import WeightedMIS.RegisterRationalProject
public import WeightedMIS.RegisterListFind
public import WeightedMIS.RegisterListMap

/-!
# Compiled processing of one rational constraint row

`nonzero` computes the dot product of the constraint row with a vector and
returns the negation of the compiled binary zero test. `cut` searches the
stored vectors for the first such pivot with the list search combinator; if
none exists it returns the input list unchanged. Otherwise it recomputes the
pivot value, allocates the projection data record `(c, (p, (pv, zero)))`, and
maps the compiled projection over all stored vectors, including the pivot.
The output is exactly `RationalWordRows.cutW`.
-/

@[expose] public section

namespace WeightedMIS.RegisterRationalCut

open PointerMemory RegisterMachine EfficientSearch EfficientSearch.Pointer StoredRational
open RegisterRationalRow (RowAt)

variable {p N : ℕ}

/-- A linked list of stored rational rows. -/
def RowsAt (h : Heap) (ptr : Ptr) (rows : List (List (BinaryRational.Word N))) : Prop :=
  ListRep (fun heap q (row : List (BinaryRational.Word N)) => RowAt heap q row) h ptr rows

theorem RowsAt.mono {h out : Heap} (ext : Extends h out) {ptr : Ptr}
    {rows : List (List (BinaryRational.Word N))} (hr : RowsAt h ptr rows) : RowsAt out ptr rows :=
  ListRep.mono ext (fun _ _ hq => RowAt.mono ext hq) hr

/-- The search data record `(c, zero)`. -/
def SearchAt (h : Heap) (ptr : Ptr)
    (d : List (BinaryRational.Word N) × BinaryRational.Word N) : Prop :=
  ∃ cp zp, h[ptr]? = some (.pair cp zp) ∧ RowAt h cp d.1 ∧ At h zp d.2

theorem SearchAt.mono {h out : Heap} (ext : Extends h out) {ptr : Ptr}
    {d : List (BinaryRational.Word N) × BinaryRational.Word N} (hd : SearchAt h ptr d) :
    SearchAt out ptr d := by
  obtain ⟨cp, zp, cell, hc, hz⟩ := hd
  exact ⟨cp, zp, ext.lookup cell, hc.mono ext, hz.mono ext⟩

/-- Arguments 0=v, 1=search record; result is the flag `dot(c, v) ≠ 0`. -/
def nonzeroBody (dot zeroTest : Fin p) : Command p :=
  RegisterPairReads.readPairs [(1, 2, 3)]
    (.call dot [.register 2, .register 0, .register 3] [4]
      (.call zeroTest [.register 4] [5]
        (.branch (.register 5) (.ret [.flag false]) (.ret [.flag true]))))

/-- Arguments 0=c, 1=zero, 2=vectors; result is the processed vector list. -/
def pivotBranch (dot map : Fin p) : Command p :=
  .call dot [.register 0, .register 5, .register 1] [6]
    (.allocate 7 (.pair (.register 6) (.register 1))
      (.allocate 8 (.pair (.register 5) (.register 7))
        (.allocate 9 (.pair (.register 0) (.register 8))
          (.call map [.register 2, .register 9] [10] (.ret [.register 10])))))

/-- Arguments 0=c, 1=zero, 2=vectors; result is the processed vector list. -/
def cutBody (dot find map : Fin p) : Command p :=
  .allocate 3 (.pair (.register 0) (.register 1))
    (.call find [.register 2, .register 3] [4, 5]
      (.branch (.register 4) (pivotBranch dot map) (.ret [.register 2])))

structure Procedures (p : ℕ) where
  proj : RegisterRationalProject.Procedures p
  zeroTest : Fin p
  nonzero : Fin p
  find : Fin p
  map : Fin p
  cut : Fin p

structure Procedures.Matches (ids : Procedures p) (code : Code p)
    (d : RegisterRationalProducts.Procedures p) : Prop where
  proj : ids.proj.Matches code d
  zeroTest : code ids.zeroTest =
    RegisterRationalZero.body ids.proj.row.read d.division.zero d.division.cmp
  nonzero : code ids.nonzero = nonzeroBody ids.proj.row.self ids.zeroTest
  find : code ids.find = RegisterListFind.body ids.find ids.nonzero
  map : code ids.map = RegisterListMap.body ids.map ids.proj.project
  cut : code ids.cut = cutBody ids.proj.row.self ids.find ids.map

def nonzeroBudget (N m : ℕ) : ℕ := RegisterRationalRow.budget N m + 60 * N + 110

theorem nonzero_compiled (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d)
    {h : Heap} (hh : Valid h) {vp sp : Ptr}
    {v c : List (BinaryRational.Word N)} {zero : BinaryRational.Word N}
    (hv : RowAt h vp v) (hs : SearchAt h sp (c, zero)) :
    ∃ out, Extends h out ∧ Valid out ∧
      Within code h (initialRegisters [.pointer vp, .pointer sp]) (code ids.nonzero)
        [.flag (RationalWordRows.nonzeroW zero c v)] out (nonzeroBudget N c.length) := by
  obtain ⟨cp, zp, cell, hc, hz⟩ := hs
  obtain ⟨mid, dotp, e1, v1, hdot, dotted⟩ :=
    RegisterRationalRow.compiled code ids.proj.row d hcode.proj.row hh hc hv hz
  have hdm := hcode.proj.row.arithmetic
  obtain ⟨out, e2, v2, tested⟩ := RegisterRationalZero.compiled code ids.proj.row.read
    d.division.zero d.division.cmp hcode.proj.row.read hdm.1.1 hdm.1.2.1 v1 hdot
  refine ⟨out, e1.trans e2, v2, ?_⟩
  let r0 := initialRegisters [Value.pointer vp, .pointer sp]
  let r1 := loadRegisters r0 2 3 15 (.pair cp zp)
  have reads : RegisterPairReads.Reads h r0 [(1, 2, 3)] r1 :=
    .cons (ptr := sp) (by simp [r0, initialRegisters]) cell (.nil _)
  let r2 := bindResults r1 [4] [Value.pointer dotp]
  let b := (BinaryRational.isZero (RegisterRationalRow.dotWords zero c v)).1
  let r3 := bindResults r2 [5] [Value.flag b]
  have hn : RationalWordRows.nonzeroW zero c v = !b := rfl
  have tail : Within code out r3 (.branch (.register 5) (.ret [.flag false]) (.ret [.flag true]))
      [.flag (RationalWordRows.nonzeroW zero c v)] out (3 + 3) := by
    have hr5 : (Atom.register 5).eval r3 = .flag b := by simp [r3, bindResults, Atom.eval]
    rw [hn]
    cases hb : b
    · exact Within.branch (b := false) (by rw [hr5, hb])
        (by simpa [values, Atom.eval] using Within.ret code out r3 [.flag true])
    · exact Within.branch (b := true) (by rw [hr5, hb])
        (by simpa [values, Atom.eval] using Within.ret code out r3 [.flag false])
  have zArgs : values r2 [.register 4] = [.pointer dotp] := by
    simp [r2, bindResults, values, Atom.eval]
  have zCall := Within.call (procedure := ids.zeroTest) (arguments := [.register 4])
    (results := [5]) (regs := r2) (by simpa only [zArgs, hcode.zeroTest] using tested) tail
  have dArgs : values r1 [.register 2, .register 0, .register 3] =
      [.pointer cp, .pointer vp, .pointer zp] := by
    simp [r1, r0, loadRegisters, decoded, initialRegisters, values, Atom.eval]
  have dCall := Within.call (procedure := ids.proj.row.self)
    (arguments := [.register 2, .register 0, .register 3]) (results := [4]) (regs := r1)
    (by simpa only [dArgs] using dotted) zCall
  have whole := reads.within dCall
  rw [hcode.nonzero]
  refine whole.mono ?_
  simp only [nonzeroBudget, List.length_cons, List.length_nil]
  omega

theorem allocate_pair {h : Heap} (hh : Valid h) {a b : Ptr} (ha : a < h.length)
    (hb : b < h.length) :
    Extends h (h ++ [.pair a b]) ∧ Valid (h ++ [.pair a b]) ∧
      (h ++ [.pair a b])[h.length]? = some (.pair a b) := by
  have safe := safe_allocate h hh (.pair a b) (by
    intro x hx
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb)
  exact ⟨safe.1, safe.2.1, by simp⟩

/-- Event bound of one cut on `k` stored vectors of length `m`. -/
def cutBudget (N m k : ℕ) : ℕ :=
  (nonzeroBudget N m + 30) * k + (RegisterRationalProject.projectBudget N m m + 35) * k +
    RegisterRationalRow.budget N m + 120

theorem cut_compiled (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d)
    {h : Heap} (hh : Valid h) {cp zp vsp : Ptr} {m : ℕ}
    {c : List (BinaryRational.Word N)} {zero : BinaryRational.Word N}
    {vs : List (List (BinaryRational.Word N))}
    (hc : RowAt h cp c) (hz : At h zp zero) (hvs : RowsAt h vsp vs)
    (hcl : c.length = m) (hvl : ∀ v ∈ vs, v.length = m) :
    ∃ out result, Extends h out ∧ Valid out ∧
      RowsAt out result (RationalWordRows.cutW zero c vs) ∧
      Within code h (initialRegisters [.pointer cp, .pointer zp, .pointer vsp])
        (code ids.cut) [.pointer result] out (cutBudget N m vs.length) := by
  -- allocate the search record
  let h1 := h ++ [.pair cp zp]
  have safe1 := safe_allocate h hh (.pair cp zp) (by
    intro x hx
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hc.allocated
    · exact hz.allocated)
  have e1 : Extends h h1 := safe1.1
  have v1 : Valid h1 := safe1.2.1
  have hs : SearchAt h1 h.length (c, zero) :=
    ⟨cp, zp, by simp [h1], hc.mono e1, hz.mono e1⟩
  obtain ⟨h2, q, e2, v2, hfound, hnone, searched⟩ := RegisterListFind.compiled_const code
    ids.find ids.nonzero hcode.find RowAt SearchAt
    (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext)
    (fun d v => RationalWordRows.nonzeroW d.2 d.1 v) (nonzeroBudget N m) v1 (hvs.mono e1) hs
    (fun {_} hv {_} {x} _ hx hd => by
      obtain ⟨out, e, vo, w⟩ := nonzero_compiled code ids d hcode hv hx hd
      exact ⟨out, e, vo, by simpa [hcl] using w⟩)
  let r0 := initialRegisters [Value.pointer cp, .pointer zp, .pointer vsp]
  let r1 := Function.update r0 3 (Value.pointer h.length)
  let found := (vs.find? (fun v => RationalWordRows.nonzeroW zero c v)).isSome
  let r2 := bindResults r1 [4, 5] [Value.flag found, .pointer q]
  have fArgs : values r1 [.register 2, .register 3] = [.pointer vsp, .pointer h.length] := by
    simp [r1, r0, initialRegisters, values, Atom.eval]
  have hsel : ∀ {rest : Command p} {outputs : List Value} {final : Heap} {b : ℕ},
      Within code h2 r2 rest outputs final b →
      Within code h r0 (.allocate 3 (.pair (.register 0) (.register 1))
        (.call ids.find [.register 2, .register 3] [4, 5] rest)) outputs final
        (8 + (5 + ((nonzeroBudget N m + 30) * vs.length + 15) + b)) := by
    intro rest outputs final b hrest
    have fCall := Within.call (procedure := ids.find) (arguments := [.register 2, .register 3])
      (results := [4, 5]) (regs := r1) (by simpa only [fArgs] using searched) hrest
    exact Within.allocate (h := h) (regs := r0) (dst := 3)
      (expr := .pair (.register 0) (.register 1))
      (by simp [CellExpr.eval, Atom.eval, r0, initialRegisters, Value.asPointer]) fCall
  rcases hfind : vs.find? (fun v => RationalWordRows.nonzeroW zero c v) with _ | piv
  · -- no pivot: return the input list
    have hcut : RationalWordRows.cutW zero c vs = vs := by
      unfold RationalWordRows.cutW; rw [hfind]
    refine ⟨h2, vsp, e1.trans e2, v2, by rw [hcut]; exact hvs.mono (e1.trans e2), ?_⟩
    have last : Within code h2 r2 (.ret [.register 2]) [.pointer vsp] h2 3 := by
      simpa [r2, r1, r0, bindResults, initialRegisters, values, Atom.eval] using
        Within.ret code h2 r2 [.register 2]
    have br := Within.branch (b := false) (test := .register 4) (regs := r2)
      (yes := pivotBranch ids.proj.row.self ids.map) (no := .ret [.register 2])
      (by simp [r2, bindResults, Atom.eval, found, hfind]) (by simpa using last)
    have whole := hsel br
    rw [hcode.cut]
    refine whole.mono ?_
    simp only [cutBudget]
    omega
  · -- pivot found
    have hpmem : piv ∈ vs := List.mem_of_find?_eq_some hfind
    have hpq : RowAt h2 q piv := hfound piv hfind
    have e12 := e1.trans e2
    obtain ⟨h3, pvp, e3, v3, hpv, dotted⟩ := RegisterRationalRow.compiled code ids.proj.row d
      hcode.proj.row v2 (hc.mono e12) hpq (hz.mono e12)
    have e13 := e12.trans e3
    obtain ⟨e4, v4, c4⟩ := allocate_pair v3 hpv.allocated (hz.mono e13).allocated
    let h4 := h3 ++ [.pair pvp zp]
    have hq3 : q < h3.length := (hpq.mono e3).allocated
    have hq4 : q < h4.length := lt_of_lt_of_le hq3 e4.length_le
    have h34 : h3.length < h4.length := by simp [h4]
    obtain ⟨e5, v5, c5⟩ := allocate_pair v4 hq4 h34
    let h5 := h4 ++ [.pair q h3.length]
    have hc3 : cp < h3.length := (hc.mono e13).allocated
    have hc5 : cp < h5.length := lt_of_lt_of_le hc3 (e4.trans e5).length_le
    have h45 : h4.length < h5.length := by simp [h5]
    obtain ⟨e6, v6, c6⟩ := allocate_pair v5 hc5 h45
    let h6 := h5 ++ [.pair cp h4.length]
    have e36 : Extends h3 h6 := e4.trans (e5.trans e6)
    have e46 : Extends h4 h6 := e5.trans e6
    have hdata : RegisterRationalProject.DataAt h6 h5.length
        (c, piv, RegisterRationalRow.dotWords zero c piv, zero) :=
      ⟨cp, h4.length, q, h3.length, pvp, zp, c6, e6.lookup c5, e46.lookup c4,
        (hc.mono e13).mono e36, (hpq.mono e3).mono e36, hpv.mono e36, (hz.mono e13).mono e36⟩
    have hvs6 : RowsAt h6 vsp vs := hvs.mono (e13.trans e36)
    obtain ⟨out, result, e7, v7, hres, mapped⟩ := RegisterListMap.compiled_const code ids.map
      ids.proj.project hcode.map RowAt RegisterRationalProject.DataAt RowAt
      (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext)
      (fun ext _ _ hx => hx.mono ext) (fun _ hx => hx.allocated)
      (fun d v => RationalWordRows.projectW d.2.2.2 d.1 d.2.1 d.2.2.1 v)
      (RegisterRationalProject.projectBudget N m m) v6 hvs6 hdata
      (fun {_} hv {_} {x} hxm hx hd => by
        obtain ⟨o, r, e, vo, hr, w⟩ :=
          RegisterRationalProject.project_compiled code ids.proj d hcode.proj hv hx hd
        exact ⟨o, r, e, vo, hr, by simpa [hcl, hvl x hxm] using w⟩)
    have hcut : RationalWordRows.cutW zero c vs =
        vs.map (RationalWordRows.projectW zero c piv (RationalWordRows.dotW zero c piv)) := by
      unfold RationalWordRows.cutW; rw [hfind]
    refine ⟨out, result, e13.trans (e36.trans e7), v7, by rw [hcut]; exact hres, ?_⟩
    let r3 := bindResults r2 [6] [Value.pointer pvp]
    let r4 := Function.update r3 7 (Value.pointer h3.length)
    let r5 := Function.update r4 8 (Value.pointer h4.length)
    let r6 := Function.update r5 9 (Value.pointer h5.length)
    let r7 := bindResults r6 [10] [Value.pointer result]
    have last : Within code out r7 (.ret [.register 10]) [.pointer result] out 3 := by
      simpa [r7, bindResults, values, Atom.eval] using Within.ret code out r7 [.register 10]
    have mArgs : values r6 [.register 2, .register 9] = [.pointer vsp, .pointer h5.length] := by
      simp [r6, r5, r4, r3, r2, r1, r0, bindResults, initialRegisters, values, Atom.eval]
    have mCall := Within.call (procedure := ids.map) (arguments := [.register 2, .register 9])
      (results := [10]) (regs := r6) (by simpa only [mArgs] using mapped) last
    have a9 := Within.allocate (h := h5) (regs := r5) (dst := 9)
      (expr := .pair (.register 0) (.register 8)) (c := .pair cp h4.length)
      (by simp [CellExpr.eval, Atom.eval, r5, r4, r3, r2, r1, r0, bindResults,
        initialRegisters, Value.asPointer]) mCall
    have a8 := Within.allocate (h := h4) (regs := r4) (dst := 8)
      (expr := .pair (.register 5) (.register 7)) (c := .pair q h3.length)
      (by simp [CellExpr.eval, Atom.eval, r4, r3, r2, bindResults, Value.asPointer]) a9
    have a7 := Within.allocate (h := h3) (regs := r3) (dst := 7)
      (expr := .pair (.register 6) (.register 1)) (c := .pair pvp zp)
      (by simp [CellExpr.eval, Atom.eval, r3, r2, r1, r0, bindResults, initialRegisters,
        Value.asPointer]) a8
    have dArgs : values r2 [.register 0, .register 5, .register 1] =
        [.pointer cp, .pointer q, .pointer zp] := by
      simp [r2, r1, r0, bindResults, initialRegisters, values, Atom.eval]
    have dCall := Within.call (procedure := ids.proj.row.self)
      (arguments := [.register 0, .register 5, .register 1]) (results := [6]) (regs := r2)
      (by simpa only [dArgs] using dotted) a7
    have br := Within.branch (b := true) (test := .register 4) (regs := r2)
      (yes := pivotBranch ids.proj.row.self ids.map) (no := .ret [.register 2])
      (by simp [r2, bindResults, Atom.eval, found, hfind]) (by simpa [pivotBranch] using dCall)
    have whole := hsel br
    rw [hcode.cut]
    refine whole.mono ?_
    simp only [cutBudget, CellExpr.args, List.length_cons, List.length_nil, hcl]
    omega

end WeightedMIS.RegisterRationalCut
