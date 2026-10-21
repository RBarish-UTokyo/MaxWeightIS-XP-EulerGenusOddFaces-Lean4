module

public import WeightedMIS.RegisterResize
public import WeightedMIS.CompiledTemplatePrimitives

/-!
# Resizing the state keys of stored signed columns

A stored column (`CompiledTemplates.ColumnAt`) refers to signed stubs, each a
sign cell pointing to its row record of two state-key words. The fixed
procedures below copy a column, allocating a fresh sign cell and row record
for every stub whose two keys are resized to the width of a supplied shape
word (`RegisterResize.resize_compiled`). The zero column is returned
unchanged. The result represents the same logical column for the resized key
function; a list of columns is processed by the generic list map.
-/

@[expose] public section

namespace WeightedMIS.RegisterColumnResize

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.Walks WeightedMIS.CompiledTemplates

variable {p : ℕ}

/-- One allocation of a cell whose references are already allocated. -/
theorem allocate_cell {h : Heap} (hh : Valid h) (c : Cell)
    (hc : ∀ q ∈ c.references, q < h.length) :
    Extends h (h ++ [c]) ∧ Valid (h ++ [c]) ∧ (h ++ [c])[h.length]? = some c := by
  have safe := safe_allocate h hh c hc
  exact ⟨safe.1, safe.2.1, by simp⟩

/-- The key function whose words are resized to width `k`. -/
def resizeKey {Row : Type*} {n : ℕ} (k : ℕ) (key : State Row → Bits n) : State Row → Bits k :=
  fun v => Bits.resizeTo k (key v)

theorem ColumnAt.allocated {Row : Type*} {n : ℕ} {key : State Row → Bits n} {h : Heap}
    {ptr : Ptr} {c : Column Row} (hc : ColumnAt key h ptr c) : ptr < h.length := by
  cases hc with
  | zero cell => exact (List.getElem?_eq_some_iff.mp cell).1
  | one cell _ => exact (List.getElem?_eq_some_iff.mp cell).1
  | two cell _ _ => exact (List.getElem?_eq_some_iff.mp cell).1

theorem StubAt.allocated {Row : Type*} {n : ℕ} {key : State Row → Bits n} {h : Heap}
    {ptr : Ptr} {s : Stub Row} (hs : StubAt key h ptr s) : ptr < h.length := by
  obtain ⟨_, _, _, hc, _⟩ := hs
  exact (List.getElem?_eq_some_iff.mp hc).1

/-- Arguments: stub, shape word. The sign cell and the row record are copied
with both state keys resized to the shape width. -/
def stubBody (resize : Fin p) : Command p :=
  .load (.register 0) 2 15 3 { CompiledTrie.failCases with
    bit := .load (.register 2) 4 5 15 { CompiledTrie.failCases with
      pair := .call resize [.register 4, .register 1] [6]
        (.call resize [.register 5, .register 1] [7]
          (.allocate 8 (.pair (.register 6) (.register 7))
            (.allocate 9 (.bit (.register 3) (.register 8)) (.ret [.register 9])))) } }

/-- Arguments: column, shape word. -/
def columnBody (stub : Fin p) : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    nil := .ret [.register 0]
    bucket := .call stub [.register 2, .register 1] [4]
      (.allocate 5 (.bucket (.register 4)) (.ret [.register 5]))
    pair := .call stub [.register 2, .register 1] [4]
      (.call stub [.register 3, .register 1] [5]
        (.allocate 6 (.pair (.register 4) (.register 5)) (.ret [.register 6]))) }

structure Procedures (p : ℕ) where
  resize : RegisterResize.Procedures p
  stub : Fin p
  column : Fin p
  columns : Fin p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  ids.resize.Matches code ∧ code ids.stub = stubBody ids.resize.resize ∧
    code ids.column = columnBody ids.stub ∧
    code ids.columns = RegisterListMap.body ids.columns ids.column

def stubBudget (k n : ℕ) : ℕ := 2 * RegisterResize.resizeBudget k n + 60

def columnBudget (k n : ℕ) : ℕ := 2 * stubBudget k n + 40

def columnsBudget (k n length : ℕ) : ℕ := (columnBudget k n + 35) * length + 13

theorem stub_compiled (code : Code p) (ids : Procedures p) (hc : ids.Matches code)
    {Row : Type*} {n k : ℕ} {key : State Row → Bits n}
    {h : Heap} (hh : Valid h) {sp wp : Ptr} {s : Stub Row} {w : Bits k}
    (hs : StubAt key h sp s) (hw : BitsAt h wp w) :
    ∃ out q, Extends h out ∧ Valid out ∧ StubAt (resizeKey k key) out q s ∧
      Within code h (initialRegisters [.pointer sp, .pointer wp]) (code ids.stub)
        [.pointer q] out (stubBudget k n) := by
  obtain ⟨hr, hstub, -, -⟩ := hc
  obtain ⟨row, minus, plus, hcell, hrow, hm, hp⟩ := hs
  obtain ⟨h1, q1, e1, v1, hq1, run1⟩ := RegisterResize.resize_compiled code ids.resize hr hh hm hw
  obtain ⟨h2, q2, e2, v2, hq2, run2⟩ :=
    RegisterResize.resize_compiled code ids.resize hr v1 (hp.mono e1) (hw.mono e1)
  have hq1' := hq1.mono e2
  have a3 := allocate_cell v2 (.pair q1 q2) (by
    intro x hx
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hq1'.allocated
    · exact hq2.allocated)
  let h3 := h2 ++ [.pair q1 q2]
  have a4 := allocate_cell a3.2.1 (.bit s.2 h2.length) (by
    intro x hx
    simp only [Cell.references, List.mem_singleton] at hx
    subst x
    simp)
  let h4 := h3 ++ [.bit s.2 h2.length]
  have e34 : Extends h2 h4 := a3.1.trans a4.1
  refine ⟨h4, h3.length, ((e1.trans e2).trans e34), a4.2.1, ?_, ?_⟩
  · refine ⟨h2.length, q1, q2, a4.2.2, a4.1.lookup a3.2.2, hq1'.mono e34, hq2.mono e34⟩
  let regs := initialRegisters [Value.pointer sp, .pointer wp]
  let r1 := loadRegisters regs 2 15 3 (.bit s.2 row)
  let r2 := loadRegisters r1 4 5 15 (.pair minus plus)
  let r3 := bindResults r2 [6] [Value.pointer q1]
  let r4 := bindResults r3 [7] [Value.pointer q2]
  let r5 := Function.update r4 8 (Value.pointer h2.length)
  let r6 := Function.update r5 9 (Value.pointer h3.length)
  have last : Within code h4 r6 (.ret [.register 9]) [.pointer h3.length] h4 3 := by
    simpa [r6, values, Atom.eval] using Within.ret code h4 r6 [.register 9]
  have alloc2 := Within.allocate (regs := r5) (dst := 9) (expr := .bit (.register 3) (.register 8))
    (c := .bit s.2 h2.length) (h := h3)
    (by simp [r5, r4, r3, r2, r1, regs, bindResults, loadRegisters, decoded, CellExpr.eval,
      Atom.eval, Value.asFlag, Value.asPointer]) last
  have alloc1 := Within.allocate (regs := r4) (dst := 8) (expr := .pair (.register 6) (.register 7))
    (c := .pair q1 q2) (h := h2)
    (by simp [r4, r3, bindResults, CellExpr.eval, Atom.eval, Value.asPointer]) alloc2
  have a2 : values r3 [.register 5, .register 1] = [.pointer plus, .pointer wp] := by
    simp [r3, r2, r1, regs, values, Atom.eval, bindResults, loadRegisters, decoded,
      initialRegisters]
  have call2 := Within.call (procedure := ids.resize.resize) (regs := r3)
    (arguments := [.register 5, .register 1]) (results := [7])
    (by simpa only [a2] using run2) alloc1
  have a1 : values r2 [.register 4, .register 1] = [.pointer minus, .pointer wp] := by
    simp [r2, r1, regs, values, Atom.eval, loadRegisters, decoded, initialRegisters]
  have call1 := Within.call (procedure := ids.resize.resize) (regs := r2)
    (arguments := [.register 4, .register 1]) (results := [6])
    (by simpa only [a1] using run1) call2
  have load2 := Within.load (regs := r1) (address := .register 2) (first := 4) (second := 5)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .call ids.resize.resize [.register 4, .register 1] [6]
        (.call ids.resize.resize [.register 5, .register 1] [7]
          (.allocate 8 (.pair (.register 6) (.register 7))
            (.allocate 9 (.bit (.register 3) (.register 8)) (.ret [.register 9])))) })
    (by simp [r1, regs, loadRegisters, decoded, Atom.eval]) hrow call1
  have load1 := Within.load (regs := regs) (address := .register 0) (first := 2) (second := 15)
    (bit := 3) (branches := { CompiledTrie.failCases with
      bit := .load (.register 2) 4 5 15 { CompiledTrie.failCases with
        pair := .call ids.resize.resize [.register 4, .register 1] [6]
          (.call ids.resize.resize [.register 5, .register 1] [7]
            (.allocate 8 (.pair (.register 6) (.register 7))
              (.allocate 9 (.bit (.register 3) (.register 8)) (.ret [.register 9])))) } })
    (by simp [regs, initialRegisters, Atom.eval]) hcell load2
  rw [hstub]
  exact load1.mono (by simp [CellExpr.args, stubBudget]; omega)

theorem column_compiled (code : Code p) (ids : Procedures p) (hc : ids.Matches code)
    {Row : Type*} {n k : ℕ} {key : State Row → Bits n}
    {h : Heap} (hh : Valid h) {cp wp : Ptr} {c : Column Row} {w : Bits k}
    (hcol : ColumnAt key h cp c) (hw : BitsAt h wp w) :
    ∃ out q, Extends h out ∧ Valid out ∧ ColumnAt (resizeKey k key) out q c ∧
      Within code h (initialRegisters [.pointer cp, .pointer wp]) (code ids.column)
        [.pointer q] out (columnBudget k n) := by
  have hc' := hc
  obtain ⟨-, hstub, hcolumn, -⟩ := hc
  let regs := initialRegisters [Value.pointer cp, .pointer wp]
  let branches : Cases (Command p) := { CompiledTrie.failCases with
    nil := .ret [.register 0]
    bucket := .call ids.stub [.register 2, .register 1] [4]
      (.allocate 5 (.bucket (.register 4)) (.ret [.register 5]))
    pair := .call ids.stub [.register 2, .register 1] [4]
      (.call ids.stub [.register 3, .register 1] [5]
        (.allocate 6 (.pair (.register 4) (.register 5)) (.ret [.register 6]))) }
  rw [hcolumn]
  cases hcol with
  | zero cell =>
    refine ⟨h, cp, .refl h, hh, .zero cell, ?_⟩
    have last := Within.ret code h (loadRegisters regs 2 3 15 .nil) [.register 0]
    have load := Within.load (regs := regs) (address := .register 0) (first := 2) (second := 3)
      (bit := 15) (branches := branches) (by simp [regs, initialRegisters, Atom.eval]) cell
      (by simpa [branches, Cases.select, values, Atom.eval, regs, loadRegisters, decoded,
        initialRegisters] using last)
    exact load.mono (by simp [columnBudget])
  | @one sp s cell stub =>
    obtain ⟨h1, q1, e1, v1, hq1, run1⟩ := stub_compiled code ids hc' hh stub hw
    have a2 := allocate_cell v1 (.bucket q1) (by
      intro x hx
      simp only [Cell.references, List.mem_singleton] at hx
      subst x
      exact StubAt.allocated hq1)
    let h2 := h1 ++ [.bucket q1]
    refine ⟨h2, h1.length, e1.trans a2.1, a2.2.1, .one a2.2.2 (hq1.mono a2.1), ?_⟩
    let r1 := loadRegisters regs 2 3 15 (.bucket sp)
    let r2 := bindResults r1 [4] [Value.pointer q1]
    let r3 := Function.update r2 5 (Value.pointer h1.length)
    have last : Within code h2 r3 (.ret [.register 5]) [.pointer h1.length] h2 3 := by
      simpa [r3, values, Atom.eval] using Within.ret code h2 r3 [.register 5]
    have alloc := Within.allocate (regs := r2) (dst := 5) (expr := .bucket (.register 4))
      (c := .bucket q1) (h := h1)
      (by simp [r2, bindResults, CellExpr.eval, Atom.eval, Value.asPointer]) last
    have a1 : values r1 [.register 2, .register 1] = [.pointer sp, .pointer wp] := by
      simp [r1, regs, values, Atom.eval, loadRegisters, decoded, initialRegisters]
    have call := Within.call (procedure := ids.stub) (regs := r1)
      (arguments := [.register 2, .register 1]) (results := [4])
      (by simpa only [a1] using run1) alloc
    have load := Within.load (regs := regs) (address := .register 0) (first := 2) (second := 3)
      (bit := 15) (branches := branches) (by simp [regs, initialRegisters, Atom.eval]) cell
      (by simpa [branches, Cases.select] using call)
    exact load.mono (by simp [CellExpr.args, columnBudget] ; omega)
  | @two sp tp s t cell first second =>
    obtain ⟨h1, q1, e1, v1, hq1, run1⟩ := stub_compiled code ids hc' hh first hw
    obtain ⟨h2, q2, e2, v2, hq2, run2⟩ :=
      stub_compiled code ids hc' v1 (second.mono e1) (hw.mono e1)
    have hq1' := hq1.mono e2
    have a3 := allocate_cell v2 (.pair q1 q2) (by
      intro x hx
      simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact StubAt.allocated hq1'
      · exact StubAt.allocated hq2)
    let h3 := h2 ++ [.pair q1 q2]
    refine ⟨h3, h2.length, (e1.trans e2).trans a3.1, a3.2.1,
      .two a3.2.2 (hq1'.mono a3.1) (hq2.mono a3.1), ?_⟩
    let r1 := loadRegisters regs 2 3 15 (.pair sp tp)
    let r2 := bindResults r1 [4] [Value.pointer q1]
    let r3 := bindResults r2 [5] [Value.pointer q2]
    let r4 := Function.update r3 6 (Value.pointer h2.length)
    have last : Within code h3 r4 (.ret [.register 6]) [.pointer h2.length] h3 3 := by
      simpa [r4, values, Atom.eval] using Within.ret code h3 r4 [.register 6]
    have alloc := Within.allocate (regs := r3) (dst := 6)
      (expr := .pair (.register 4) (.register 5)) (c := .pair q1 q2) (h := h2)
      (by simp [r3, r2, bindResults, CellExpr.eval, Atom.eval, Value.asPointer]) last
    have a2 : values r2 [.register 3, .register 1] = [.pointer tp, .pointer wp] := by
      simp [r2, r1, regs, values, Atom.eval, bindResults, loadRegisters, decoded,
        initialRegisters]
    have call2 := Within.call (procedure := ids.stub) (regs := r2)
      (arguments := [.register 3, .register 1]) (results := [5])
      (by simpa only [a2] using run2) alloc
    have a1 : values r1 [.register 2, .register 1] = [.pointer sp, .pointer wp] := by
      simp [r1, regs, values, Atom.eval, loadRegisters, decoded, initialRegisters]
    have call1 := Within.call (procedure := ids.stub) (regs := r1)
      (arguments := [.register 2, .register 1]) (results := [4])
      (by simpa only [a1] using run1) call2
    have load := Within.load (regs := regs) (address := .register 0) (first := 2) (second := 3)
      (bit := 15) (branches := branches) (by simp [regs, initialRegisters, Atom.eval]) cell
      (by simpa [branches, Cases.select] using call1)
    exact load.mono (by simp [CellExpr.args, columnBudget] ; omega)

/-- Resize the state keys of every column of a stored list. -/
theorem columns_compiled (code : Code p) (ids : Procedures p) (hc : ids.Matches code)
    {Row : Type*} {n k : ℕ} {key : State Row → Bits n}
    {h : Heap} (hh : Valid h) {lp wp : Ptr} {cs : List (Column Row)} {w : Bits k}
    (hl : ListRep (ColumnAt key) h lp cs) (hw : BitsAt h wp w) :
    ∃ out q, Extends h out ∧ Valid out ∧ ListRep (ColumnAt (resizeKey k key)) out q cs ∧
      Within code h (initialRegisters [.pointer lp, .pointer wp]) (code ids.columns)
        [.pointer q] out (columnsBudget k n cs.length) := by
  have hc' := hc
  obtain ⟨-, -, -, hcolumns⟩ := hc
  obtain ⟨out, q, he, hv, hq, run⟩ := RegisterListMap.compiled_const code ids.columns ids.column
    hcolumns (ColumnAt key) (fun h p (s : Bits k) => BitsAt h p s) (ColumnAt (resizeKey k key))
    (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he)
    (fun _ hy => ColumnAt.allocated hy) (fun _ c => c) (columnBudget k n) hh hl hw
    (fun hv _ _ _ hx hs => column_compiled code ids hc' hv hx hs)
  exact ⟨out, q, he, hv, by simpa using hq, run⟩

/-- The resized keys keep the state numbers when they fit in the new width. -/
theorem resizeKey_value {Row : Type*} {n k : ℕ} {key : State Row → Bits n} (v : State Row)
    (hv : (key v).value < 2 ^ k) : (resizeKey k key v).value = (key v).value :=
  Bits.resizeTo_value_of_lt _ hv

end WeightedMIS.RegisterColumnResize
