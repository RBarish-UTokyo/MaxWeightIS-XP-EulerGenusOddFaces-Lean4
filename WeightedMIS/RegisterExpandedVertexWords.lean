module

public import WeightedMIS.RegisterExpandedScalars
public import WeightedMIS.ExpandedContext

/-!
# Vertex-width parameter words

Given a shape word of width `k` (later the significant part of the node
count), the procedure resizes the base, state count, block, one, two, start
and finish words from the working width to width `k`, builds the zero word of
width `k`, a dimension-shape list of `d` zero words, and the five-pair
arithmetic record expected by the expanded-graph generator.
-/

@[expose] public section

namespace WeightedMIS.RegisterExpandedParameters

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.ExpandedParameters

variable {p : ℕ}

/-- Arguments: shape word, base, states, block, one, two, start, finish,
dimension list. Results: arithmetic record, shape list, shape word, zero word,
start, finish, one. -/
def vertexBody (ids : Procedures p) : Command p :=
  .call ids.resize.resize [.register 1, .register 0] [1]
  (.call ids.resize.resize [.register 2, .register 0] [2]
  (.call ids.resize.resize [.register 3, .register 0] [3]
  (.call ids.resize.resize [.register 4, .register 0] [4]
  (.call ids.resize.resize [.register 5, .register 0] [5]
  (.call ids.resize.resize [.register 6, .register 0] [6]
  (.call ids.resize.resize [.register 7, .register 0] [7]
  (.call ids.zero [.register 0] [9]
  (.call ids.shapeMap [.register 8, .register 9] [11]
  (.allocate 10 (.pair (.register 5) (.register 9))
  (.allocate 10 (.pair (.register 4) (.register 10))
  (.allocate 10 (.pair (.register 3) (.register 10))
  (.allocate 10 (.pair (.register 2) (.register 10))
  (.allocate 10 (.pair (.register 1) (.register 10))
  (.ret [.register 10, .register 11, .register 0, .register 9, .register 6, .register 7,
    .register 4]))))))))))))))

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

theorem shapeMap_compiled (code : Code p) (ids : Procedures p)
    (hmap : code ids.shapeMap = RegisterListMap.body ids.shapeMap ids.constItem)
    (hconst : code ids.constItem = constItemBody)
    {h : Heap} (hh : Valid h) {dp zp : Ptr} {k : ℕ} {dims : List Ptr} {z : Bits k}
    (hd : ListAt h dp dims) (hz : BitsAt h zp z) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (List.replicate dims.length z) ∧
      Within code h (initialRegisters [.pointer dp, .pointer zp]) (code ids.shapeMap)
        [.pointer q] out (38 * dims.length + 13) := by
  have hl : ListRep (fun _ p (x : Ptr) => p = x) h dp dims :=
    ⟨dims, hd, List.forall₂_same.mpr (fun _ _ => rfl)⟩
  obtain ⟨out, q, he, hv, hq, run⟩ := RegisterListMap.compiled_const code ids.shapeMap
    ids.constItem hmap (fun _ p (x : Ptr) => p = x) (fun h p (z : Bits k) => BitsAt h p z)
    (fun h p (y : Bits k) => BitsAt h p y) (fun _ _ _ hx => hx) (fun he _ _ hx => hx.mono he)
    (fun he _ _ hx => hx.mono he) (fun _ hy => hy.allocated) (fun data _ => data) 3 hh hl hz
    (fun {h'} _ {xp} _ _ _ hd' => by
      refine ⟨h', zp, .refl h', ‹Valid h'›, hd', ?_⟩
      rw [hconst]
      unfold constItemBody
      simpa [values, Atom.eval, initialRegisters] using
        Within.ret code h' (initialRegisters [.pointer xp, .pointer zp]) [.register 1])
  refine ⟨out, q, he, hv, ?_, run.mono (by omega)⟩
  rwa [List.map_const'] at hq

def vertexBudget (k G d : ℕ) : ℕ := 7 * (RegisterResize.resizeBudget k G + 5) + 24 * k +
  38 * d + 100

/-- The record of resized arithmetic words. -/
def resizedArithmetic {G : ℕ} (k : ℕ) (base states block one two : Bits G) : ArithmeticWords k :=
  ⟨Bits.resizeTo k base, Bits.resizeTo k states, Bits.resizeTo k block, Bits.resizeTo k one,
    Bits.resizeTo k two⟩

theorem vertex_compiled (code : Code p) (ids : Procedures p) (hc : ids.ScalarMatches code)
    (hmap : code ids.shapeMap = RegisterListMap.body ids.shapeMap ids.constItem)
    (hconst : code ids.constItem = constItemBody)
    (hbody : code ids.vertex = vertexBody ids)
    {h : Heap} (hh : Valid h) {vp bp sp blp op twp stp fip dp : Ptr} {k G : ℕ}
    {shape : Bits k} {base states block one two start finish : Bits G} {dims : List Ptr}
    (hvs : BitsAt h vp shape) (hb : BitsAt h bp base) (hs : BitsAt h sp states)
    (hbl : BitsAt h blp block) (ho : BitsAt h op one) (htw : BitsAt h twp two)
    (hst : BitsAt h stp start) (hfi : BitsAt h fip finish) (hd : ListAt h dp dims) :
    ∃ out ap shp zp sk fk ok, Extends h out ∧ Valid out ∧
      ArithmeticAt out ap (resizedArithmetic k base states block one two) ∧
      WordsAt out shp (List.replicate dims.length (Bits.zero k)) ∧
      BitsAt out vp shape ∧ BitsAt out zp (Bits.zero k) ∧
      BitsAt out sk (Bits.resizeTo k start) ∧ BitsAt out fk (Bits.resizeTo k finish) ∧
      BitsAt out ok (Bits.resizeTo k one) ∧
      Within code h (initialRegisters [.pointer vp, .pointer bp, .pointer sp, .pointer blp,
          .pointer op, .pointer twp, .pointer stp, .pointer fip, .pointer dp])
        (code ids.vertex)
        [.pointer ap, .pointer shp, .pointer vp, .pointer zp, .pointer sk, .pointer fk,
          .pointer ok] out (vertexBudget k G dims.length) := by
  obtain ⟨-, -, -, -, -, -, -, -, hzero, -, -, -, -, -, -, -, hres⟩ := hc
  have resize := fun {h : Heap} (hv : Valid h) {xp sp : Ptr} {x : Bits G} {s : Bits k}
    (hx : BitsAt h xp x) (hs : BitsAt h sp s) =>
    RegisterResize.resize_compiled code ids.resize hres hv hx hs
  obtain ⟨h1, t1, e1, v1, ht1, run1⟩ := resize hh hb hvs
  obtain ⟨h2, t2, e2, v2, ht2, run2⟩ := resize v1 (hs.mono e1) (hvs.mono e1)
  have e02 := e1.trans e2
  obtain ⟨h3, t3, e3, v3, ht3, run3⟩ := resize v2 (hbl.mono e02) (hvs.mono e02)
  have e03 := e02.trans e3
  obtain ⟨h4, t4, e4, v4, ht4, run4⟩ := resize v3 (ho.mono e03) (hvs.mono e03)
  have e04 := e03.trans e4
  obtain ⟨h5, t5, e5, v5, ht5, run5⟩ := resize v4 (htw.mono e04) (hvs.mono e04)
  have e05 := e04.trans e5
  obtain ⟨h6, t6, e6, v6, ht6, run6⟩ := resize v5 (hst.mono e05) (hvs.mono e05)
  have e06 := e05.trans e6
  obtain ⟨h7, t7, e7, v7, ht7, run7⟩ := resize v6 (hfi.mono e06) (hvs.mono e06)
  have e07 := e06.trans e7
  obtain ⟨h8, z, e8, v8, hz, -, run8⟩ := RegisterZero.compiled code ids.zero hzero v7
    (hvs.mono e07)
  have e08 := e07.trans e8
  obtain ⟨h9, sh, e9, v9, hsh, run9⟩ := shapeMap_compiled code ids hmap hconst v8
    (hd.mono e08) hz
  have e19 := ((e2.trans e3).trans (e4.trans e5)).trans ((e6.trans e7).trans (e8.trans e9))
  have e29 := (e3.trans (e4.trans e5)).trans ((e6.trans e7).trans (e8.trans e9))
  have e39 := (e4.trans e5).trans ((e6.trans e7).trans (e8.trans e9))
  have e49 := e5.trans ((e6.trans e7).trans (e8.trans e9))
  have e59 := (e6.trans e7).trans (e8.trans e9)
  have e69 := e7.trans (e8.trans e9)
  have e79 := e8.trans e9
  have a1 := ht1.mono e19
  have a2 := ht2.mono e29
  have a3 := ht3.mono e39
  have a4 := ht4.mono e49
  have a5 := ht5.mono e59
  have a6 := ht6.mono e69
  have a7 := ht7.mono e79
  have az := hz.mono e9
  obtain ⟨g1e, g1v, g1c⟩ := allocate_pair v9 a5.allocated az.allocated
  let g1 := h9 ++ [Cell.pair t5 z]
  obtain ⟨g2e, g2v, g2c⟩ := allocate_pair g1v (a4.mono g1e).allocated
    (show h9.length < g1.length by simp [g1])
  let g2 := g1 ++ [Cell.pair t4 h9.length]
  obtain ⟨g3e, g3v, g3c⟩ := allocate_pair g2v ((a3.mono g1e).mono g2e).allocated
    (show g1.length < g2.length by simp [g2])
  let g3 := g2 ++ [Cell.pair t3 g1.length]
  obtain ⟨g4e, g4v, g4c⟩ := allocate_pair g3v (((a2.mono g1e).mono g2e).mono g3e).allocated
    (show g2.length < g3.length by simp [g3])
  let g4 := g3 ++ [Cell.pair t2 g2.length]
  obtain ⟨g5e, g5v, g5c⟩ := allocate_pair g4v ((((a1.mono g1e).mono g2e).mono g3e).mono g4e).allocated
    (show g3.length < g4.length by simp [g4])
  let g5 := g4 ++ [Cell.pair t1 g3.length]
  have eg : Extends h9 g5 := g1e.trans (g2e.trans (g3e.trans (g4e.trans g5e)))
  have hzz : BitsAt g5 z (Bits.zero k) := az.mono eg
  refine ⟨g5, g4.length, sh, z, t6, t7, t4, e1.trans (e19.trans eg), g5v, ?_, hsh.mono eg,
    (hvs.mono e08).mono (e9.trans eg), hzz, a6.mono eg, a7.mono eg, a4.mono eg, ?_⟩
  · refine ⟨t1, g3.length, t2, g2.length, t3, g1.length, t4, h9.length, t5, z, g5c,
      g5e.lookup g4c, (g4e.trans g5e).lookup g3c, (g3e.trans (g4e.trans g5e)).lookup g2c,
      (g2e.trans (g3e.trans (g4e.trans g5e))).lookup g1c, a1.mono eg, a2.mono eg, a3.mono eg, a4.mono eg, a5.mono eg, hzz⟩
  let r0 := initialRegisters [Value.pointer vp, .pointer bp, .pointer sp, .pointer blp,
    .pointer op, .pointer twp, .pointer stp, .pointer fip, .pointer dp]
  let r1 := bindResults r0 [1] [Value.pointer t1]
  let r2 := bindResults r1 [2] [Value.pointer t2]
  let r3 := bindResults r2 [3] [Value.pointer t3]
  let r4 := bindResults r3 [4] [Value.pointer t4]
  let r5 := bindResults r4 [5] [Value.pointer t5]
  let r6 := bindResults r5 [6] [Value.pointer t6]
  let r7 := bindResults r6 [7] [Value.pointer t7]
  let r8 := bindResults r7 [9] [Value.pointer z]
  let r9 := bindResults r8 [11] [Value.pointer sh]
  let r10 := Function.update r9 10 (Value.pointer h9.length)
  let r11 := Function.update r10 10 (Value.pointer g1.length)
  let r12 := Function.update r11 10 (Value.pointer g2.length)
  let r13 := Function.update r12 10 (Value.pointer g3.length)
  let r14 := Function.update r13 10 (Value.pointer g4.length)
  have last : Within code g5 r14 (.ret [.register 10, .register 11, .register 0, .register 9,
      .register 6, .register 7, .register 4])
      [.pointer g4.length, .pointer sh, .pointer vp, .pointer z, .pointer t6, .pointer t7,
        .pointer t4] g5 15 := by
    simpa [r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, r0, values, Atom.eval,
      bindResults, initialRegisters] using
      Within.ret code g5 r14 [.register 10, .register 11, .register 0, .register 9,
        .register 6, .register 7, .register 4]
  have l5 := Within.allocate (regs := r13) (dst := 10) (h := g4)
    (expr := .pair (.register 1) (.register 10)) (c := .pair t1 g3.length)
    (by simp [r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, bindResults,
      CellExpr.eval, Atom.eval, Value.asPointer]) last
  have l4 := Within.allocate (regs := r12) (dst := 10) (h := g3)
    (expr := .pair (.register 2) (.register 10)) (c := .pair t2 g2.length)
    (by simp [r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, bindResults,
      CellExpr.eval, Atom.eval, Value.asPointer]) l5
  have l3 := Within.allocate (regs := r11) (dst := 10) (h := g2)
    (expr := .pair (.register 3) (.register 10)) (c := .pair t3 g1.length)
    (by simp [r11, r10, r9, r8, r7, r6, r5, r4, r3, bindResults,
      CellExpr.eval, Atom.eval, Value.asPointer]) l4
  have l2 := Within.allocate (regs := r10) (dst := 10) (h := g1)
    (expr := .pair (.register 4) (.register 10)) (c := .pair t4 h9.length)
    (by simp [r10, r9, r8, r7, r6, r5, r4, bindResults,
      CellExpr.eval, Atom.eval, Value.asPointer]) l3
  have l1 := Within.allocate (regs := r9) (dst := 10) (h := h9)
    (expr := .pair (.register 5) (.register 9)) (c := .pair t5 z)
    (by simp [r9, r8, r7, r6, r5, bindResults,
      CellExpr.eval, Atom.eval, Value.asPointer]) l2
  have a9 : values r8 [.register 8, .register 9] = [.pointer dp, .pointer z] := by
    simp [r8, r7, r6, r5, r4, r3, r2, r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c9 := Within.call (procedure := ids.shapeMap) (regs := r8)
    (arguments := [.register 8, .register 9]) (results := [11])
    (by simpa only [a9] using run9) l1
  have a8 : values r7 [.register 0] = [.pointer vp] := by
    simp [r7, r6, r5, r4, r3, r2, r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c8 := Within.call (procedure := ids.zero) (regs := r7)
    (arguments := [.register 0]) (results := [9])
    (by simpa only [a8] using run8) c9
  have a7 : values r6 [.register 7, .register 0] = [.pointer fip, .pointer vp] := by
    simp [r6, r5, r4, r3, r2, r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c7 := Within.call (procedure := ids.resize.resize) (regs := r6)
    (arguments := [.register 7, .register 0]) (results := [7])
    (by simpa only [a7] using run7) c8
  have a6 : values r5 [.register 6, .register 0] = [.pointer stp, .pointer vp] := by
    simp [r5, r4, r3, r2, r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c6 := Within.call (procedure := ids.resize.resize) (regs := r5)
    (arguments := [.register 6, .register 0]) (results := [6])
    (by simpa only [a6] using run6) c7
  have a5 : values r4 [.register 5, .register 0] = [.pointer twp, .pointer vp] := by
    simp [r4, r3, r2, r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c5 := Within.call (procedure := ids.resize.resize) (regs := r4)
    (arguments := [.register 5, .register 0]) (results := [5])
    (by simpa only [a5] using run5) c6
  have a4 : values r3 [.register 4, .register 0] = [.pointer op, .pointer vp] := by
    simp [r3, r2, r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c4 := Within.call (procedure := ids.resize.resize) (regs := r3)
    (arguments := [.register 4, .register 0]) (results := [4])
    (by simpa only [a4] using run4) c5
  have a3 : values r2 [.register 3, .register 0] = [.pointer blp, .pointer vp] := by
    simp [r2, r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c3 := Within.call (procedure := ids.resize.resize) (regs := r2)
    (arguments := [.register 3, .register 0]) (results := [3])
    (by simpa only [a3] using run3) c4
  have a2 : values r1 [.register 2, .register 0] = [.pointer sp, .pointer vp] := by
    simp [r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c2 := Within.call (procedure := ids.resize.resize) (regs := r1)
    (arguments := [.register 2, .register 0]) (results := [2])
    (by simpa only [a2] using run2) c3
  have a1' : values r0 [.register 1, .register 0] = [.pointer bp, .pointer vp] := by
    simp [r0, values, Atom.eval, initialRegisters]
  have c1 := Within.call (procedure := ids.resize.resize) (regs := r0)
    (arguments := [.register 1, .register 0]) (results := [1])
    (by simpa only [a1'] using run1) c2
  rw [hbody]
  exact c1.mono (by simp only [vertexBudget, CellExpr.args, List.length_cons, List.length_nil]; omega)

end WeightedMIS.RegisterExpandedParameters
