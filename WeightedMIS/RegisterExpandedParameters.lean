module

public import WeightedMIS.RegisterExpandedVertexWords
public import WeightedMIS.SparseSearchLabeled

/-!
# Exact parameter words of the expanded search graph

The fixed procedure receives the row-count word `r`, the list of cost words
(its length is the number `m` of original edges, which is also the box
radius), a list of length `d`, and the zero word of a working width `G`.
Under the single fit premise `fitBound r d w < 2^G` it returns, at exactly the
widths used by `SparseSearchGraph.Labeled.graph`:

* the arithmetic record `ExpandedParameters.arithmetic r d m`, which satisfies
  `ArithmeticRepresents` (with the `d = 0` exception for the base);
* a shape list of `d` zero words at the vertex width;
* the limit word, the node count at its own binary length, which is the
  vertex width;
* the zero word at the vertex width (the hub state key);
* the start and finish node keys `nodeKey (start m)` and `nodeKey (finish m)`;
* the word one at the vertex width;
* the zero word at the cost width, and the cost-width shape word.

All arithmetic runs at width `G` and the vertex and cost widths are obtained by
stripping leading zero bits; no width is supplied by the caller.
-/

@[expose] public section

namespace WeightedMIS.RegisterExpandedParameters

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.ExpandedParameters
open WeightedMIS.SparseSearchGraph WeightedMIS.NodeEncoding WeightedMIS.Expanded

variable {p : ℕ}

/-- Arguments: row-count word, cost list, dimension list, zero word of width
`G`. Results: arithmetic record, shape list, limit word, vertex zero word,
start key, finish key, vertex one word, cost zero word, cost shape word. -/
def parametersBody (ids : Procedures p) : Command p :=
  .call ids.scalars [.register 0, .register 1, .register 3] [4, 5, 6, 7, 8]
  (.call ids.counts [.register 2, .register 4, .register 5, .register 6, .register 7,
    .register 8, .register 3] [9, 10, 11, 12, 13, 14]
  (.call ids.strip [.register 11] [11]
  (.call ids.strip [.register 12] [12]
  (.call ids.vertex [.register 11, .register 5, .register 6, .register 10, .register 4,
    .register 13, .register 14, .register 9, .register 2] [0, 1, 4, 5, 6, 7, 8]
  (.call ids.zero [.register 12] [9]
  (.ret [.register 0, .register 1, .register 4, .register 5, .register 6, .register 7,
    .register 8, .register 9, .register 12]))))))

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  ids.ScalarMatches code ∧
  code ids.parameters = parametersBody ids ∧
  code ids.vertex = vertexBody ids ∧
  code ids.shapeMap = RegisterListMap.body ids.shapeMap ids.constItem ∧
  code ids.constItem = constItemBody ∧
  code ids.strip = RegisterSignificant.stripBody ids.strip

/-- Explicit event budget; quadratic in the widths and linear in `m` and `d`. -/
def budget (G wr wc m d : ℕ) : ℕ :=
  scalarsBudget G wr wc m + countsBudget G d + 2 * RegisterSignificant.stripBudget G +
    vertexBudget G G d + 24 * G + 200

theorem budget_mono {G wr wc m d G' wr' wc' m' d' : ℕ} (hG : G ≤ G') (hr : wr ≤ wr')
    (hc : wc ≤ wc') (hm : m ≤ m') (hd : d ≤ d') :
    budget G wr wc m d ≤ budget G' wr' wc' m' d' := by
  unfold budget scalarsBudget countsBudget vertexBudget countFoldBudget sumFoldBudget
    powFoldBudget RegisterResize.resizeBudget addBudget mulBudget subBudget
    RegisterSignificant.stripBudget
  gcongr

theorem budget_le (G wr wc m d : ℕ) :
    budget G wr wc m d ≤ 6000 * (G + wr + wc + 1) ^ 2 * (m + d + 1) := by
  have key := budget_mono (G' := G + wr + wc + 1) (wr' := G + wr + wc + 1)
    (wc' := G + wr + wc + 1) (m' := m + d + 1) (d' := m + d + 1)
    (show G ≤ G + wr + wc + 1 by omega) (show wr ≤ G + wr + wc + 1 by omega)
    (show wc ≤ G + wr + wc + 1 by omega) (show m ≤ m + d + 1 by omega)
    (show d ≤ m + d + 1 by omega)
  refine key.trans ?_
  have hX : 1 ≤ G + wr + wc + 1 := by omega
  have hY : 1 ≤ m + d + 1 := by omega
  generalize G + wr + wc + 1 = X at hX ⊢
  generalize m + d + 1 = Y at hY ⊢
  have h1 : X ≤ X ^ 2 * Y := by nlinarith
  have h2 : Y ≤ X ^ 2 * Y := Nat.le_mul_of_pos_left Y (by positivity)
  have h3 : X * Y ≤ X ^ 2 * Y := by nlinarith
  have h4 : X ^ 2 ≤ X ^ 2 * Y := by nlinarith
  have h5 : 1 ≤ X ^ 2 * Y := by nlinarith
  unfold budget scalarsBudget countsBudget vertexBudget countFoldBudget sumFoldBudget
    powFoldBudget RegisterResize.resizeBudget addBudget mulBudget subBudget
    RegisterSignificant.stripBudget
  ring_nf
  ring_nf at h1 h2 h3 h4 h5
  linarith

theorem resizedArithmetic_eq {G r d m : ℕ} {w : Fin m → ℕ} (hf : Fits G r d w) :
    resizedArithmetic (vertexWidth r d m) (word G (4 * m + 1)) (word G (2 * r + 1))
      (word G (2 * (4 * m + 1) ^ d)) (word G 1) (word G 2) = arithmetic r d m := by
  simp only [resizedArithmetic, arithmetic, resizeTo_word_of_lt hf.base,
    resizeTo_word_of_lt hf.states, resizeTo_word_of_lt hf.block, resizeTo_word_of_lt hf.one,
    resizeTo_word_of_lt hf.two]

theorem compiled (code : Code p) (ids : Procedures p) (hc : ids.Matches code)
    {h : Heap} (hh : Valid h) {rp cp dp zp : Ptr} {G wr wc r d m : ℕ}
    {rw : Bits wr} {costs : List (Bits wc)} {dims : List Ptr} {w : Fin m → ℕ}
    (hr : BitsAt h rp rw) (hrv : rw.value = r)
    (hcs : WordsAt h cp costs) (hcv : costs.map Bits.value = List.ofFn w)
    (hd : ListAt h dp dims) (hdl : dims.length = d) (hz : BitsAt h zp (Bits.zero G))
    (hfit : fitBound r d w < 2 ^ G) :
    ∃ out arp shp lp zvp sp fp op zcp csp, Extends h out ∧ Valid out ∧
      ArithmeticAt out arp (arithmetic r d m) ∧
      WordsAt out shp (List.replicate d (Bits.zero (vertexWidth r d m))) ∧
      BitsAt out lp (encodeBits (vertexWidth r d m) (nodeCount r d m)) ∧
      BitsAt out zvp (Bits.zero (vertexWidth r d m)) ∧
      BitsAt out sp (nodeKey (start m : Node (Fin r) (Fin d) m)) ∧
      BitsAt out fp (nodeKey (finish m : Node (Fin r) (Fin d) m)) ∧
      BitsAt out op (word (vertexWidth r d m) 1) ∧
      BitsAt out zcp (Bits.zero (costWidth r d m w)) ∧
      BitsAt out csp (encodeBits (costWidth r d m w) (costProduct r d w)) ∧
      Within code h (initialRegisters [.pointer rp, .pointer cp, .pointer dp, .pointer zp])
        (code ids.parameters)
        [.pointer arp, .pointer shp, .pointer lp, .pointer zvp, .pointer sp, .pointer fp,
          .pointer op, .pointer zcp, .pointer csp] out (budget G wr wc m d) := by
  obtain ⟨hs, hbody, hvertex, hmap, hconst, hstrip⟩ := hc
  have hzero : code ids.zero = RegisterZero.zeroBody ids.zero := hs.2.2.2.2.2.2.2.2.1
  have hf := fits_of_lt hfit
  have hm : costs.length = m := by simpa using congrArg List.length hcv
  have hsum : (costs.map Bits.value).sum = weightBound w := by
    rw [hcv, List.sum_ofFn]
    rfl
  obtain ⟨h1, q4, q5, q6, q7, q8, e1, v1, hq4, hq5, hq6, hq7, hq8, run1⟩ :=
    scalars_compiled code ids hs hh hr hcs hz
  rw [hm] at hq5 hq7
  rw [hrv] at hq6 hq7
  rw [hsum] at hq8
  have hpos : 1 ≤ (4 * m + 1) ^ dims.length := Nat.one_le_pow _ _ (by omega)
  obtain ⟨h2, q9, q10, q11, q12, q13, q14, e2, v2, hq9, hq10, hq11, hq12, hq13, hq14, run2⟩ :=
    counts_compiled code ids hs v1 (hd.mono e1) hq4 hq5 hq6 hq7 hq8 (hz.mono e1) hpos
      (by rw [hdl]; exact hf.pow) hf.one
  rw [hdl] at hq9 hq10 hq11 hq12 hq14 hpos
  have hN : (word G (2 * (4 * m + 1) ^ d * (1 + (2 * r + 1) ^ 2))).value = nodeCount r d m :=
    word_value_of_lt hf.nodes
  have hC : (word G ((2 * (4 * m + 1) ^ d * (1 + (2 * r + 1) ^ 2) *
      (2 * r + 2 * m + 2) + 2) * weightBound w)).value = costProduct r d w :=
    word_value_of_lt hf.cost
  obtain ⟨vq, hvq, run3⟩ := RegisterSignificant.strip_compiled_of_value code ids.strip hstrip
    hq11 hN
  obtain ⟨cq, hcq, run4⟩ := RegisterSignificant.strip_compiled_of_value code ids.strip hstrip
    hq12 hC
  have e12 := e1.trans e2
  obtain ⟨h5, ap, shp, zvp, sk, fk, ok, e5, v5, har, hsh, hlim, hzv, hsk, hfk, hok, run5⟩ :=
    vertex_compiled code ids hs hmap hconst hvertex v2 (k := vertexWidth r d m) hvq
      (hq5.mono e2) (hq6.mono e2) hq10 (hq4.mono e2) hq13 hq14 hq9 (hd.mono e12)
  obtain ⟨h6, zc, e6, v6, hzc, -, run6⟩ := RegisterZero.compiled code ids.zero hzero v5
    (hcq.mono e5)
  rw [resizedArithmetic_eq hf] at har
  rw [hdl] at hsh
  rw [resizeTo_word_of_lt (by have := hf.pow; omega), ← nodeKey_start r d m] at hsk
  rw [resizeTo_word_of_lt hf.pow, ← nodeKey_finish r d m] at hfk
  rw [resizeTo_word_of_lt hf.one] at hok
  refine ⟨h6, ap, shp, vq, zvp, sk, fk, ok, zc, cq, e12.trans (e5.trans e6), v6, har.mono e6,
    hsh.mono e6, hlim.mono e6, hzv.mono e6, hsk.mono e6, hfk.mono e6, hok.mono e6, hzc,
    (hcq.mono e5).mono e6, ?_⟩
  let r0 := initialRegisters [Value.pointer rp, .pointer cp, .pointer dp, .pointer zp]
  let r1 := bindResults r0 [4, 5, 6, 7, 8]
    [Value.pointer q4, .pointer q5, .pointer q6, .pointer q7, .pointer q8]
  let r2 := bindResults r1 [9, 10, 11, 12, 13, 14]
    [Value.pointer q9, .pointer q10, .pointer q11, .pointer q12, .pointer q13, .pointer q14]
  let r3 := bindResults r2 [11] [Value.pointer vq]
  let r4 := bindResults r3 [12] [Value.pointer cq]
  let r5 := bindResults r4 [0, 1, 4, 5, 6, 7, 8]
    [Value.pointer ap, .pointer shp, .pointer vq, .pointer zvp, .pointer sk, .pointer fk,
      .pointer ok]
  let r6 := bindResults r5 [9] [Value.pointer zc]
  have last : Within code h6 r6 (.ret [.register 0, .register 1, .register 4, .register 5,
      .register 6, .register 7, .register 8, .register 9, .register 12])
      [.pointer ap, .pointer shp, .pointer vq, .pointer zvp, .pointer sk, .pointer fk,
        .pointer ok, .pointer zc, .pointer cq] h6 19 := by
    simpa [r6, r5, r4, r3, values, Atom.eval, bindResults] using
      Within.ret code h6 r6 [.register 0, .register 1, .register 4, .register 5,
        .register 6, .register 7, .register 8, .register 9, .register 12]
  have a6 : values r5 [.register 12] = [.pointer cq] := by
    simp [r5, r4, values, Atom.eval, bindResults]
  have c6 := Within.call (procedure := ids.zero) (regs := r5)
    (arguments := [.register 12]) (results := [9])
    (by simpa only [a6, hzero] using run6) last
  have a5 : values r4 [.register 11, .register 5, .register 6, .register 10, .register 4,
      .register 13, .register 14, .register 9, .register 2] =
      [.pointer vq, .pointer q5, .pointer q6, .pointer q10, .pointer q4, .pointer q13,
        .pointer q14, .pointer q9, .pointer dp] := by
    simp [r4, r3, r2, r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c5 := Within.call (procedure := ids.vertex) (regs := r4)
    (arguments := [.register 11, .register 5, .register 6, .register 10, .register 4,
      .register 13, .register 14, .register 9, .register 2]) (results := [0, 1, 4, 5, 6, 7, 8])
    (by simpa only [a5] using run5) c6
  have a4 : values r3 [.register 12] = [.pointer q12] := by
    simp [r3, r2, values, Atom.eval, bindResults]
  have c4 := Within.call (procedure := ids.strip) (regs := r3)
    (arguments := [.register 12]) (results := [12])
    (by simpa only [a4] using run4.mono (le_refl _)) c5
  have a3 : values r2 [.register 11] = [.pointer q11] := by
    simp [r2, values, Atom.eval, bindResults]
  have c3 := Within.call (procedure := ids.strip) (regs := r2)
    (arguments := [.register 11]) (results := [11])
    (by simpa only [a3] using run3) c4
  have a2 : values r1 [.register 2, .register 4, .register 5, .register 6, .register 7,
      .register 8, .register 3] =
      [.pointer dp, .pointer q4, .pointer q5, .pointer q6, .pointer q7, .pointer q8,
        .pointer zp] := by
    simp [r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c2 := Within.call (procedure := ids.counts) (regs := r1)
    (arguments := [.register 2, .register 4, .register 5, .register 6, .register 7,
      .register 8, .register 3]) (results := [9, 10, 11, 12, 13, 14])
    (by simpa only [a2] using run2) c3
  have a1 : values r0 [.register 0, .register 1, .register 3] =
      [.pointer rp, .pointer cp, .pointer zp] := by
    simp [r0, values, Atom.eval, initialRegisters]
  have c1 := Within.call (procedure := ids.scalars) (regs := r0)
    (arguments := [.register 0, .register 1, .register 3]) (results := [4, 5, 6, 7, 8])
    (by simpa only [a1] using run1) c2
  rw [hbody]
  refine c1.mono ?_
  have hv := hf.vertexWidth_le
  have hcw := hf.costWidth_le
  rw [← costWidth_eq] at *
  simp only [budget, vertexBudget, RegisterResize.resizeBudget, List.length_cons,
    List.length_nil, hm, hdl]
  omega

/-! ## Facts for the generation and search interfaces -/

/-- Value facts consumed by `SparseGraphConstruction.compiled` and by
`ExpandedSourceSemantics.SourceInterface`. -/
theorem generation_facts (r d m : ℕ) :
    ArithmeticRepresents (arithmetic r d m) r d m ∧
      (List.replicate d (Bits.zero (vertexWidth r d m))).length = d ∧
      (encodeBits (vertexWidth r d m) (nodeCount r d m)).value = nodeCount r d m ∧
      (word (vertexWidth r d m) 1).value = 1 ∧ (arithmetic r d m).one.value = 1 ∧
      nodeCount r d m ≤ 2 ^ vertexWidth r d m := by
  have h1 := (ScalarNodeCodec.parameters_fit r d m).2.2.1
  refine ⟨arithmetic_represents r d m, List.length_replicate .., limit_value r d m,
    word_value_of_lt h1, word_value_of_lt h1, (Nat.lt_size_self _).le⟩

/-- The working width also counts the settled path length of the search. -/
theorem count_width {Label : Type*} {r m d G : ℕ} (η : Option (Fin m) → Label)
    (C : Fin m → Walks.Column (Fin r)) (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2)
    (w : Fin m → ℕ) (hfit : fitBound r d w < 2 ^ G) :
    (Labeled.graph η C W π m w).elements.length + 2 ≤ 2 ^ G :=
  (Nat.add_le_add_right (Labeled.graph_size_le η C W π m w) 2).trans (fits_of_lt hfit).entries

end WeightedMIS.RegisterExpandedParameters
