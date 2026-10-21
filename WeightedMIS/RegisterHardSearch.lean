module

public import WeightedMIS.RegisterHardSearchBudget
public import WeightedMIS.ExecutableReduction

/-!
# Compiled sparse search of a hard component

One fixed procedure takes, at a single input width `G`,

* the stored signed columns `C` (`CompiledTemplates.ColumnAt` with state keys
  of width `G`),
* the per-edge lists of signed delta words (values `W e i`),
* the signed parity-row words (values whose residues are `π e`),
* the cost words (values `cost e`),
* the row-count word `r`, a list of length `d`, and the zero word of width `G`,

and returns the list of count words whose values are
`projection (ExecutableReduction.searchLabels C W π m cost) e` in edge order.

The procedure computes the parameter words at the vertex and cost widths
(`RegisterExpandedParameters`), the label keys `0..m` (`RegisterGenerationInputs`),
the edge records (`RegisterEdgeMetadata`), the expanded adjacency trie
(`SparseGraphConstruction`), the shortest path with its label histogram
(`EfficientSearch.Output.compiled_exact`), and the ordered histogram values
(`RegisterHistogramValues`). The generated trie is identified with
`SparseSearchGraph.Labeled.graph` and the histogram with the projection of the
search labels (`SearchHistogramProjection.table_projection`). The premises are
the single width bound `fitBound r d cost < 2^G`, `|W| ≤ 2`, and the existence
of a source-to-target path in the expanded graph.
-/

@[expose] public section

namespace WeightedMIS.RegisterHardSearch

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.Walks WeightedMIS.CompiledTemplates
open WeightedMIS.ExpandedWords WeightedMIS.ExpandedParameters WeightedMIS.SparseSearchGraph
open WeightedMIS.NodeEncoding WeightedMIS.Expanded WeightedMIS.RegisterColumnResize
open WeightedMIS.SearchHistogramProjection WeightedMIS.RegisterGenerationInputs

variable {p : ℕ}

structure Procedures (p : ℕ) where
  inputs : RegisterGenerationInputs.Procedures p
  edges : RegisterEdgeMetadata.Procedures p
  graph : RegisterGraphEnumeration.Procedures p
  templates : Fin p
  column : Fin p
  stub : Fin p
  emit : Fin p
  pack : Fin p
  enumerate : Fin p
  build : Fin p
  insert : Fin p
  construct : Fin p
  search : EfficientSearch.Linked.Procedures p
  recovery : RegisterSearchHistogram.Procedures p
  readback : Fin p
  output : Fin p
  values : Fin p
  hard : Fin p

/-- Arguments: columns, delta lists, parity words, cost words, row-count word,
dimension list, zero word. Result: the count words in edge order. -/
def hardBody (ids : Procedures p) : Command p :=
  .call ids.inputs.parameters.parameters [.register 4, .register 3, .register 5, .register 6]
    [7, 8, 9, 10, 11, 12, 13, 14, 15]
  (.call ids.inputs.keys [.register 3, .register 6] [4, 5]
  (.allocate 5 (.pair (.register 14) (.register 5))
  (.call ids.edges.edges [.register 0, .register 1, .register 2, .register 3, .register 4,
    .register 10, .register 15] [0]
  (.call ids.construct [.register 0, .register 10, .register 7, .register 8, .register 5,
    .register 9, .register 10, .register 13] [1]
  (.call ids.output [.register 1, .register 11, .register 14, .register 12, .register 6]
    [2, 3, 15]
  (.call ids.values [.register 4, .register 3, .register 6] [0]
  (.ret [.register 0])))))))

structure Procedures.Matches (ids : Procedures p) (code : Code p) : Prop where
  inputs : ids.inputs.Matches code
  edges : ids.edges.Matches code
  graph : ids.graph.Matches code
  templates : code ids.templates = CompiledTemplates.listBody ids.templates ids.column
  column : code ids.column = CompiledTemplates.columnBody ids.stub ids.emit
  stub : code ids.stub = CompiledTemplates.stubBody
  emit : code ids.emit = CompiledTemplates.emitBody
  pack : code ids.pack = RegisterGenerationPack.body
  enumerate : code ids.enumerate = RegisterAllSources.body ids.graph.range ids.graph.scan
  build : code ids.build = CompiledGraphConstruction.graphBody ids.build ids.insert
  insert : code ids.insert = CompiledTrie.insertBody ids.insert
  construct : code ids.construct =
    SparseGraphConstruction.body ids.templates ids.pack ids.enumerate ids.build
  search : ids.search.Matches code
  recovery : ids.recovery.Matches code
  readback : code ids.readback = RegisterSearchHistogram.readbackBody ids.recovery.select
    ids.recovery.labels ids.recovery.histogram
  output : code ids.output = EfficientSearch.Output.body ids.search.solve ids.readback
  values : code ids.values = RegisterHistogramValues.valuesBody ids.values ids.recovery.lookup
  hard : code ids.hard = hardBody ids

/-- The compiled hard-component search returns exactly the edge projections of
`ExecutableReduction.searchLabels`, within `budget r m d G` interpreter events. -/
theorem compiled (code : Code p) (ids : Procedures p) (hc : ids.Matches code)
    {r m d G : ℕ} (key : State (Fin r) → Bits G)
    (hkey : ∀ v, (key v).value = (stateEquiv r v).val) (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (hW : ∀ e i, |W e i| ≤ 2) (π : Fin m → ZMod 2) (cost : Fin m → ℕ)
    (D : Fin m → Fin d → SignedWord G) (hD : ∀ e i, (D e i).value = W e i)
    (P : Fin m → RegisterPotentialStep.Word G)
    (hP : ∀ e, (RegisterPotentialStep.value (P e) : ZMod 2) = π e)
    (K : Fin m → Bits G) (hK : ∀ e, (K e).value = cost e)
    {rw : Bits G} (hrv : rw.value = r) {dims : List Ptr} (hdims : dims.length = d)
    (hfit : fitBound r d cost < 2 ^ G)
    (hreach : Nonempty (Path C W π m (start m) (finish m)))
    {h : Heap} (hh : Valid h) {cp dp pp kp rp np zp : Ptr}
    (hcols : ListRep (ColumnAt key) h cp (List.ofFn C))
    (hds : ListRep DeltasAt h dp (List.ofFn (fun e => List.ofFn (D e))))
    (hpis : SignedWords.ListAt h pp (List.ofFn P))
    (hcosts : WordsAt h kp (List.ofFn K))
    (hr : BitsAt h rp rw) (hdl : ListAt h np dims) (hz : BitsAt h zp (Bits.zero G)) :
    ∃ (out : Heap) (q : Ptr) (counts : List (Bits G)), Extends h out ∧ Valid out ∧
      WordsAt out q counts ∧
      counts.map Bits.value =
        List.ofFn (fun e => projection (ExecutableReduction.searchLabels C W π m cost) e) ∧
      Within code h (initialRegisters [.pointer cp, .pointer dp, .pointer pp, .pointer kp,
        .pointer rp, .pointer np, .pointer zp]) (code ids.hard) [.pointer q] out
        (budget r m d G) := by
  have hf := fits_of_lt hfit
  have hm : m < 2 ^ G := by have := hf.base; omega
  -- parameter words
  have hcv : (List.ofFn K).map Bits.value = List.ofFn cost := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext hK)
  obtain ⟨h1, arp, shp, lp, zvp, sp, fp, op, zcp, csp, e1, v1, har, hshape, hlimit, hzv, hsp, hfp,
    hop, hzc, hcs, run1⟩ := RegisterExpandedParameters.compiled code ids.inputs.parameters
      hc.inputs.1 hh hr hrv hcosts hcv hdl hdims hz hfit
  -- label keys
  obtain ⟨h2, keys, mp, e2, v2, hkeys, hmp, run2⟩ := RegisterGenerationInputs.keys_compiled code
    ids.inputs hc.inputs v1 (hcosts.mono e1) (by simp) (hz.mono e1) hm hf.one
  obtain ⟨L, hLlist, hL⟩ := labels_of_keys hkeys
  let η : Option (Fin m) → Ptr := labelPtr L mp
  have hη : ∀ l, BitsAt h2 (η l) (edgeKey G l) := labelPtr_bitsAt hL hmp
  have hinj : Function.Injective η := labelPtr_injective hm hη
  obtain ⟨encode, hencode⟩ := exists_encode (G := G) hinj
  -- connector cost-label record
  have hzc2 := hzc.mono e2
  have a3 := allocate_cell v2 (.pair zcp mp) (by
    intro x hx
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hzc2.allocated
    · exact hmp.allocated)
  let h3 := h2 ++ [.pair zcp mp]
  have e3 : Extends h2 h3 := a3.1
  have hconn : CostLabelAt h3 h2.length (Bits.zero (costWidth r d m cost)) (η none) :=
    ⟨zcp, a3.2.2, hzc2.mono e3, lt_of_lt_of_le hmp.allocated e3.length_le⟩
  have e13 : Extends h1 h3 := e2.trans e3
  have e03 : Extends h h3 := e1.trans e13
  -- edge records
  obtain ⟨h4, q4, e4, v4, hedges, run4⟩ := RegisterEdgeMetadata.edges_compiled code ids.edges
    hc.edges key C (fun e => List.ofFn (D e)) P K L (d := d) (fun e => List.length_ofFn) a3.2.1
    (ListRep.mono e03 (fun _ _ hx => hx.mono e03) hcols)
    (ListRep.mono e03 (fun _ _ hx => hx.mono e03) hds) (hpis.mono e03) (hcosts.mono e03)
    (hLlist.mono e3) (hzv.mono e13) (hcs.mono e13)
  have hi := source_interface key hkey C W hW π cost D hD P hP K hK η
  have hhub : resizeKey (vertexWidth r d m) key none = Bits.zero (vertexWidth r d m) :=
    hubKey_eq hi.key
  obtain ⟨ptrs, hptrs, hrecords⟩ := hedges
  have e14 : Extends h1 h4 := e13.trans e4
  -- adjacency trie
  have hgen := RegisterExpandedParameters.generation_facts r d m
  obtain ⟨h5, gp, e5, v5, hgraph, run5⟩ := SparseGraphConstruction.compiled code ids.graph
    hc.graph ids.templates ids.column ids.stub ids.emit ids.pack ids.enumerate ids.build ids.insert
    hc.templates hc.column hc.stub hc.emit hc.pack hc.enumerate hc.build hc.insert
    (resizeKey (vertexWidth r d m) key) C (edgeMetadata cost D P K η) v4 hptrs hrecords
    (by rw [hhub]; exact hzv.mono e14) (har.mono e14) (hshape.mono e14) (hconn.mono e4)
    (hlimit.mono e14) (hzv.mono e14) (hop.mono e14) hgen.2.2.2.1 hgen.2.2.2.2.1
    (fun e => by simp [edgeMetadata, RegisterEdgeMetadata.metadata])
  have hgraph' : GraphAt h5 gp (Labeled.graph η C W π m cost) := by
    rw [← graph_eq key hkey C W hW π cost D hD P hP K hK η]
    exact hgraph
  have e15 : Extends h1 h5 := e14.trans e5
  have e25 : Extends h2 h5 := (e3.trans e4).trans e5
  -- search and histogram
  obtain ⟨path⟩ := hreach
  have hwalk := Labeled.storedPath_walk η cost path
  obtain ⟨h6, dist, tablePtr, distance, rpath, table, e6, v6, -, htable, hlookup, -, -, hcounts,
    run6⟩ := EfficientSearch.Output.compiled_exact code ids.search hc.search ids.recovery
      hc.recovery ids.readback hc.readback v5 hgraph' (hsp.mono e15) (hzc.mono e15)
      (hfp.mono e15) (hz.mono (e1.trans e15)) (Labeled.graph_canonical η C W π m cost)
      (weightBound cost) (Labeled.graph_weight_bound η C W π m cost)
      (Labeled.graph_no_overflow_width η C W π m cost)
      (RegisterExpandedParameters.count_width η C W π cost hfit) encode
      (fun x hx => by
        obtain ⟨s, y, -, rfl⟩ := (Labeled.mem_graph_iff η C W π m cost x).mp hx
        show BitsAt h5 (η y.1) (encode (η y.1))
        rw [hencode]
        exact (hη y.1).mono e25)
      ⟨_, hwalk⟩
  -- ordered count words
  have e26 : Extends h2 h6 := e25.trans e6
  obtain ⟨h7, result, e7, v7, hresult, run7⟩ := RegisterHistogramValues.compiled code ids.values
    ids.recovery.lookup hc.values hc.recovery.1 v6 (hkeys.mono e26) htable
    (hz.mono ((e1.trans e2).trans e26))
  refine ⟨h7, result, _, (e1.trans e2).trans (e26.trans e7), v7, hresult, ?_, ?_⟩
  · rw [List.map_map, List.map_ofFn]
    apply congrArg List.ofFn
    funext e
    exact table_projection η encode hencode hm hlookup hcounts e
  -- the derivation of the fixed body
  let regs := initialRegisters [Value.pointer cp, .pointer dp, .pointer pp, .pointer kp,
    .pointer rp, .pointer np, .pointer zp]
  let r1 := bindResults regs [7, 8, 9, 10, 11, 12, 13, 14, 15] [Value.pointer arp, .pointer shp,
    .pointer lp, .pointer zvp, .pointer sp, .pointer fp, .pointer op, .pointer zcp, .pointer csp]
  let r2 := bindResults r1 [4, 5] [Value.pointer keys, .pointer mp]
  let r3 := Function.update r2 5 (Value.pointer h2.length)
  let r4 := bindResults r3 [0] [Value.pointer q4]
  let r5 := bindResults r4 [1] [Value.pointer gp]
  let r6 := bindResults r5 [2, 3, 15] [Value.pointer dist, .pointer tablePtr, .flag false]
  let r7 := bindResults r6 [0] [Value.pointer result]
  have last : Within code h7 r7 (.ret [.register 0]) [.pointer result] h7 3 := by
    simpa [r7, values, Atom.eval, bindResults] using Within.ret code h7 r7 [.register 0]
  have a7 : values r6 [.register 4, .register 3, .register 6] =
      [.pointer keys, .pointer tablePtr, .pointer zp] := by
    simp [r6, r5, r4, r3, r2, r1, regs, values, Atom.eval, bindResults, initialRegisters]
  have c7 := Within.call (procedure := ids.values) (regs := r6)
    (arguments := [.register 4, .register 3, .register 6]) (results := [0])
    (by simpa only [a7] using run7) last
  have a6 : values r5 [.register 1, .register 11, .register 14, .register 12, .register 6] =
      [.pointer gp, .pointer sp, .pointer zcp, .pointer fp, .pointer zp] := by
    simp [r5, r4, r3, r2, r1, regs, values, Atom.eval, bindResults, initialRegisters]
  have c6 := Within.call (procedure := ids.output) (regs := r5)
    (arguments := [.register 1, .register 11, .register 14, .register 12, .register 6])
    (results := [2, 3, 15]) (by simpa only [a6, hc.output] using run6) c7
  have a5 : values r4 [.register 0, .register 10, .register 7, .register 8, .register 5,
      .register 9, .register 10, .register 13] =
      [.pointer q4, .pointer zvp, .pointer arp, .pointer shp, .pointer h2.length, .pointer lp,
        .pointer zvp, .pointer op] := by
    simp [r4, r3, r2, r1, regs, values, Atom.eval, bindResults]
  have c5 := Within.call (procedure := ids.construct) (regs := r4)
    (arguments := [.register 0, .register 10, .register 7, .register 8, .register 5,
      .register 9, .register 10, .register 13]) (results := [1])
    (by simpa only [a5, hc.construct] using run5) c6
  have a4 : values r3 [.register 0, .register 1, .register 2, .register 3, .register 4,
      .register 10, .register 15] =
      [.pointer cp, .pointer dp, .pointer pp, .pointer kp, .pointer keys, .pointer zvp,
        .pointer csp] := by
    simp [r3, r2, r1, regs, values, Atom.eval, bindResults, initialRegisters]
  have c4 := Within.call (procedure := ids.edges.edges) (regs := r3)
    (arguments := [.register 0, .register 1, .register 2, .register 3, .register 4,
      .register 10, .register 15]) (results := [0])
    (by simpa only [a4] using run4) c5
  have c3 := Within.allocate (regs := r2) (dst := 5) (expr := .pair (.register 14) (.register 5))
    (c := .pair zcp mp) (h := h2)
    (by simp [r2, r1, bindResults, CellExpr.eval, Atom.eval, Value.asPointer]) c4
  have a2 : values r1 [.register 3, .register 6] = [.pointer kp, .pointer zp] := by
    simp [r1, regs, values, Atom.eval, bindResults, initialRegisters]
  have c2 := Within.call (procedure := ids.inputs.keys) (regs := r1)
    (arguments := [.register 3, .register 6]) (results := [4, 5])
    (by simpa only [a2] using run2) c3
  have a1 : values regs [.register 4, .register 3, .register 5, .register 6] =
      [.pointer rp, .pointer kp, .pointer np, .pointer zp] := by
    simp [regs, values, Atom.eval, initialRegisters]
  have c1 := Within.call (procedure := ids.inputs.parameters.parameters) (regs := regs)
    (arguments := [.register 4, .register 3, .register 5, .register 6])
    (results := [7, 8, 9, 10, 11, 12, 13, 14, 15]) (by simpa only [a1] using run1) c2
  rw [hc.hard]
  refine c1.mono ?_
  -- budget
  have hv : vertexWidth r d m ≤ G := hf.vertexWidth_le
  have hcw : costWidth r d m cost ≤ G := hf.costWidth_le
  have hE := Labeled.graph_size_le η C W π m cost
  have ht : (SparseGraphConstruction.data C (edgeMetadata cost D P K η) (arithmetic r d m)
      (List.replicate d (Bits.zero (vertexWidth r d m))) (Bits.zero (costWidth r d m cost))
      (η none)).templates.length ≤ 2 * m := by
    simpa [SparseGraphConstruction.data] using SearchConstruction.signedArcs_length_le C
  have hs : (arithmetic r d m).states.value = 2 * r + 1 := (arithmetic_represents r d m).2.1
  have b4 := edges_mono (m := m) (d := d) (n0 := G) (n1 := G) (n2 := G) (wc := G)
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl hv hcw
  have b5 := construction_mono (m := m) (d := d) (s := (arithmetic r d m).states.value)
    (N := (encodeBits (vertexWidth r d m) (nodeCount r d m)).value) le_rfl hv le_rfl ht
    (le_of_eq hs) (le_of_eq (limit_value r d m))
  have b6 := steps_mono (lb := G) (nb := G) hv hcw le_rfl le_rfl hE
  simp only [List.length_cons, List.length_nil, List.length_replicate, List.length_ofFn,
    CellExpr.args] at b5 ⊢
  unfold budget boundOf
  omega

/-- The same result with the polynomial event bound of `budget_le`: linear in
`(4m+1)^d` and polynomial of degree six in `r + m + d + G`. -/
theorem compiled_bound (code : Code p) (ids : Procedures p) (hc : ids.Matches code)
    {r m d G : ℕ} (key : State (Fin r) → Bits G)
    (hkey : ∀ v, (key v).value = (stateEquiv r v).val) (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (hW : ∀ e i, |W e i| ≤ 2) (π : Fin m → ZMod 2) (cost : Fin m → ℕ)
    (D : Fin m → Fin d → SignedWord G) (hD : ∀ e i, (D e i).value = W e i)
    (P : Fin m → RegisterPotentialStep.Word G)
    (hP : ∀ e, (RegisterPotentialStep.value (P e) : ZMod 2) = π e)
    (K : Fin m → Bits G) (hK : ∀ e, (K e).value = cost e)
    {rw : Bits G} (hrv : rw.value = r) {dims : List Ptr} (hdims : dims.length = d)
    (hfit : fitBound r d cost < 2 ^ G)
    (hreach : Nonempty (Path C W π m (start m) (finish m)))
    {h : Heap} (hh : Valid h) {cp dp pp kp rp np zp : Ptr}
    (hcols : ListRep (ColumnAt key) h cp (List.ofFn C))
    (hds : ListRep DeltasAt h dp (List.ofFn (fun e => List.ofFn (D e))))
    (hpis : SignedWords.ListAt h pp (List.ofFn P))
    (hcosts : WordsAt h kp (List.ofFn K))
    (hr : BitsAt h rp rw) (hdl : ListAt h np dims) (hz : BitsAt h zp (Bits.zero G)) :
    ∃ (out : Heap) (q : Ptr) (counts : List (Bits G)), Extends h out ∧ Valid out ∧
      WordsAt out q counts ∧
      counts.map Bits.value =
        List.ofFn (fun e => projection (ExecutableReduction.searchLabels C W π m cost) e) ∧
      Within code h (initialRegisters [.pointer cp, .pointer dp, .pointer pp, .pointer kp,
        .pointer rp, .pointer np, .pointer zp]) (code ids.hard) [.pointer q] out
        (2 ^ 40 * (4 * m + 1) ^ d * (r + m + d + G + 2) ^ 6) := by
  obtain ⟨out, q, counts, he, hv, hq, hvals, run⟩ := compiled code ids hc key hkey C W hW π cost
    D hD P hP K hK hrv hdims hfit hreach hh hcols hds hpis hcosts hr hdl hz
  exact ⟨out, q, counts, he, hv, hq, hvals, run.mono (budget_le r m d G)⟩

end WeightedMIS.RegisterHardSearch
