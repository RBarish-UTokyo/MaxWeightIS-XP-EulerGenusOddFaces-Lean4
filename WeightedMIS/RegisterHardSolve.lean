module

public import WeightedMIS.RegisterHardKernel
public import WeightedMIS.RegisterTranspose
public import WeightedMIS.RegisterHalve
public import WeightedMIS.RegisterResize
public import WeightedMIS.RegisterOddRow
public import WeightedMIS.RegisterHardSearch
public import WeightedMIS.RegisterHardRecovery
public import WeightedMIS.RegisterEdgeCostProgram
public import WeightedMIS.RegisterEdgeWords
public import WeightedMIS.RegisterComponentSolve

/-!
# The compiled hard-component solver

The entry procedure receives the stored ribbon table, the vertex words and
the canonical stored weights (`RegisterWeightMask.CanonAt w0`) of a connected
nonbipartite all-half component with nonnegative weights. It

1. reads the endpoint records and the edge index words off the table,
2. computes the integer edge costs (`RegisterEdgeCostProgram`) at the cost
   width `c = NetworkWeights.width w0 n`,
3. computes stored rational rows of the global kernel rows
   (`RegisterHardKernel`) at the rational width `ratWidth n m`,
4. builds the zero and unit words of the search width
   `G = searchWidth c n m d` with `d` the number of global rows,
5. transposes the global rows into per-edge deltas of width `G`, computes the
   even-face columns with state keys of width `G` and the number of even
   faces, resizes the costs to width `G`, computes the odd row at width `G`,
6. runs the sparse search (`RegisterHardSearch`) and the recovery
   (`RegisterHardRecovery`) at width `G`.

The output is the stored word list of `ExecutableReduction.hardSolve`; the
main theorem `hard_spec` is the contract `RegisterComponentSolve.HardSpec`.
-/

@[expose] public section

namespace WeightedMIS.RegisterHardSolve

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.RibbonTable
open WeightedMIS.RegisterFlagKeys WeightedMIS.HardWidths WeightedMIS.RegisterHardInputs
open WeightedMIS.RegisterIncidenceRows (EdgeAt)
open WeightedMIS.RegisterRationalCut (RowsAt)
open scoped BigOperators

variable {p : ℕ}

/-! ## Procedures -/

/-- Arguments 0 = table, 1 = vertex words, 2 = edge records, 3 = edge index
words, 4 = cost words, 5 = global rational rows. -/
def stage2Body (consts tstage face shift resizeList odd search recovery : Fin p) : Command p :=
  .call consts [.register 5, .register 4, .register 0, .register 1] [6, 7]
  (.call tstage [.register 2, .register 5, .register 6] [8, 9]
  (.allocate 10 (.pair (.register 7) (.register 6))
  (.call face [.register 0, .register 10, .register 7] [10, 11, 12]
  (.call shift [.register 12, .flag false] [12, 11]
  (.call resizeList [.register 4, .register 6] [4]
  (.load (.register 1) 11 13 15 { CompiledTrie.failCases with
    cons :=
      .allocate 13 (.bit (.flag true) .null)
      (.call odd [.register 2, .register 3, .register 1, .register 11, .register 13, .register 7,
        .register 6] [14, 15]
      (.call search [.register 10, .register 8, .register 14, .register 4, .register 12,
        .register 9, .register 6] [5]
      (.call recovery [.register 2, .register 1, .register 11, .register 14, .register 5,
        .register 13, .register 7, .register 6] [15]
      (.ret [.register 15])))) }))))))

/-- Arguments 0 = table, 1 = vertex words, 2 = stored weights. -/
def hardBody (edges keys costs kernel stage2 : Fin p) : Command p :=
  .call edges [.register 0, .null] [3]
  (.call keys [.register 0, .null] [4]
  (.call costs [.register 1, .register 3, .register 2] [5, 6]
  (.call kernel [.register 0, .register 1, .register 3, .register 4] [6]
  (.call stage2 [.register 0, .register 1, .register 3, .register 4, .register 5, .register 6] [7]
  (.ret [.register 7])))))

structure Procedures (p : ℕ) where
  hard : Fin p
  stage2 : Fin p
  edges : Fin p
  edgeItem : Fin p
  keys : Fin p
  key : Fin p
  searchConsts : Fin p
  shift : Fin p
  resizeList : Fin p
  costs : RegisterEdgeCostProgram.Procedures p
  kernel : RegisterHardKernel.Procedures p
  transpose : RegisterTranspose.Procedures p
  odd : RegisterOddRow.Procedures p
  search : RegisterHardSearch.Procedures p
  recovery : RegisterHardRecovery.Procedures p

structure Procedures.Matches (ids : Procedures p) (code : Code p) : Prop where
  hard : code ids.hard = hardBody ids.edges ids.keys ids.costs.self ids.kernel.kernel ids.stage2
  stage2 : code ids.stage2 = stage2Body ids.searchConsts ids.transpose.stage ids.kernel.face.top
    ids.shift ids.resizeList ids.odd.self ids.search.hard ids.recovery.self
  edges : code ids.edges = RegisterListMap.body ids.edges ids.edgeItem
  edgeItem : code ids.edgeItem = edgeItemBody
  keys : code ids.keys = RegisterListMap.body ids.keys ids.key
  key : code ids.key = RegisterEdgeWords.keyBody
  searchConsts : code ids.searchConsts =
    searchConstsBody ids.kernel.dbl ids.kernel.pad ids.kernel.widen
  shift : code ids.shift = RegisterHalve.shiftBody ids.shift
  resizeList : code ids.resizeList = RegisterListMap.body ids.resizeList ids.transpose.resize.resize
  costs : ids.costs.Matches code
  kernel : ids.kernel.Matches code
  transpose : ids.transpose.Matches code
  odd : ids.odd.Matches code
  search : ids.search.Matches code
  recovery : ids.recovery.Matches code

/-! ## Budgets -/

/-- Events of the stages after the kernel, at the search width `G`. -/
def stage2Budget (W c N n m d : ℕ) : ℕ :=
  searchConstsBudget c n m d +
    RegisterTranspose.stageBudget N (searchWidth c n m d) d m +
    FaceStageProgram.stageBudget W (searchWidth c n m d) (searchWidth c n m d) m +
    (28 * searchWidth c n m d + 15) +
    ((RegisterResize.resizeBudget (searchWidth c n m d) c + 35) * m + 13) +
    RegisterOddRow.budget W W (searchWidth c n m d) n m +
    2 ^ 40 * (4 * m + 1) ^ d * (5 * m + d + searchWidth c n m d + 2) ^ 6 +
    RegisterHardRecovery.budget W (searchWidth c n m d) n m + 200

/-! ## Facts about the instance -/

theorem edges_pos {n m : ℕ} {left right : Fin m → Fin n}
    (hnb : ¬Incidence.Bipartite left right) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · exact absurd ⟨fun _ => true, fun e => e.elim0⟩ hnb
  · exact h

theorem search_reachable {n m : ℕ} {left right : Fin m → Fin n}
    (R : EmbeddingFaces.Ribbon left right) (root : Fin n) (hc : Incidence.Connected left right)
    (hnb : ¬Incidence.Bipartite left right) :
    Nonempty (Expanded.Path (R.computedColumn (EmbeddingFaces.Flag.canonicalOrder m))
      (ComputedEmbeddedMatrices.globalColumn R)
      (fun e => (ExecutableReduction.parityRow (left := left) (right := right) root e : ZMod 2)) m
      (Expanded.start m) (Expanded.finish m)) := by
  have hmat := ComputedEmbeddedMatrices.computed_matrices_spec R hc hnb
  have hπ : IntegerSlacks.OddRow left right root
      (ExecutableReduction.parityRow (left := left) (right := right) root) :=
    ComputedOddRow.oddRow_correct left right (List.finRange m) (fun e => List.mem_finRange e)
      (List.finRange n) (fun v => List.mem_finRange v) root hc hnb
  have hempty : Slack.Independent left right (∅ : Finset (Fin n)) := by intro e; simp
  obtain ⟨witness, -, -⟩ := Reduction.independent_set_has_path left right root hc _ _
    hmat.2 hmat.1 _ hπ (fun _ => 0) ∅ hempty
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  unfold Reduction.SearchPath at witness
  rw [hcard] at witness
  exact ⟨witness⟩

/-! ## The stages after the kernel -/

theorem stage2_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W c N n m : ℕ} {left right : Fin m → Fin n} (R : EmbeddingFaces.Ribbon left right)
    (w : Fin n → ℚ) (hn0 : 0 < n) (hn : n < 2 ^ W) (hmW : m < 2 ^ W)
    (hc : Incidence.Connected left right) (hnb : ¬Incidence.Bipartite left right)
    (hw : ∀ v, 0 ≤ w v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2))
    (hcl : ∀ e, IntegerEdgeCosts.integerCost left right (List.finRange m) (List.finRange n) w e <
      2 ^ c)
    {h : Heap} (hh : Valid h) {tp rp ep ip cp ap : Ptr}
    (hT : RecordsAt h tp (encodeRibbon W R)) (hr : WordsAt h rp (rangeWords W n))
    (he : ListRep EdgeAt h ep (GraphReachEncoded.edgeWords W left right))
    (hi : WordsAt h ip (GraphReachEncoded.rangeWords W m))
    (hcs : WordsAt h cp ((List.finRange m).map fun e => word c
      (IntegerEdgeCosts.integerCost left right (List.finRange m) (List.finRange n) w e)))
    {acc : List (List (BinaryRational.Word N))} (ha : RowsAt h ap acc)
    (hrep : List.Forall₂ RationalWordRows.RowRep acc
      ((ComputedEmbeddedMatrices.globalRows R).map ComputedKernel.rationalRow)) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q (GraphReachEncoded.setWords W (ExecutableReduction.hardSolve R w ⟨0, hn0⟩)) ∧
      Within code h (initialRegisters [.pointer tp, .pointer rp, .pointer ep, .pointer ip,
          .pointer cp, .pointer ap]) (code ids.stage2) [.pointer q] out
        (stage2Budget W c N n m (ComputedEmbeddedMatrices.globalRows R).length) := by
  have hm0 := edges_pos hnb
  set d := (ComputedEmbeddedMatrices.globalRows R).length with hd
  set G := searchWidth c n m d with hG
  set r := (R.evenRootIndices (EmbeddingFaces.Flag.canonicalOrder m)).length with hrdef
  set cost := IntegerEdgeCosts.integerCost left right (List.finRange m) (List.finRange n) w
    with hcost
  have hr4 : r ≤ 4 * m := by
    simpa [hrdef] using R.evenRow_count_le (EmbeddingFaces.Flag.canonicalOrder m)
  have hfit := fit_lt (n := n) (d := d) hr4 cost hcl
  rw [← hG] at hfit
  have h8m : 8 * m + 1 < 2 ^ G := edges_lt_searchWidth c n m d
  have h2n : 2 * n < 2 ^ G := vertices_lt_searchWidth c n m d
  have hcG : c ≤ G := c_le_searchWidth c n m d
  have hG2 : 2 ≤ G := two_le_searchWidth c n m d
  -- the search constants
  obtain ⟨as, has, hasl⟩ := listRep_listAt ha
  obtain ⟨ts, hts, htsl⟩ := listRep_listAt hT
  obtain ⟨rs, hrs, hrsl⟩ := listRep_listAt hr
  have hal : acc.length = d := by rw [hd, hrep.length_eq, List.length_map]
  have hne : ((List.finRange m).map fun e => word c (cost e)) ≠ [] := by
    simp only [ne_eq, List.map_eq_nil_iff]
    intro h0
    have := congrArg List.length h0
    simp at this; omega
  obtain ⟨o1, zp, op, e1, v1, hz, hone, w1⟩ := searchConsts_compiled code ids.searchConsts
    ids.kernel.dbl ids.kernel.pad ids.kernel.widen hm.searchConsts hm.kernel.dbl hm.kernel.pad
    hm.kernel.widen hh has (by rw [hasl, hal]) hcs hne hts (by simpa using htsl) hrs
    (by simpa using hrsl)
  rw [← hG] at hz hone
  have hone1 : (word G 1).value = 1 := word_value (by omega)
  -- deltas and dimensions
  obtain ⟨o2, dp, dimsP, cols, e2, v2, hcols, hcolv, hdims, w2⟩ :=
    RegisterTranspose.global_compiled R code ids.transpose hm.transpose EdgeAt
      (fun he' _ _ hx => hx.mono he') v1 hG2 (he.mono e1 (fun _ _ hx => hx.mono e1))
      (by simp [GraphReachEncoded.edgeWords]) (ha.mono e1) hrep hz
  obtain ⟨dims, hdl, hdlen⟩ := listRep_listAt hdims
  simp only [List.length_replicate] at hdlen
  -- face columns with keys of width G
  obtain ⟨f3, v3, c3⟩ := alloc_pair v2 (hone.mono e2).allocated (hz.mono e2).allocated
  have hfc : RegisterFaceRow.ConstsAt (word G 1) (Bits.zero G) (o2 ++ [.pair op zp]) o2.length :=
    ⟨op, zp, c3, (hone.mono e2).mono f3, (hz.mono e2).mono f3⟩
  have e13 := e1.trans (e2.trans f3)
  obtain ⟨o4, colsP, rowsP, cntP, ws4, e4, v4, hcolsAt, -, -, hcnt, w4⟩ :=
    FaceStageProgram.stage_compiled ids.kernel.face code hm.kernel.face R hmW (by omega) h8m
      (word G 1) (Bits.zero G) hone1 (Bits.value_zero G) v3 (hT.mono e13) hfc
      ((hone.mono e2).mono f3)
  -- the number of even faces
  obtain ⟨o5, rp5, e5, v5, hr5, w5⟩ := RegisterHalve.shift_compiled code ids.shift hm.shift v4
    hcnt false
  have hrv : (RegisterHalve.shiftRight false (word G (2 * r + 1))).1.value = r := by
    have := RegisterHalve.halve_value (word G (2 * r + 1))
    unfold RegisterHalve.halve at this
    rw [this, word_value (by omega)]
    omega
  -- costs at width G
  have e15 := e13.trans (e4.trans e5)
  obtain ⟨o6, kp, e6, v6, hks, w6⟩ := RegisterResize.resizeList_compiled code
    ids.transpose.resize hm.transpose.resize ids.resizeList hm.resizeList v5 (hcs.mono e15)
    ((hz.mono e2).mono ((f3.trans e4).trans e5))
  have e16 := e15.trans e6
  -- the root word
  obtain ⟨rest, hrest⟩ := RegisterComponentSolve.rangeWords_cons (W := W) hn0
  have hr6 := hr.mono e16
  rw [hrest] at hr6
  obtain ⟨x0, rt, cell, hx0, -⟩ := WordsAt.cons_iff.mp hr6
  obtain ⟨f7, v7, b7⟩ := alloc_bit v6 true (BitsAt.nil v6.1)
  have hone7 : BitsAt (o6 ++ [.bit true 0]) o6.length GraphReachEncoded.one := b7
  have e17 := e16.trans f7
  -- the odd row
  have hnodes : WordsAt (o6 ++ [.bit true 0]) rp (GraphReachEncoded.rangeWords W n) := by
    rw [AllHalfEncoded.rangeWords_eq]; exact hr.mono e17
  obtain ⟨o8, pp, πw, e8, v8, hπw, hπs, w8⟩ := RegisterOddRow.oddRow_compiled code ids.odd hm.odd
    left right ⟨0, hn0⟩ (word G 1) (Bits.zero G) hn hmW (by omega) hone1 (Bits.value_zero G) v7
    (he.mono e17 (fun _ _ hx => hx.mono e17)) (hi.mono e17) hnodes (hx0.mono f7) hone7
    ((hone.mono e2).mono ((((f3.trans e4).trans e5).trans e6).trans f7))
    ((hz.mono e2).mono ((((f3.trans e4).trans e5).trans e6).trans f7))
  have e18 := e17.trans e8
  have e48 := ((((e5.trans e6).trans f7).trans e8))
  -- search inputs
  obtain ⟨D, hDeq, hDv⟩ := exists_matrix SignedWord.value cols
    (fun e i => ComputedEmbeddedMatrices.globalColumn R e i) hcolv
  have hkey : ∀ v, (RegisterFaceColumns.stateKey G r v).value =
      (NodeEncoding.stateEquiv r v).val := by
    intro v
    unfold RegisterFaceColumns.stateKey
    exact word_value (by have := (NodeEncoding.stateEquiv r v).isLt; omega)
  have hK : ∀ e, (Bits.resizeTo G (word c (cost e))).value = cost e := by
    intro e
    rw [Bits.resizeTo_value_of_lt _ (lt_of_lt_of_le (by rw [word_value (hcl e)]; exact hcl e)
      (Nat.pow_le_pow_right (by norm_num) hcG)), word_value (hcl e)]
  have hcolsOf : ListRep (CompiledTemplates.ColumnAt (RegisterFaceColumns.stateKey G r)) o8 colsP
      (List.ofFn (R.computedColumn (EmbeddingFaces.Flag.canonicalOrder m))) := by
    rw [List.ofFn_eq_map]; exact ListRep.mono e48 (fun _ _ hx => hx.mono e48) hcolsAt
  have hdsOf : ListRep (fun heap ptr ds => DeltasAt heap ptr ds) o8 dp
      (List.ofFn (fun e => List.ofFn (D e))) := by
    rw [hDeq]
    exact ListRep.mono ((e4.trans e48)) (fun _ _ hx => hx.mono (e4.trans e48))
      (ListRep.mono f3 (fun _ _ hx => hx.mono f3) hcols)
  have hpisOf : SignedWords.ListAt o8 pp (List.ofFn πw) := by
    rw [List.ofFn_eq_map]; exact hπs
  have hcostsOf : WordsAt o8 kp (List.ofFn fun e => Bits.resizeTo G (word c (cost e))) := by
    rw [List.ofFn_eq_map]
    have := (hks.mono (f7.trans e8))
    rw [List.map_map] at this
    exact this
  -- the search
  obtain ⟨o9, yp, counts, e9, v9, hy, hyv, w9⟩ := RegisterHardSearch.compiled_bound code ids.search
    hm.search (RegisterFaceColumns.stateKey G r) hkey
    (R.computedColumn (EmbeddingFaces.Flag.canonicalOrder m))
    (ComputedEmbeddedMatrices.globalColumn R)
    (ComputedEmbeddedMatrices.computed_matrices_spec R hc hnb).1
    (fun e => (ExecutableReduction.parityRow (left := left) (right := right) ⟨0, hn0⟩ e : ZMod 2))
    cost D hDv πw (fun e => by rw [hπw e]) (fun e => Bits.resizeTo G (word c (cost e))) hK
    hrv hdlen (lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by omega)) hfit)
    (search_reachable R ⟨0, hn0⟩ hc hnb) v8 hcolsOf hdsOf hpisOf hcostsOf
    ((hr5.mono e6).mono (f7.trans e8)) (hdl.mono ((f3.trans e4).trans e48))
    ((hz.mono e2).mono ((f3.trans e4).trans e48))
  -- recovery data
  obtain ⟨yw, hyeq, hywv⟩ := exists_ofFn_map Bits.value counts _ hyv
  have hyw : ∀ e, ((yw e).value : ℤ) = HardSolveReference.hardCounts R w ⟨0, hn0⟩ e := by
    intro e
    simp only [HardSolveReference.hardCounts, ExecutableReduction.hardLabels, Fintype.card_fin]
    rw [hywv e]
  obtain ⟨heven, hthr, hπb, hsum⟩ := RegisterHardRecovery.hard_instance R w ⟨0, hn0⟩ hc hnb hw ho
    πw yw hπw hyw
  have hlen : (ExecutableReduction.hardLabels R w ⟨0, hn0⟩).length ≤
      SparseSearchGraph.entryBound r m d m + 1 := by
    have := HardSolveReference.searchLabels_length_le
      (R.computedColumn (EmbeddingFaces.Flag.canonicalOrder m))
      (ComputedEmbeddedMatrices.globalColumn R)
      (fun e => (ExecutableReduction.parityRow (left := left) (right := right) ⟨0, hn0⟩ e :
        ZMod 2)) (Fintype.card (Fin m)) cost
    simpa only [ExecutableReduction.hardLabels, Fintype.card_fin] using this
  have hB : (3 * n + 1) * (SparseSearchGraph.entryBound r m d m + 1 + 1) < 2 ^ G := by
    refine lt_of_le_of_lt (Nat.mul_le_mul_left _ ?_) hfit
    unfold ExpandedParameters.fitBound
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hwf := RegisterHardRecovery.width_of_bounds πw yw _ hπb (le_of_eq_of_le hsum hlen) hB
  have hyws : WordsAt o9 yp ((List.finRange m).map yw) := by
    rw [← List.ofFn_eq_map, hyeq]; exact hy
  have e19 := e18.trans e9
  have hnodes9 : WordsAt o9 rp (GraphReachEncoded.rangeWords W n) := by
    rw [AllHalfEncoded.rangeWords_eq]; exact hr.mono e19
  obtain ⟨o10, q, e10, v10, hq, w10⟩ := RegisterHardRecovery.compiled code ids.recovery
    hm.recovery left right ⟨0, hn0⟩ πw yw (word G 1) hn hone1 hwf heven v9
    (he.mono e19 (fun _ _ hx => hx.mono e19)) hnodes9 ((hx0.mono f7).mono (e8.trans e9))
    (hπs.mono e9) hyws (hone7.mono (e8.trans e9))
    ((hone.mono e2).mono ((f3.trans e4).trans (e48.trans e9)))
    ((hz.mono e2).mono ((f3.trans e4).trans (e48.trans e9)))
  rw [hthr] at hq
  refine ⟨o10, q, e19.trans e10, v10, hq, ?_⟩
  rw [hm.stage2]
  refine (call_of (by reg_simp) w1 (call_of (by reg_simp) w2
    (Within.allocate (c := .pair op zp) (by reg_simp)
    (call_of (by reg_simp) w4 (call_of (by reg_simp) w5 (call_of (by reg_simp) w6
    (Within.load (pointer := rp) (c := Cell.cons x0 rt) (by reg_simp) cell
    (Within.allocate (c := .bit true 0) (by reg_simp)
    (call_of (by reg_simp) w8 (call_of (by reg_simp) w9 (call_of (by reg_simp) w10
    (ret_values (by reg_simp) le_rfl)))))))))))).mono ?_
  have hpow : (r + m + d + G + 2) ^ 6 ≤ (5 * m + d + G + 2) ^ 6 :=
    Nat.pow_le_pow_left (by omega) 6
  have hsb : 2 ^ 40 * (4 * m + 1) ^ d * (r + m + d + G + 2) ^ 6 ≤
      2 ^ 40 * (4 * m + 1) ^ d * (5 * m + d + G + 2) ^ 6 := Nat.mul_le_mul_left _ hpow
  simp only [stage2Budget, CellExpr.args, List.length_cons, List.length_nil, List.length_map,
    List.length_finRange, ← hG, ← hd] at hsb ⊢
  omega

/-! ## The entry procedure -/

/-- Events of the whole hard-component solver with `n` vertices, `m` edges,
weight width `w0`, word width `W` and `d` global rows. -/
def hardTotal (W w0 n m d : ℕ) : ℕ :=
  edgesBudget m + RegisterEdgeWords.keysBudget m + RegisterEdgeCostProgram.budget W w0 n m +
    RegisterHardKernel.kernelBudget W n m +
    stage2Budget W (NetworkWeights.width w0 n) (ratWidth n m) n m d + 100

/-- The budget of the hard-component solver as a function of its instance. -/
def hardBudget (W w0 : ℕ) : RegisterComponentSolve.HardBudget :=
  fun {n m} {_left _right} R _w =>
    hardTotal W w0 n m (ComputedEmbeddedMatrices.globalRows R).length

theorem keys_eq {W n m : ℕ} {left right : Fin m → Fin n} (R : EmbeddingFaces.Ribbon left right) :
    (encodeRibbon W R).map EdgeRec.key = GraphReachEncoded.rangeWords W m := by
  unfold encodeRibbon GraphReachEncoded.rangeWords
  rw [List.map_map]
  rfl

/-- The compiled hard-component solver satisfies the hard-component contract
for canonical stored weights of any width `w0`. -/
theorem hard_spec (ids : Procedures p) (code : Code p) (hm : ids.Matches code) (W w0 : ℕ) :
    RegisterComponentSolve.HardSpec code ids.hard W (RegisterWeightMask.CanonAt w0)
      (hardBudget W w0) := by
  intro n m left right R w hn0 hn hmW hc hnb hw ho h hh tp rp wp hT hr hwp
  -- endpoint records and index words
  obtain ⟨o1, ep, e1, v1, he, w1⟩ := edges_compiled code ids.edges ids.edgeItem hm.edges
    hm.edgeItem hh hT
  rw [RegisterGraphArcs.edgePairs_encode] at he
  obtain ⟨o2, ip, e2, v2, hi, w2⟩ := RegisterEdgeWords.keys_compiled code ids.keys ids.key
    hm.keys hm.key v1 (hT.mono e1)
  rw [keys_eq] at hi
  have e12 := e1.trans e2
  -- edge costs
  obtain ⟨q, hq, hval, hrow⟩ := exists_row hwp
  have hv : WordsAt o2 rp (GraphReachEncoded.rangeWords W n) := by
    rw [AllHalfEncoded.rangeWords_eq]; exact hr.mono e12
  obtain ⟨o3, cp, zp, e3, v3, hcs, hlt, -, w3⟩ := RegisterEdgeCostProgram.edgeCosts_compiled code
    ids.costs hm.costs hn left right w hw q hq hval v2 hv
    (edgeWordsAt_of (he.mono e2 (fun _ _ hx => hx.mono e2))) (hrow.mono e12)
  -- the kernel
  have e13 := e12.trans e3
  obtain ⟨o4, ap, acc, e4, v4, ha, hrep, w4⟩ := RegisterHardKernel.kernel_compiled ids.kernel code
    hm.kernel R hn hmW v3 (hT.mono e13) (hr.mono e13)
    (he.mono (e2.trans e3) (fun _ _ hx => hx.mono (e2.trans e3))) (hi.mono e3)
  -- the remaining stages
  have e14 := e13.trans e4
  obtain ⟨o5, res, e5, v5, hres, w5⟩ := stage2_compiled ids code hm R w hn0 hn hmW hc hnb hw ho
    hlt v4 (hT.mono e14) (hr.mono e14) (he.mono (e2.trans (e3.trans e4))
      (fun _ _ hx => hx.mono (e2.trans (e3.trans e4)))) ((hi.mono e3).mono e4) (hcs.mono e4)
    ha hrep
  refine ⟨o5, res, e14.trans e5, v5, hres, ?_⟩
  rw [hm.hard]
  refine (call_of (by reg_simp) w1 (call_of (by reg_simp) w2 (call_of (by reg_simp) w3
    (call_of (by reg_simp) w4 (call_of (by reg_simp) w5
    (ret_values (by reg_simp) le_rfl)))))).mono ?_
  simp only [hardBudget, hardTotal, List.length_cons, List.length_nil,
    encodeRibbon_length]
  omega

end WeightedMIS.RegisterHardSolve
