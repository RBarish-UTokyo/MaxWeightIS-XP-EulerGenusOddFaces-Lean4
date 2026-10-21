module

public import WeightedMIS.RegisterRestrictTable
public import WeightedMIS.RegisterWordFilter
public import WeightedMIS.RegisterEdgeWords

/-!
# Stored ribbon tables of induced graphs and of components

From the stored table of a ribbon, the range words of its vertices, a vertex
selection (a per-vertex mask, or a reached word list), and stored weights,
the procedures compute the retained vertex words, the retained edge words,
the restricted and renumbered table, the range words of the local vertices,
and the selected weights. The results are exactly the stored forms of the
executable induced graph `ComputedInduced.ribbon` and of the executable
component `ComputedComponents.componentRibbon`.
-/

@[expose] public section

namespace WeightedMIS.RegisterInducedRibbon

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys
open WeightedMIS.ExpandedWords WeightedMIS.RegisterWordFilter

variable {p : ℕ}

/-! ## Procedures -/

/-- Registers 0 = table, 1 = vertex range words, 3 = weights, 4 = retained
vertex words, 5 = retained edge words. Results: table, local range words,
retained vertex words, selected weights. -/
def tailBody (keys restrict select take : Fin p) : Command p :=
  .call keys [.register 0, .null] [6]
    (.call restrict [.register 0, .register 5, .register 4, .register 6, .register 1] [7]
      (.call select [.register 1, .register 3, .register 4] [8]
        (.call take [.register 1, .register 4, .null] [9]
          (.ret [.register 7, .register 9, .register 4, .register 8]))))

/-- Arguments 0 = table, 1 = vertex range words, 2 = mask, 3 = weights. -/
def inducedBody (mask edges keys restrict select take : Fin p) : Command p :=
  .call mask [.register 1, .register 2] [4]
    (.call edges [.register 0, .register 4] [5] (tailBody keys restrict select take))

/-- Arguments 0 = table, 1 = vertex range words, 2 = reached words, 3 = weights. -/
def componentBody (members edges keys restrict select take : Fin p) : Command p :=
  .call members [.register 1, .register 2] [4]
    (.call edges [.register 0, .register 4] [5] (tailBody keys restrict select take))

structure Procedures (p : ℕ) where
  induced : Fin p
  component : Fin p
  restrict : RegisterRestrictTable.Procedures p
  filter : RegisterWordFilter.Procedures p
  edges : RegisterEdgeWords.Procedures p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.induced = inducedBody ids.filter.mask ids.edges.inducedEdges ids.edges.keys
    ids.restrict.restrict ids.filter.select ids.filter.take ∧
  code ids.component = componentBody ids.filter.members ids.edges.componentEdges ids.edges.keys
    ids.restrict.restrict ids.filter.select ids.filter.take ∧
  ids.restrict.Matches code ∧ ids.filter.Matches code ∧ ids.edges.Matches code

/-- Events after the vertex and edge selection, for `t` records, `ke`
retained edges, `kv` retained vertices, and `kw` weights. -/
def tailBudget (W t ke kv kw : ℕ) : ℕ :=
  RegisterEdgeWords.keysBudget t + RegisterRestrictTable.restrictBudget W t ke kv +
    selectBudget W kv kw + takeBudget kv + 40

def inducedRibbonBudget (W n m : ℕ) : ℕ :=
  maskBudget n + RegisterEdgeWords.inducedBudget W m n + tailBudget W m m n n + 20

def componentRibbonBudget (W n m s : ℕ) : ℕ :=
  membersBudget W s n + RegisterEdgeWords.componentBudget W m n + tailBudget W m m n n + 20

theorem tailBudget_mono {W t ke kv kw ke' kv' : ℕ} (hke : ke ≤ ke') (hkv : kv ≤ kv') :
    tailBudget W t ke kv kw ≤ tailBudget W t ke' kv' kw := by
  simp only [tailBudget, RegisterRestrictTable.restrictBudget, RegisterRestrictTable.tableBudget,
    RegisterRestrictTable.recordBudget, RegisterRestrictTable.endpointsBudget,
    RegisterRestrictCorner.cornersBudget, RegisterRestrictCorner.cornerRBudget,
    RegisterFirstReturn.scanBudget, RegisterFirstReturn.stepBudget,
    RegisterWordAssoc.relabelBudget, RegisterWordAssoc.assocBudget, RegisterMembership.budget,
    selectBudget, takeBudget]
  gcongr

/-! ## Closed-form bounds -/

/-- Monomials of degree at most `(1, 3)` in `(W, N)` are dominated by `W * N ^ 3` and `N ^ 3`. -/
theorem cubic_facts (W N : ℕ) (hN : 1 ≤ N) :
    1 ≤ N ^ 3 ∧ N ≤ N ^ 3 ∧ N ^ 2 ≤ N ^ 3 ∧ W ≤ W * N ^ 3 ∧ W * N ≤ W * N ^ 3 ∧
      W * N ^ 2 ≤ W * N ^ 3 := by
  have h1 : N ≤ N ^ 3 := by nlinarith [Nat.one_le_pow 2 N hN]
  have h2 : N ^ 2 ≤ N ^ 3 := by nlinarith
  have h0 : 1 ≤ N ^ 3 := Nat.one_le_pow 3 N hN
  exact ⟨h0, h1, h2, by nlinarith, Nat.mul_le_mul_left W h1, Nat.mul_le_mul_left W h2⟩

set_option linter.unusedSimpArgs false in
theorem inducedRibbonBudget_le (W n m : ℕ) :
    inducedRibbonBudget W n m ≤ 100000 * (W + 1) * (n + m + 1) ^ 3 := by
  have hmono : inducedRibbonBudget W n m ≤ inducedRibbonBudget W (n + m + 1) (n + m + 1) := by
    simp only [inducedRibbonBudget, componentRibbonBudget, tailBudget,
      RegisterRestrictTable.restrictBudget,
      RegisterRestrictTable.tableBudget, RegisterRestrictTable.recordBudget,
      RegisterRestrictTable.endpointsBudget, RegisterRestrictCorner.cornersBudget,
      RegisterRestrictCorner.cornerRBudget, RegisterFirstReturn.scanBudget,
      RegisterFirstReturn.stepBudget, RegisterRecordLookup.cornerBudget,
      RegisterRecordLookup.findBudget, RegisterWordAssoc.relabelBudget,
      RegisterWordAssoc.assocBudget, RegisterMembership.budget, selectBudget, takeBudget,
      maskBudget, membersBudget, RegisterEdgeWords.inducedBudget,
      RegisterEdgeWords.componentBudget, RegisterEdgeWords.keysBudget]
    gcongr <;> omega
  refine hmono.trans ?_
  have hN : 1 ≤ n + m + 1 := by omega
  generalize n + m + 1 = N at hN ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := cubic_facts W N hN
  simp only [inducedRibbonBudget, componentRibbonBudget, tailBudget,
      RegisterRestrictTable.restrictBudget,
      RegisterRestrictTable.tableBudget, RegisterRestrictTable.recordBudget,
      RegisterRestrictTable.endpointsBudget, RegisterRestrictCorner.cornersBudget,
      RegisterRestrictCorner.cornerRBudget, RegisterFirstReturn.scanBudget,
      RegisterFirstReturn.stepBudget, RegisterRecordLookup.cornerBudget,
      RegisterRecordLookup.findBudget, RegisterWordAssoc.relabelBudget,
      RegisterWordAssoc.assocBudget, RegisterMembership.budget, selectBudget, takeBudget,
      maskBudget, membersBudget, RegisterEdgeWords.inducedBudget,
      RegisterEdgeWords.componentBudget, RegisterEdgeWords.keysBudget]
  ring_nf
  nlinarith

set_option linter.unusedSimpArgs false in
theorem componentRibbonBudget_le (W n m s : ℕ) :
    componentRibbonBudget W n m s ≤ 100000 * (W + 1) * (n + m + s + 1) ^ 3 := by
  have hmono : componentRibbonBudget W n m s ≤
      componentRibbonBudget W (n + m + s + 1) (n + m + s + 1) (n + m + s + 1) := by
    simp only [inducedRibbonBudget, componentRibbonBudget, tailBudget,
      RegisterRestrictTable.restrictBudget,
      RegisterRestrictTable.tableBudget, RegisterRestrictTable.recordBudget,
      RegisterRestrictTable.endpointsBudget, RegisterRestrictCorner.cornersBudget,
      RegisterRestrictCorner.cornerRBudget, RegisterFirstReturn.scanBudget,
      RegisterFirstReturn.stepBudget, RegisterRecordLookup.cornerBudget,
      RegisterRecordLookup.findBudget, RegisterWordAssoc.relabelBudget,
      RegisterWordAssoc.assocBudget, RegisterMembership.budget, selectBudget, takeBudget,
      maskBudget, membersBudget, RegisterEdgeWords.inducedBudget,
      RegisterEdgeWords.componentBudget, RegisterEdgeWords.keysBudget]
    gcongr <;> omega
  refine hmono.trans ?_
  have hN : 1 ≤ n + m + s + 1 := by omega
  generalize n + m + s + 1 = N at hN ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := cubic_facts W N hN
  simp only [inducedRibbonBudget, componentRibbonBudget, tailBudget,
      RegisterRestrictTable.restrictBudget,
      RegisterRestrictTable.tableBudget, RegisterRestrictTable.recordBudget,
      RegisterRestrictTable.endpointsBudget, RegisterRestrictCorner.cornersBudget,
      RegisterRestrictCorner.cornerRBudget, RegisterFirstReturn.scanBudget,
      RegisterFirstReturn.stepBudget, RegisterRecordLookup.cornerBudget,
      RegisterRecordLookup.findBudget, RegisterWordAssoc.relabelBudget,
      RegisterWordAssoc.assocBudget, RegisterMembership.budget, selectBudget, takeBudget,
      maskBudget, membersBudget, RegisterEdgeWords.inducedBudget,
      RegisterEdgeWords.componentBudget, RegisterEdgeWords.keysBudget]
  ring_nf
  nlinarith

/-- The record keys of a ribbon table are the range words of its edges. -/
theorem keys_encode (W : ℕ) {n m : ℕ} {left right : Fin m → Fin n}
    (R : EmbeddingFaces.Ribbon left right) :
    (encodeRibbon W R).map EdgeRec.key = rangeWords W m := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [encodeEdge]

/-! ## The shared tail -/

theorem tail_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {α : Type*} (WeightAt : Heap → Ptr → α → Prop)
    (weightMono : ∀ {h h' : Heap}, Extends h h' →
      ∀ ptr x, WeightAt h ptr x → WeightAt h' ptr x)
    {W n m : ℕ} {h : Heap} (hh : Valid h) (regs : Registers)
    {tp rp wp vp ep : Ptr} {T : List (EdgeRec W)} {ws : List α} {vs es : List (Bits W)}
    (r0 : regs 0 = .pointer tp) (r1 : regs 1 = .pointer rp) (r3 : regs 3 = .pointer wp)
    (r4 : regs 4 = .pointer vp) (r5 : regs 5 = .pointer ep)
    (hT : RecordsAt h tp T) (hkeys : T.map EdgeRec.key = rangeWords W m)
    (hr : WordsAt h rp (rangeWords W n)) (hw : ListRep WeightAt h wp ws)
    (hv : WordsAt h vp vs) (he : WordsAt h ep es)
    (hes : es.length ≤ m) (hvs : vs.length ≤ n) (hws : ws.length ≤ n) :
    ∃ out q l s, Extends h out ∧ Valid out ∧ RecordsAt out q (restrictTable W T es vs) ∧
      WordsAt out l (rangeWords W vs.length) ∧ WordsAt out vp vs ∧
      ListRep WeightAt out s (selectBy vs ws) ∧
      Within code h regs (tailBody ids.edges.keys ids.restrict.restrict ids.filter.select
        ids.filter.take) [.pointer q, .pointer l, .pointer vp, .pointer s] out
        (tailBudget W T.length es.length vs.length ws.length) := by
  obtain ⟨-, -, hrm, hfm, hem⟩ := hm
  obtain ⟨o1, kp, e1, v1, hk, w1⟩ := RegisterEdgeWords.keys_compiled code ids.edges.keys
    ids.edges.key hem.2.2.2.2.2.2.1 hem.2.2.2.2.2.2.2.1 hh hT
  rw [hkeys] at hk
  obtain ⟨o2, q, e2, v2, hq, w2⟩ :=
    RegisterRestrictTable.restrict_compiled ids.restrict code hrm
    v1 (hT.mono e1) (he.mono e1) (hv.mono e1) hk (hr.mono e1) hes hvs
  have e12 := e1.trans e2
  obtain ⟨o3, s, e3, v3, hs, w3⟩ := select_compiled code ids.filter.select ids.filter.mem
    ids.filter.cmp hfm.2.1 hfm.2.2.2.2.2.1 hfm.2.2.2.2.2.2 WeightAt weightMono v2 (hr.mono e12)
    (ListRep.mono e12 (weightMono e12) hw) (hv.mono e12)
  obtain ⟨o4, l, e4, v4, hl, w4⟩ := take_compiled ids.filter code hfm
    (fun h p (w : Bits W) => BitsAt h p w) (fun he _ _ hb => hb.mono he) v3
    ((hr.mono e12).mono e3) ((hv.mono e12).mono e3) hvs
  have e14 := e12.trans (e3.trans e4)
  refine ⟨o4, q, l, s, e14, v4, (hq.mono e3).mono e4, hl, hv.mono e14,
    by rw [selectBy_eq_filter vs ws hws]; exact ListRep.mono e4 (weightMono e4) hs, ?_⟩
  refine (call_of (by reg_simp [r0]) w1 (call_of (by reg_simp [r0, r1, r4, r5]) w2
    (call_of (by reg_simp [r1, r3, r4]) w3 (call_of (by reg_simp [r1, r4]) w4
    (ret_values (by reg_simp [r4]) le_rfl))))).mono ?_
  simp [tailBudget]; omega

theorem inducedBudget_mono {W t kv kv' : ℕ} (h : kv ≤ kv') :
    RegisterEdgeWords.inducedBudget W t kv ≤ RegisterEdgeWords.inducedBudget W t kv' := by
  simp only [RegisterEdgeWords.inducedBudget, RegisterMembership.budget]
  gcongr

theorem componentBudget_mono {W t kv kv' : ℕ} (h : kv ≤ kv') :
    RegisterEdgeWords.componentBudget W t kv ≤ RegisterEdgeWords.componentBudget W t kv' := by
  simp only [RegisterEdgeWords.componentBudget, RegisterMembership.budget]
  gcongr

/-! ## Induced graphs -/

/-- From the stored table of a ribbon, its vertex range words, the stored
retention mask, and stored weights, the procedure produces the stored table
of the executable induced ribbon, the range words of its vertices, the words
of the retained vertices, and the induced weights. -/
theorem induced_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {α : Type*} (WeightAt : Heap → Ptr → α → Prop)
    (weightMono : ∀ {h h' : Heap}, Extends h h' →
      ∀ ptr x, WeightAt h ptr x → WeightAt h' ptr x)
    {W n m : ℕ} (hn : n < 2 ^ W) (hmW : m < 2 ^ W) {left right : Fin m → Fin n}
    (R : EmbeddingFaces.Ribbon left right) (keep : Fin n → Prop) [DecidablePred keep]
    (w : Fin n → α) {h : Heap} (hh : Valid h) {tp rp mp wp : Ptr}
    (hT : RecordsAt h tp (encodeRibbon W R)) (hr : WordsAt h rp (rangeWords W n))
    (hmask : MaskAt h mp (List.ofFn (fun v => decide (keep v))))
    (hw : ListRep WeightAt h wp (List.ofFn w)) :
    ∃ out q l vp s, Extends h out ∧ Valid out ∧
      RecordsAt out q (encodeRibbon W (ComputedInduced.ribbon left right keep R)) ∧
      WordsAt out l (rangeWords W (ComputedInduced.vertices keep).length) ∧
      WordsAt out vp ((ComputedInduced.vertices keep).map (fun v => word W v.val)) ∧
      ListRep WeightAt out s (List.ofFn (fun v => w (ComputedInduced.vertexEquiv keep v).val)) ∧
      Within code h (initialRegisters [.pointer tp, .pointer rp, .pointer mp, .pointer wp])
        (code ids.induced) [.pointer q, .pointer l, .pointer vp, .pointer s] out
        (inducedRibbonBudget W n m) := by
  have hm' := hm
  obtain ⟨hind, -, -, hfm, hem⟩ := hm'
  obtain ⟨o1, vq, e1, v1, hvq, w1⟩ := mask_compiled code ids.filter.mask hfm.1
    (fun h p (w : Bits W) => BitsAt h p w) (fun he _ _ hb => hb.mono he) hh hr hmask
  rw [← maskWords_eq _ (by simp), ← InducedTable.vertices_encode] at hvq
  obtain ⟨o2, eq, e2, v2, heq, w2⟩ := RegisterEdgeWords.inducedEdges_compiled ids.edges code hem
    v1 (hT.mono e1) hvq
  rw [← InducedTable.edges_encode left right keep W hn R] at heq
  have hkv : ((ComputedInduced.vertices keep).map (fun v => word W v.val)).length ≤ n := by
    simpa [ComputedInduced.vertices] using List.length_filter_le _ (List.finRange n)
  have hke :
      ((ComputedInduced.edges left right keep).map (fun e => word W e.val)).length ≤ m := by
    simpa [ComputedInduced.edges] using List.length_filter_le _ (List.finRange m)
  let regs := bindResults (bindResults (initialRegisters [.pointer tp, .pointer rp, .pointer mp,
    .pointer wp]) [4] [.pointer vq]) [5] [.pointer eq]
  have e12 := e1.trans e2
  obtain ⟨out, q, l, s, e3, v3, hq, hl, hv, hs, w3⟩ := tail_compiled ids code hm WeightAt
    weightMono v2 regs (by simp [regs, bindResults, initialRegisters])
    (by simp [regs, bindResults, initialRegisters]) (by simp [regs, bindResults, initialRegisters])
    (by simp [regs, bindResults]) (by simp [regs, bindResults]) (hT.mono e12) (keys_encode W R)
    (hr.mono e12) (ListRep.mono e12 (weightMono e12) hw) (WordsAt.mono e2 hvq) heq hke hkv (by simp)
  rw [← InducedTable.encode_ribbon left right keep W hn hmW R] at hq
  rw [← InducedTable.weights_encode keep W hn w] at hs
  refine ⟨out, q, l, vq, s, e12.trans e3, v3, hq, by simpa using hl, hv, hs, ?_⟩
  rw [hind]
  have hb := tailBudget_mono (W := W) (t := m) (kw := n) hke hkv
  have hi := inducedBudget_mono (W := W) (t := m) hkv
  refine (call_of (by reg_simp) w1 (call_of (by reg_simp) w2 w3)).mono ?_
  simp only [inducedRibbonBudget, encodeRibbon_length, List.length_ofFn] at hb hi ⊢
  simp only [List.length_ofFn, List.length_cons, List.length_nil] at *
  omega

/-! ## Components -/

/-- From the stored table of a ribbon, its vertex range words, a stored list
of the words of the reached vertices of a root, and stored weights, the
procedure produces the stored table of the executable component ribbon, the
range words of its vertices, the words of its vertices, and its weights. -/
theorem component_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {α : Type*} (WeightAt : Heap → Ptr → α → Prop)
    (weightMono : ∀ {h h' : Heap}, Extends h h' →
      ∀ ptr x, WeightAt h ptr x → WeightAt h' ptr x)
    {W n m : ℕ} (hn : n < 2 ^ W) (hmW : m < 2 ^ W) {left right : Fin m → Fin n}
    (R : EmbeddingFaces.Ribbon left right) (root : Fin n) (S : List (Fin n))
    (hS : ∀ v, v ∈ S ↔ v ∈ (ComputedComponents.routes left right root).seen)
    (w : Fin n → α) {h : Heap} (hh : Valid h) {tp rp sp wp : Ptr}
    (hT : RecordsAt h tp (encodeRibbon W R)) (hr : WordsAt h rp (rangeWords W n))
    (hsw : WordsAt h sp (S.map (fun v => word W v.val)))
    (hw : ListRep WeightAt h wp (List.ofFn w)) :
    ∃ out q l vp s, Extends h out ∧ Valid out ∧
      RecordsAt out q (encodeRibbon W (ComputedComponents.componentRibbon left right root R)) ∧
      WordsAt out l (rangeWords W (ComputedComponents.vertices left right root).length) ∧
      WordsAt out vp ((ComputedComponents.vertices left right root).map (fun v => word W v.val)) ∧
      ListRep WeightAt out s
        (List.ofFn (fun v => w (ComputedComponents.vertexEquiv left right root v).val)) ∧
      Within code h (initialRegisters [.pointer tp, .pointer rp, .pointer sp, .pointer wp])
        (code ids.component) [.pointer q, .pointer l, .pointer vp, .pointer s] out
        (componentRibbonBudget W n m S.length) := by
  have hm' := hm
  obtain ⟨-, hcomp, -, hfm, hem⟩ := hm'
  obtain ⟨o1, vq, e1, v1, hvq, w1⟩ := members_memberWords ids.filter code hfm hh hr hsw
  rw [← ComponentTable.vertices_encode left right root W hn S hS] at hvq
  obtain ⟨o2, eq, e2, v2, heq, w2⟩ := RegisterEdgeWords.componentEdges_compiled ids.edges code
    hem v1 (hT.mono e1) hvq
  rw [← ComponentTable.edges_encode left right root W hn R] at heq
  have hkv : ((ComputedComponents.vertices left right root).map
      (fun v => word W v.val)).length ≤ n := by
    simpa using ComputedComponents.vertices_length_le left right root
  have hke : ((ComputedComponents.edges left right root).map
      (fun e => word W e.val)).length ≤ m := by
    simpa using ComputedComponents.edges_length_le left right root
  let regs := bindResults (bindResults (initialRegisters [.pointer tp, .pointer rp, .pointer sp,
    .pointer wp]) [4] [.pointer vq]) [5] [.pointer eq]
  have e12 := e1.trans e2
  obtain ⟨out, q, l, s, e3, v3, hq, hl, hv, hs, w3⟩ := tail_compiled ids code hm WeightAt
    weightMono v2 regs (by simp [regs, bindResults, initialRegisters])
    (by simp [regs, bindResults, initialRegisters]) (by simp [regs, bindResults, initialRegisters])
    (by simp [regs, bindResults]) (by simp [regs, bindResults]) (hT.mono e12) (keys_encode W R)
    (hr.mono e12) (ListRep.mono e12 (weightMono e12) hw) (WordsAt.mono e2 hvq) heq hke hkv (by simp)
  rw [← ComponentTable.encode_componentRibbon left right root W hn hmW R] at hq
  rw [← ComponentTable.weights_encode left right root W hn w] at hs
  refine ⟨out, q, l, vq, s, e12.trans e3, v3, hq, by simpa using hl, hv, hs, ?_⟩
  rw [hcomp]
  have hb := tailBudget_mono (W := W) (t := m) (kw := n) hke hkv
  have hi := componentBudget_mono (W := W) (t := m) hkv
  refine (call_of (by reg_simp) w1 (call_of (by reg_simp) w2 w3)).mono ?_
  simp only [componentRibbonBudget, encodeRibbon_length, List.length_ofFn, List.length_map]
    at hb hi ⊢
  simp only [List.length_ofFn, List.length_cons, List.length_nil, List.length_map] at *
  omega

end WeightedMIS.RegisterInducedRibbon
