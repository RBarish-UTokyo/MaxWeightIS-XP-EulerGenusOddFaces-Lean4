module

public import WeightedMIS.RegisterInducedRibbon
public import WeightedMIS.RegisterComponentRoots
public import WeightedMIS.RegisterListReverse
public import WeightedMIS.AllHalfEncoded

/-!
# Solving one computed component

For a root word, the procedure runs the adjacency search, builds the stored
table, range words, vertex words and weights of the component ribbon, and
solves the component locally: it builds the parity arcs and parity vertex
words, runs the parity search from the even copy of local vertex `0`, and
tests the odd copy. If it is reached, the compiled hard-component solver is
called; otherwise the color class of the even copies is filtered from the
local range words. The local result words are read back to original vertex
words and prepended (reversed) to an accumulator.

The hard-component solver is a parameter: `HardSpec` is the contract of a
procedure that returns the stored words of `ExecutableReduction.hardSolve` on
every connected nonbipartite all-half input with nonnegative weights, within
a budget `hb R w`.
-/

@[expose] public section

namespace WeightedMIS.RegisterComponentSolve

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys
open WeightedMIS.ExpandedWords WeightedMIS.ResidualWords WeightedMIS.EmbeddingFaces
open WeightedMIS.GraphReachEncoded (one reachE parityReachE colorWordsE adjArcs parityArcs
  parityNodeWords parityWord edgeWords setWords)

variable {p : ℕ}

/-! ## The hard-component contract -/

/-- Budgets of a hard-component solver, as a function of its input. -/
abbrev HardBudget : Type :=
  ∀ {n m : ℕ} {left right : Fin m → Fin n}, Ribbon left right → (Fin n → ℚ) → ℕ

/-- The procedure `hard`, called with the stored table, the vertex range words
and the stored weights of a connected nonbipartite all-half instance with
nonnegative weights, returns the stored words of the actual
`ExecutableReduction.hardSolve` output at the canonical root, within `hb R w`. -/
def HardSpec (code : Code p) (hard : Fin p) (W : ℕ) (WeightAt : Heap → Ptr → ℚ → Prop)
    (hb : HardBudget) : Prop :=
  ∀ {n m : ℕ} {left right : Fin m → Fin n} (R : Ribbon left right) (w : Fin n → ℚ) (hn : 0 < n),
    n < 2 ^ W → m < 2 ^ W → Incidence.Connected left right → ¬Incidence.Bipartite left right →
    (∀ v, 0 ≤ w v) → Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2) →
    ∀ {h : Heap}, Valid h → ∀ {tp rp wp : Ptr}, RecordsAt h tp (encodeRibbon W R) →
      WordsAt h rp (rangeWords W n) → ListRep WeightAt h wp (List.ofFn w) →
      ∃ out q, Extends h out ∧ Valid out ∧
        WordsAt out q (setWords W (ExecutableReduction.hardSolve R w ⟨0, hn⟩)) ∧
        Within code h (initialRegisters [.pointer tp, .pointer rp, .pointer wp]) (code hard)
          [.pointer q] out (hb R w)

/-! ## Representations -/

/-- The shared context of the component loop:
`pair table (pair range (pair weights (pair adjacencyArcs one)))`. -/
def CtxAt (WeightAt : Heap → Ptr → ℚ → Prop) (W : ℕ) {n m : ℕ} {left right : Fin m → Fin n}
    (H : Ribbon left right) (w : Fin n → ℚ) (h : Heap) (ptr : Ptr) : Prop :=
  ∃ tp a1 rp a2 wp a3 ap op, h[ptr]? = some (.pair tp a1) ∧ h[a1]? = some (.pair rp a2) ∧
    h[a2]? = some (.pair wp a3) ∧ h[a3]? = some (.pair ap op) ∧
    RecordsAt h tp (encodeRibbon W H) ∧ WordsAt h rp (rangeWords W n) ∧
    ListRep WeightAt h wp (List.ofFn w) ∧ TableAt h ap (adjArcs (edgeWords W left right)) ∧
    BitsAt h op one

theorem CtxAt.mono {WeightAt : Heap → Ptr → ℚ → Prop}
    (weightMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, WeightAt h ptr x → WeightAt h' ptr x)
    {W n m : ℕ} {left right : Fin m → Fin n} {H : Ribbon left right} {w : Fin n → ℚ}
    {h h' : Heap} (he : Extends h h') {ptr : Ptr} (hc : CtxAt WeightAt W H w h ptr) :
    CtxAt WeightAt W H w h' ptr := by
  obtain ⟨tp, a1, rp, a2, wp, a3, ap, op, c1, c2, c3, c4, hT, hr, hw, ha, ho⟩ := hc
  exact ⟨tp, a1, rp, a2, wp, a3, ap, op, he.lookup c1, he.lookup c2, he.lookup c3, he.lookup c4,
    hT.mono he, hr.mono he, ListRep.mono he (weightMono he) hw, ha.mono he, ho.mono he⟩

/-! ## Procedures -/

/-- Arguments 0 = local vertex word, 1 = reached parity words. -/
def colorItemBody (member : Fin p) : Command p :=
  .allocate 2 (.bit (.flag true) (.register 0))
    (.call member [.register 2, .register 1] [3]
      (.branch (.register 3) (.ret [.flag false]) (.ret [.flag true])))

/-- Arguments 0 = table, 1 = range words, 2 = weights, 3 = unit word. -/
def localBody (parityArcs parityNodes search member hard color : Fin p) : Command p :=
  .call parityArcs [.register 0, .register 3, .null] [4]
    (.call parityNodes [.register 1, .null, .null] [5]
      (.load (.register 1) 6 7 15 { CompiledTrie.failCases with
        cons := .allocate 8 (.bit (.flag false) (.register 6))
          (.call search [.register 4, .register 3, .register 5, .register 8] [9, 10]
            (.allocate 11 (.bit (.flag true) (.register 6))
              (.call member [.register 11, .register 9] [12]
                (.branch (.register 12)
                  (.call hard [.register 0, .register 1, .register 2] [13] (.ret [.register 13]))
                  (.call color [.register 1, .register 9] [13] (.ret [.register 13])))))) }))

/-- Arguments 0 = root word, 1 = context, 2 = accumulated words. -/
def itemBody (search component localSolve select reverse : Fin p) : Command p :=
  .load (.register 1) 3 4 15 { CompiledTrie.failCases with
    pair := .load (.register 4) 5 6 15 { CompiledTrie.failCases with
      pair := .load (.register 6) 7 8 15 { CompiledTrie.failCases with
        pair := .load (.register 8) 9 10 15 { CompiledTrie.failCases with
          pair := .call search [.register 9, .register 10, .register 5, .register 0] [11, 12]
            (.call component [.register 3, .register 5, .register 11, .register 7] [3, 5, 7, 12]
              (.call localSolve [.register 3, .register 5, .register 12, .register 10] [13]
                (.call select [.register 5, .register 7, .register 13] [14]
                  (.call reverse [.register 14, .register 2] [15]
                    (.ret [.register 15]))))) } } } }

structure Procedures (p : ℕ) where
  item : Fin p
  localSolve : Fin p
  color : Fin p
  colorItem : Fin p
  reverse : Fin p
  hard : Fin p
  roots : RegisterComponentRoots.Procedures p
  arcs : RegisterGraphArcs.Procedures p
  induced : RegisterInducedRibbon.Procedures p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.item = itemBody ids.roots.search ids.induced.component ids.localSolve
    ids.induced.filter.select ids.reverse ∧
  code ids.localSolve = localBody ids.arcs.parityArcs ids.arcs.parityNodes ids.roots.search
    ids.roots.residual.member ids.hard ids.color ∧
  code ids.color = RegisterListFilter.body ids.color ids.colorItem ∧
  code ids.colorItem = colorItemBody ids.roots.residual.member ∧
  code ids.reverse = RegisterListReverse.body ids.reverse ∧
  ids.roots.Matches code ∧ ids.arcs.Matches code ∧ ids.induced.Matches code

/-! ## Budgets -/

def colorBudget (W k : ℕ) : ℕ := (RegisterMembership.budget (W + 1) (2 * k + 1) + 95) * k + 13

/-- Events of the local solver apart from the hard call, for `k` vertices and
`ke` edges. -/
def localBudget (W k ke : ℕ) : ℕ :=
  RegisterGraphArcs.parityBudget ke + RegisterGraphArcs.nodesBudget k +
    RegisterResidualSearch.budget (W + 1) 1 (4 * ke) (2 * k) +
    RegisterMembership.budget (W + 1) (2 * k + 1) + colorBudget W k + 120

/-- Events of one component apart from its hard call, on a graph with `n`
vertices and `m` edges. -/
def itemBudget (W n m : ℕ) : ℕ :=
  RegisterResidualSearch.budget W 1 (2 * m) n +
    RegisterInducedRibbon.componentRibbonBudget W n m (n + 1) + localBudget W n m +
    RegisterWordFilter.selectBudget W n n + 26 * n + 120

theorem searchBudget_mono {k b a a' x x' : ℕ} (ha : a ≤ a') (hx : x ≤ x') :
    RegisterResidualSearch.budget k b a x ≤ RegisterResidualSearch.budget k b a' x' := by
  simp only [RegisterResidualSearch.budget, RegisterResidualReach.budget,
    RegisterResidualReach.stepBudget, RegisterResidualCrossing.budget,
    RegisterResidualPredicate.budget, RegisterMembership.budget, RegisterRouteLookup.budget]
  gcongr

theorem membershipBudget_mono {k x x' : ℕ} (hx : x ≤ x') :
    RegisterMembership.budget k x ≤ RegisterMembership.budget k x' := by
  simp only [RegisterMembership.budget]
  gcongr

theorem localBudget_mono {W k ke k' ke' : ℕ} (hk : k ≤ k') (hke : ke ≤ ke') :
    localBudget W k ke ≤ localBudget W k' ke' := by
  have h1 := searchBudget_mono (k := W + 1) (b := 1) (Nat.mul_le_mul_left 4 hke)
    (Nat.mul_le_mul_left 2 hk)
  have h2 := membershipBudget_mono (k := W + 1) (show 2 * k + 1 ≤ 2 * k' + 1 by omega)
  simp only [localBudget, colorBudget, RegisterGraphArcs.parityBudget,
    RegisterGraphArcs.nodesBudget]
  gcongr

/-! ## Words -/

theorem rangeWords_cons {W k : ℕ} (hk : 0 < k) :
    ∃ rest, rangeWords W k = word W 0 :: rest := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact ⟨_, by rw [rangeWords, List.range_succ_eq_map, List.map_cons]⟩

theorem exists_map_word {W n : ℕ} (l : List (Bits W))
    (hl : ∀ x ∈ l, ∃ v : Fin n, x = word W v.val) :
    ∃ S : List (Fin n), l = S.map (fun v => word W v.val) := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons x l ih =>
    obtain ⟨v, rfl⟩ := hl x List.mem_cons_self
    obtain ⟨S, rfl⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    exact ⟨v :: S, rfl⟩

theorem colorItem_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {vp sp : Ptr} {v : Bits W} {seen : List (Bits (W + 1))}
    (hv : BitsAt h vp v) (hs : WordsAt h sp seen) :
    ∃ out, Extends h out ∧ Valid out ∧
      Within code h (initialRegisters [.pointer vp, .pointer sp]) (code ids.colorItem)
        [.flag (!RegisterMembership.found (parityWord true v) seen)] out
        (RegisterMembership.budget (W + 1) seen.length + 30) := by
  obtain ⟨-, -, -, hitem, -, hroots, -, -⟩ := hm
  obtain ⟨-, -, -, -, -, hres⟩ := hroots
  obtain ⟨e1, v1, b1⟩ := alloc_bit hh true hv
  have hmem := RegisterMembership.compiled code ids.roots.residual.member ids.roots.residual.cmp
    hres.2.2.2.1 hres.2.2.2.2.2.2.2 b1 (hs.mono e1)
  change Within code _ _ _ [.flag (RegisterMembership.found (parityWord true v) seen)] _ _ at hmem
  refine ⟨_, e1, v1, ?_⟩
  rw [hitem]
  cases hf : RegisterMembership.found (parityWord true v) seen <;> rw [hf] at hmem
  · refine (Within.allocate (c := Cell.bit true vp) (by reg_simp)
      (call_of (by reg_simp) hmem
      (Within.branch (b := false) (by reg_simp) (ret_values (by reg_simp) le_rfl)))).mono ?_
    simp [CellExpr.args]; omega
  · refine (Within.allocate (c := Cell.bit true vp) (by reg_simp)
      (call_of (by reg_simp) hmem
      (Within.branch (b := true) (by reg_simp) (ret_values (by reg_simp) le_rfl)))).mono ?_
    simp [CellExpr.args]; omega

theorem color_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W k : ℕ} {h : Heap} (hh : Valid h) {rp sp : Ptr} {seen : List (Bits (W + 1))}
    (hr : WordsAt h rp (rangeWords W k)) (hs : WordsAt h sp seen) (hlen : seen.length ≤ 2 * k + 1) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (colorWordsE seen (rangeWords W k)) ∧
      Within code h (initialRegisters [.pointer rp, .pointer sp]) (code ids.color)
        [.pointer q] out (colorBudget W k) := by
  have hm' := hm
  obtain ⟨-, -, hcolor, -⟩ := hm'
  obtain ⟨out, q, he, hv, hq, hw⟩ := RegisterListFilter.compiled_const code ids.color
    ids.colorItem hcolor (fun h p (w : Bits W) => BitsAt h p w) WordsAt
    (fun he _ _ hb => hb.mono he) (fun he _ _ hb => hb.mono he)
    (fun seen v => !RegisterMembership.found (parityWord true v) seen)
    (RegisterMembership.budget (W + 1) seen.length + 30) hh hr hs
    (fun hv' _ _ _ hx hd => colorItem_compiled ids code hm hv' hx hd)
  refine ⟨out, q, he, hv, hq, hw.mono ?_⟩
  have := membershipBudget_mono (k := W + 1) hlen
  simp only [colorBudget, rangeWords_length]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right k (by omega)) _

theorem parityNodeWords_length {W : ℕ} (nodes : List (Bits W)) :
    (parityNodeWords nodes).length = 2 * nodes.length :=
  RegisterComponentRoots.length_flatMap_const _ _ 2 (fun _ => rfl)

theorem parityArcs_length {W : ℕ} (edges : List (Bits W × Bits W)) :
    (parityArcs edges).length = 4 * edges.length :=
  RegisterComponentRoots.length_flatMap_const _ _ 4 (fun _ => rfl)

theorem adjArcs_length {W : ℕ} (edges : List (Bits W × Bits W)) :
    (adjArcs edges).length = 2 * edges.length :=
  RegisterComponentRoots.length_flatMap_const _ _ 2 (fun _ => rfl)

/-! ## The local solver -/

/-- From the stored table, range words and weights of a connected all-half
graph with nonnegative weights, the procedure returns the stored words of the
canonical-root solver `halfSolve`. -/
theorem local_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} (WeightAt : Heap → Ptr → ℚ → Prop)
    (weightMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, WeightAt h ptr x → WeightAt h' ptr x)
    (hb : HardBudget) (hard : HardSpec code ids.hard W WeightAt hb)
    {k ke : ℕ} (hk : k < 2 ^ W) (hke : ke < 2 ^ W) (hk0 : 0 < k) {left right : Fin ke → Fin k}
    (R : Ribbon left right) (w : Fin k → ℚ) (hc : Incidence.Connected left right)
    (hw : ∀ v, 0 ≤ w v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2))
    {h : Heap} (hh : Valid h) {tp rp wp op : Ptr}
    (hT : RecordsAt h tp (encodeRibbon W R)) (hr : WordsAt h rp (rangeWords W k))
    (hwp : ListRep WeightAt h wp (List.ofFn w)) (hop : BitsAt h op one) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q (setWords W (ExecutableReduction.halfSolve R w ⟨0, hk0⟩)) ∧
      Within code h (initialRegisters [.pointer tp, .pointer rp, .pointer wp, .pointer op])
        (code ids.localSolve) [.pointer q] out (localBudget W k ke + hb R w) := by
  have hm' := hm
  obtain ⟨-, hlocal, -, -, -, hroots, harcs, -⟩ := hm'
  have hroots' := hroots
  obtain ⟨-, -, -, -, -, hres⟩ := hroots'
  obtain ⟨o1, pa, e1, v1, hpa, w1⟩ :=
    RegisterGraphArcs.parityArcs_compiled ids.arcs code harcs hh hT hop
  rw [RegisterGraphArcs.edgePairs_encode] at hpa
  obtain ⟨o2, pn, e2, v2, hpn, w2⟩ :=
    RegisterGraphArcs.parityNodes_compiled ids.arcs code harcs v1 (hr.mono e1)
  have e12 := e1.trans e2
  obtain ⟨rest, hrest⟩ := rangeWords_cons (W := W) hk0
  have hr2 := hr.mono e12
  rw [hrest] at hr2
  obtain ⟨x0, rt, cell, hx0, -⟩ := WordsAt.cons_iff.mp hr2
  obtain ⟨e3, v3, b3⟩ := alloc_bit v2 false hx0
  obtain ⟨o4, ps, rtp, e4, v4, hps, w4⟩ := RegisterComponentRoots.search_compiled ids.roots code
    hroots v3 ((hpa.mono e2).mono e3) ((hop.mono e12).mono e3) (hpn.mono e3) b3
  change WordsAt o4 ps (parityReachE (edgeWords W left right) (rangeWords W k) (word W 0)) at hps
  obtain ⟨e5, v5, b5⟩ := alloc_bit v4 true ((hx0.mono e3).mono e4)
  have w6 := RegisterMembership.compiled code ids.roots.residual.member ids.roots.residual.cmp
    hres.2.2.2.1 hres.2.2.2.2.2.2.2 b5 (hps.mono e5)
  change Within code _ _ _
    [.flag (RegisterMembership.found (parityWord true (word W 0))
      (parityReachE (edgeWords W left right) (rangeWords W k) (word W 0)))] _ _ at w6
  have hpf := GraphReachEncoded.parity_found_iff left right hk ⟨0, hk0⟩ ⟨0, hk0⟩ true
  rw [AllHalfEncoded.rangeWords_eq] at hpf
  change RegisterMembership.found (parityWord true (word W 0))
      (parityReachE (edgeWords W left right) (rangeWords W k) (word W 0)) = true ↔ _ at hpf
  have hlen := RegisterComponentRoots.reachE_length (parityArcs (edgeWords W left right))
    (parityNodeWords (rangeWords W k)) (parityWord false (word W 0))
  rw [parityNodeWords_length, rangeWords_length] at hlen
  change (parityReachE (edgeWords W left right) (rangeWords W k) (word W 0)).length ≤
    2 * k + 1 at hlen
  have hpaLen : (parityArcs (edgeWords W left right)).length = 4 * ke := by
    rw [parityArcs_length]; simp [edgeWords]
  have hpnLen : (parityNodeWords (rangeWords W k)).length = 2 * k := by
    rw [parityNodeWords_length, rangeWords_length]
  have hmb := membershipBudget_mono (k := W + 1) hlen
  have e15 := (((e12.trans e3).trans e4).trans e5)
  by_cases hseen : ((⟨0, hk0⟩ : Fin k), true) ∈
      (ComputedOddRow.paritySearch left right (List.finRange ke) (List.finRange k) ⟨0, hk0⟩).seen
  · have hf := hpf.mpr hseen
    rw [hf] at w6
    obtain ⟨out, q, e6, v6, hq, wH⟩ := hard R w hk0 hk hke hc
      (ComputedOddRow.nonbipartite_of_seen left right (List.finRange ke) (List.finRange k)
        (fun v => List.mem_finRange v) ⟨0, hk0⟩ hseen) hw ho v5 (hT.mono e15) (hr.mono e15)
      (ListRep.mono e15 (weightMono e15) hwp)
    refine ⟨out, q, e15.trans e6, v6, ?_, ?_⟩
    · simpa only [ExecutableReduction.halfSolve, hseen, ↓reduceIte] using hq
    rw [hlocal]
    refine (call_of (by reg_simp) w1 (call_of (by reg_simp) w2
      (Within.load (pointer := rp) (c := Cell.cons x0 rt) (by reg_simp) cell
      (Within.allocate (c := Cell.bit false x0) (by reg_simp)
      (call_of (by reg_simp) w4
      (Within.allocate (c := Cell.bit true x0) (by reg_simp)
      (call_of (by reg_simp) w6
      (Within.branch (b := true) (by reg_simp)
      (call_of (by reg_simp) wH (ret_values (by reg_simp) le_rfl)))))))))).mono ?_
    simp only [localBudget, hpaLen, hpnLen, CellExpr.args, List.length_cons, List.length_nil,
      encodeRibbon_length, rangeWords_length]
    omega
  · have hf : RegisterMembership.found (parityWord true (word W 0))
        (parityReachE (edgeWords W left right) (rangeWords W k) (word W 0)) = false := by
      rw [← Bool.not_eq_true, hpf]; exact hseen
    rw [hf] at w6
    obtain ⟨out, q, e6, v6, hq, wC⟩ := color_compiled ids code hm v5 (hr.mono e15)
      (hps.mono e5) hlen
    have hcol := GraphReachEncoded.colorClass_encode left right hk ⟨0, hk0⟩
    rw [AllHalfEncoded.rangeWords_eq] at hcol
    change colorWordsE (parityReachE (edgeWords W left right) (rangeWords W k) (word W 0))
      (rangeWords W k) = _ at hcol
    refine ⟨out, q, e15.trans e6, v6, ?_, ?_⟩
    · simp only [ExecutableReduction.halfSolve, hseen, ↓reduceIte]
      rw [← hcol]
      exact hq
    rw [hlocal]
    refine (call_of (by reg_simp) w1 (call_of (by reg_simp) w2
      (Within.load (pointer := rp) (c := Cell.cons x0 rt) (by reg_simp) cell
      (Within.allocate (c := Cell.bit false x0) (by reg_simp)
      (call_of (by reg_simp) w4
      (Within.allocate (c := Cell.bit true x0) (by reg_simp)
      (call_of (by reg_simp) w6
      (Within.branch (b := false) (by reg_simp)
      (call_of (by reg_simp) wC (ret_values (by reg_simp) le_rfl)))))))))).mono ?_
    simp only [localBudget, hpaLen, hpnLen, CellExpr.args, List.length_cons, List.length_nil,
      encodeRibbon_length, rangeWords_length]
    omega

/-! ## One component -/

/-- The hard budget charged to the component of `root`. -/
def componentHardBudget (hb : HardBudget) {n m : ℕ} {left right : Fin m → Fin n}
    (H : Ribbon left right) (w : Fin n → ℚ) (root : Fin n) : ℕ :=
  hb (ComputedComponents.componentRibbon left right root H)
    (AllHalfEncoded.localWeights left right w root)

theorem componentRibbonBudget_mono {W n m s s' : ℕ} (hs : s ≤ s') :
    RegisterInducedRibbon.componentRibbonBudget W n m s ≤
      RegisterInducedRibbon.componentRibbonBudget W n m s' := by
  have := membershipBudget_mono (k := W) hs
  simp only [RegisterInducedRibbon.componentRibbonBudget, RegisterWordFilter.membersBudget]
  gcongr

theorem selectBudget_mono {W k k' l l' : ℕ} (hk : k ≤ k') (hl : l ≤ l') :
    RegisterWordFilter.selectBudget W k l ≤ RegisterWordFilter.selectBudget W k' l' := by
  have := membershipBudget_mono (k := W) hk
  simp only [RegisterWordFilter.selectBudget]
  gcongr

/-- For a root word and the shared context, the procedure prepends the
reversed original words of the solved component of the root. -/
theorem item_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} (WeightAt : Heap → Ptr → ℚ → Prop)
    (weightMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, WeightAt h ptr x → WeightAt h' ptr x)
    (hb : HardBudget) (hard : HardSpec code ids.hard W WeightAt hb)
    {n m : ℕ} (hn : n < 2 ^ W) (hmW : m < 2 ^ W) {left right : Fin m → Fin n}
    (H : Ribbon left right) (w : Fin n → ℚ) (hw : ∀ v, 0 ≤ w v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2))
    (r : Fin n) {h : Heap} (hh : Valid h) {xp dp acc : Ptr} {as : List (Bits W)}
    (hx : BitsAt h xp (word W r.val)) (hd : CtxAt WeightAt W H w h dp) (ha : WordsAt h acc as) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (AllHalfEncoded.step W H w as r) ∧
      Within code h (initialRegisters [.pointer xp, .pointer dp, .pointer acc]) (code ids.item)
        [.pointer q] out (itemBudget W n m + componentHardBudget hb H w r) := by
  have hm' := hm
  obtain ⟨hitem, -, -, -, hrev, hroots, -, hind⟩ := hm'
  have hind' := hind
  obtain ⟨-, -, -, hfm, -⟩ := hind'
  obtain ⟨tp, a1, rp, a2, wp, a3, ap, op, c1, c2, c3, c4, hT, hr, hwp, hap, hop⟩ := hd
  -- the reached words of the root
  obtain ⟨o1, sp, rtp, e1, v1, hseen, w1⟩ :=
    RegisterComponentRoots.search_compiled ids.roots code hroots hh hap hop hr hx
  have hmemr : ∀ x ∈ reachE (adjArcs (edgeWords W left right)) (rangeWords W n) (word W r.val),
      ∃ v : Fin n, x = word W v.val := by
    intro x hx'
    rw [← AllHalfEncoded.rangeWords_eq] at hx'
    obtain ⟨v, rfl, -⟩ := GraphReachEncoded.mem_reach left right hn r x hx'
    exact ⟨v, rfl⟩
  obtain ⟨S, hSeq⟩ := exists_map_word _ hmemr
  have hS : ∀ v, v ∈ S ↔ v ∈ (ComputedComponents.routes left right r).seen := by
    intro v
    rw [← GraphReachEncoded.found_reach_iff left right hn r v, ResidualListReach.found_iff_mem,
      AllHalfEncoded.rangeWords_eq]
    change v ∈ S ↔ word W v.val ∈ reachE (adjArcs (edgeWords W left right)) (rangeWords W n)
      (word W r.val)
    rw [hSeq, mem_map_word hn]
  have hSlen : S.length ≤ n + 1 := by
    have := RegisterComponentRoots.reachE_length (adjArcs (edgeWords W left right))
      (rangeWords W n) (word W r.val)
    rw [hSeq, List.length_map, rangeWords_length] at this
    exact this
  rw [hSeq] at hseen
  -- the component ribbon
  obtain ⟨o2, q, l, vp, s, e2, v2, hq, hl, hvp, hs, w2⟩ :=
    RegisterInducedRibbon.component_compiled ids.induced code hind WeightAt weightMono hn hmW H r
      S hS w v1 (hT.mono e1) (hr.mono e1) hseen (ListRep.mono e1 (weightMono e1) hwp)
  have e12 := e1.trans e2
  -- the local solver
  have hk : (ComputedComponents.vertices left right r).length < 2 ^ W :=
    lt_of_le_of_lt (ComputedComponents.vertices_length_le left right r) hn
  have hke : (ComputedComponents.edges left right r).length < 2 ^ W :=
    lt_of_le_of_lt (ComputedComponents.edges_length_le left right r) hmW
  obtain ⟨o3, lw, e3, v3, hlw, w3⟩ := local_compiled ids code hm WeightAt weightMono hb hard hk hke
    (ComputedComponents.vertices_length_pos left right r)
    (ComputedComponents.componentRibbon left right r H) (AllHalfEncoded.localWeights left right w r)
    (ComputedComponents.local_connected left right r) (fun v => hw _)
    (ComputedComponents.local_half_optimal left right r w ho) v2 hq hl hs (hop.mono e12)
  rw [← AllHalfEncoded.localSolve_eq] at hlw
  -- reading back the original words
  obtain ⟨o4, sel, e4, v4, hsel, w4⟩ := RegisterWordFilter.select_compiled code
    ids.induced.filter.select ids.induced.filter.mem ids.induced.filter.cmp hfm.2.1
    hfm.2.2.2.2.2.1 hfm.2.2.2.2.2.2 (fun h p (w : Bits W) => BitsAt h p w)
    (fun he _ _ hb => hb.mono he) v3 (hl.mono e3) (hvp.mono e3) hlw
  -- prepending to the accumulator
  have e14 := (e12.trans e3).trans e4
  obtain ⟨o5, q5, e5, v5, hq5, w5⟩ := RegisterListReverse.compiled code ids.reverse hrev
    (fun h p (w : Bits W) => BitsAt h p w) (fun he _ _ hb => hb.mono he) v4 hsel (ha.mono e14)
  refine ⟨o5, q5, e14.trans e5, v5, hq5, ?_⟩
  rw [hitem]
  refine (Within.load (pointer := dp) (c := Cell.pair tp a1) (by reg_simp) c1
    (Within.load (pointer := a1) (c := Cell.pair rp a2) (by reg_simp) c2
    (Within.load (pointer := a2) (c := Cell.pair wp a3) (by reg_simp) c3
    (Within.load (pointer := a3) (c := Cell.pair ap op) (by reg_simp) c4
    (call_of (by reg_simp) w1 (call_of (by reg_simp) w2 (call_of (by reg_simp) w3
    (call_of (by reg_simp) w4 (call_of (by reg_simp) w5
    (ret_values (by reg_simp) le_rfl)))))))))).mono ?_
  have hb1 := componentRibbonBudget_mono (W := W) (n := n) (m := m) hSlen
  have hb2 := localBudget_mono (W := W) (ComputedComponents.vertices_length_le left right r)
    (ComputedComponents.edges_length_le left right r)
  have hks := AllHalfEncoded.setWords_length_le (W := W)
    (AllHalfEncoded.localSolve H w r)
  have hb3 := selectBudget_mono (W := W) (l := (ComputedComponents.vertices left right r).length)
    (l' := n) (hks.trans (ComputedComponents.vertices_length_le left right r))
    (ComputedComponents.vertices_length_le left right r)
  have hsl := AllHalfEncoded.selectFilter_length_le
    (rangeWords W (ComputedComponents.vertices left right r).length)
    ((ComputedComponents.vertices left right r).map (fun u => word W u.val))
    (setWords W (AllHalfEncoded.localSolve H w r))
  have hvl := ComputedComponents.vertices_length_le left right r
  simp only [List.length_map] at hsl
  simp only [itemBudget, componentHardBudget, adjArcs_length, rangeWords_length,
    List.length_map, List.length_cons, List.length_nil] at hb1 hb2 hb3 ⊢
  have hel : (edgeWords W left right).length = m := by simp [edgeWords]
  rw [hel]
  have hw2 : ((ComputedComponents.vertices left right r).map (fun u => word W u.val)).length ≤ n :=
    by simpa using hvl
  omega

end WeightedMIS.RegisterComponentSolve
