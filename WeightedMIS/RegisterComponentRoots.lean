module

public import WeightedMIS.RegisterGraphArcs
public import WeightedMIS.RegisterResidualSearch
public import WeightedMIS.RegisterListFilter

/-!
# Component roots of a stored graph

For every stored vertex word the residual search with unit capacities and
unit threshold computes the reached word list, and the vertex is kept when no
reached word has a smaller value (one comparator call per reached word). The
list filter over the vertex words returns exactly `GraphReachEncoded.rootsE`,
which on the adjacency arcs of a graph is the word list of the computed
component roots `ComputedComponents.roots`.
-/

@[expose] public section

namespace WeightedMIS.RegisterComponentRoots

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch WeightedMIS.RegisterFlagKeys
open WeightedMIS.ExpandedWords WeightedMIS.ResidualWords
open WeightedMIS.GraphReachEncoded (one reachE isRootE rootsE adjArcs)

variable {p : ℕ}

/-! ## Representations -/

/-- A list of values stored through the representation of their images. -/
theorem listRep_map {α β : Type*} {R : Heap → Ptr → β → Prop} {h : Heap} {ptr : Ptr}
    {f : α → β} {xs : List α} :
    ListRep R h ptr (xs.map f) ↔ ListRep (fun h p x => R h p (f x)) h ptr xs := by
  constructor
  · rintro ⟨ptrs, hl, hr⟩
    exact ⟨ptrs, hl, List.forall₂_map_right_iff.mp hr⟩
  · rintro ⟨ptrs, hl, hr⟩
    exact ⟨ptrs, hl, List.forall₂_map_right_iff.mpr hr⟩

/-- The search context `pair arcs (pair one nodes)`. -/
def SearchAt {k : ℕ} (h : Heap) (ptr : Ptr) (ctx : List (Arc k 1) × List (Bits k)) : Prop :=
  ∃ ap rest op np, h[ptr]? = some (.pair ap rest) ∧ h[rest]? = some (.pair op np) ∧
    TableAt h ap ctx.1 ∧ BitsAt h op one ∧ WordsAt h np ctx.2

theorem SearchAt.mono {k : ℕ} {h h' : Heap} (he : Extends h h') {ptr : Ptr}
    {ctx : List (Arc k 1) × List (Bits k)} (hs : SearchAt h ptr ctx) : SearchAt h' ptr ctx := by
  obtain ⟨ap, rest, op, np, c1, c2, ha, ho, hn⟩ := hs
  exact ⟨ap, rest, op, np, he.lookup c1, he.lookup c2, ha.mono he, ho.mono he, hn.mono he⟩

/-! ## Procedures -/

/-- Arguments 0 = word, 1 = list; the flag says that no listed word is smaller. -/
def allLeBody (self cmp : Fin p) : Command p :=
  .load (.register 1) 2 3 15 { CompiledTrie.failCases with
    nil := .ret [.flag true]
    cons := .call cmp [.register 2, .register 0] [4, 5]
      (.branch (.register 4) (.ret [.flag false])
        (.call self [.register 0, .register 3] [6] (.ret [.register 6]))) }

/-- Arguments 0 = vertex word, 1 = search context. -/
def rootItemBody (search allLe : Fin p) : Command p :=
  .load (.register 1) 2 3 15 { CompiledTrie.failCases with
    pair := .load (.register 3) 4 5 15 { CompiledTrie.failCases with
      pair := .call search [.register 2, .register 4, .register 5, .register 0] [6, 7]
        (.call allLe [.register 0, .register 6] [8] (.ret [.register 8])) } }

/-- Arguments 0 = arcs, 1 = unit word, 2 = vertex words. -/
def rootsBody (filter : Fin p) : Command p :=
  .allocate 3 (.pair (.register 1) (.register 2))
    (.allocate 4 (.pair (.register 0) (.register 3))
      (.call filter [.register 2, .register 4] [5] (.ret [.register 5])))

structure Procedures (p : ℕ) where
  roots : Fin p
  filter : Fin p
  rootItem : Fin p
  allLe : Fin p
  search : Fin p
  residual : RegisterResidualSearch.Procedures p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.roots = rootsBody ids.filter ∧
  code ids.filter = RegisterListFilter.body ids.filter ids.rootItem ∧
  code ids.rootItem = rootItemBody ids.search ids.allLe ∧
  code ids.allLe = allLeBody ids.allLe ids.residual.cmp ∧
  code ids.search = RegisterResidualSearch.searchBody ids.residual.reach ids.residual.prepend ∧
  ids.residual.Matches code

def allLeBudget (W k : ℕ) : ℕ := (36 * W + 70) * k + 13

def rootItemBudget (W a k : ℕ) : ℕ :=
  RegisterResidualSearch.budget W 1 a k + allLeBudget W (k + 1) + 60

def rootsBudget (W a k : ℕ) : ℕ := (rootItemBudget W a k + 35) * k + 40

/-! ## Correctness -/

theorem compare_lt {n : ℕ} (a b : Bits n) :
    decide ((Bits.compare a b).1 = .lt) = !decide (b.value ≤ a.value) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_le]
  exact (Bits.compare_correct a b).1

theorem allLe_compiled (code : Code p) (self cmp : Fin p) (hself : code self = allLeBody self cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {W : ℕ} {h : Heap} {vp lp : Ptr} {v : Bits W} {us : List (Bits W)}
    (hv : BitsAt h vp v) (hl : WordsAt h lp us) :
    Within code h (initialRegisters [.pointer vp, .pointer lp]) (code self)
      [.flag (isRootE us v)] h (allLeBudget W us.length) := by
  induction us generalizing lp with
  | nil =>
    have cell := WordsAt.nil_iff.mp hl
    rw [hself]
    refine (Within.load (pointer := lp) (c := Cell.nil) (by reg_simp) cell
      (ret_values (by reg_simp [isRootE]) le_rfl)).mono ?_
    simp [allLeBudget]
  | cons u us ih =>
    obtain ⟨uh, ut, cell, hu, ht⟩ := WordsAt.cons_iff.mp hl
    have hc := RegisterComparator.compiled code cmp hcmp hu hv
    by_cases hle : v.value ≤ u.value
    · have hr := ih ht
      rw [hself]
      refine (Within.load (pointer := lp) (c := Cell.cons uh ut) (by reg_simp) cell
        (call_of (by reg_simp) hc (Within.branch (b := false) (by reg_simp [compare_lt, hle])
        (call_of (by reg_simp) hr
        (ret_values (by reg_simp [isRootE, hle]) le_rfl))))).mono ?_
      simp [allLeBudget]; nlinarith
    · rw [hself]
      refine (Within.load (pointer := lp) (c := Cell.cons uh ut) (by reg_simp) cell
        (call_of (by reg_simp) hc (Within.branch (b := true) (by reg_simp [compare_lt, hle])
        (ret_values (by reg_simp [isRootE, hle]) le_rfl)))).mono ?_
      simp [allLeBudget]; nlinarith

/-- The residual search with unit threshold computes the reached words. -/
theorem search_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {k : ℕ} {h : Heap} (hh : Valid h) {ap op np sp : Ptr} {arcs : List (Arc k 1)}
    {nodes : List (Bits k)} {s : Bits k}
    (ha : TableAt h ap arcs) (ho : BitsAt h op one) (hn : WordsAt h np nodes)
    (hs : BitsAt h sp s) :
    ∃ out seenp routep, Extends h out ∧ Valid out ∧ WordsAt out seenp (reachE arcs nodes s) ∧
      Within code h (initialRegisters [.pointer ap, .pointer op, .pointer np, .pointer sp])
        (code ids.search) [.pointer seenp, .pointer routep] out
        (RegisterResidualSearch.budget k 1 arcs.length nodes.length) := by
  obtain ⟨-, -, -, -, hsearch, hres⟩ := hm
  obtain ⟨out, seenp, routep, he, hv, hseen, -, hw⟩ :=
    RegisterResidualSearch.compiled code ids.residual hres hh ha ho hn hs
  exact ⟨out, seenp, routep, he, hv, hseen, by rw [hsearch]; exact hw⟩

theorem reachE_length {k : ℕ} (arcs : List (Arc k 1)) (nodes : List (Bits k)) (s : Bits k) :
    (reachE arcs nodes s).length ≤ nodes.length + 1 := by
  unfold reachE
  have := (ResidualListReach.explore_lengths arcs one nodes.length
    (ResidualListReach.initial s)).1
  simpa [ResidualListReach.initial, Nat.add_comm] using this

theorem rootItem_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {vp dp : Ptr} {v : Bits W}
    {ctx : List (Arc W 1) × List (Bits W)} (hv : BitsAt h vp v) (hd : SearchAt h dp ctx) :
    ∃ out, Extends h out ∧ Valid out ∧
      Within code h (initialRegisters [.pointer vp, .pointer dp]) (code ids.rootItem)
        [.flag (isRootE (reachE ctx.1 ctx.2 v) v)] out
        (rootItemBudget W ctx.1.length ctx.2.length) := by
  have hm' := hm
  obtain ⟨-, -, hitem, hall, -, hres⟩ := hm'
  obtain ⟨ap, rest, op, np, c1, c2, ha, ho, hn⟩ := hd
  obtain ⟨out, seenp, routep, he, hvo, hseen, w1⟩ := search_compiled ids code hm hh ha ho hn hv
  have w2 := allLe_compiled code ids.allLe ids.residual.cmp hall hres.2.2.2.2.2.2.2
    (hv.mono he) hseen
  have hlen := reachE_length ctx.1 ctx.2 v
  refine ⟨out, he, hvo, ?_⟩
  rw [hitem]
  refine (Within.load (pointer := dp) (c := Cell.pair ap rest) (by reg_simp) c1
    (Within.load (pointer := rest) (c := Cell.pair op np) (by reg_simp) c2
    (call_of (by reg_simp) w1 (call_of (by reg_simp) w2
    (ret_values (by reg_simp) le_rfl))))).mono ?_
  have : allLeBudget W (reachE ctx.1 ctx.2 v).length ≤ allLeBudget W (ctx.2.length + 1) := by
    simp only [allLeBudget]; gcongr
  simp only [rootItemBudget]
  norm_num
  omega

/-- The filter of the vertex words by the root test is `rootsE`. -/
theorem roots_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {ap op np : Ptr} {edges : List (Bits W × Bits W)}
    {nodes : List (Bits W)}
    (ha : TableAt h ap (adjArcs edges)) (ho : BitsAt h op one) (hn : WordsAt h np nodes) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (rootsE edges nodes) ∧
      Within code h (initialRegisters [.pointer ap, .pointer op, .pointer np]) (code ids.roots)
        [.pointer q] out (rootsBudget W (adjArcs edges).length nodes.length) := by
  have hm' := hm
  obtain ⟨hroots, hfilter, -⟩ := hm'
  obtain ⟨e1, v1, c1⟩ := alloc_pair hh ho.allocated hn.allocated
  have ha1 : ap < (h ++ [Cell.pair op np]).length := lt_of_lt_of_le ha.allocated e1.length_le
  have hh1 : h.length < (h ++ [Cell.pair op np]).length := by simp
  obtain ⟨e2, v2, c2⟩ := alloc_pair v1 ha1 hh1
  have e12 := e1.trans e2
  have hctx : SearchAt (h ++ [Cell.pair op np] ++ [Cell.pair ap h.length])
      (h ++ [Cell.pair op np]).length (adjArcs edges, nodes) :=
    ⟨ap, h.length, op, np, c2, e2.lookup c1, ha.mono e12, ho.mono e12, hn.mono e12⟩
  obtain ⟨out, q, he, hv, hq, hw⟩ := RegisterListFilter.compiled_const code ids.filter
    ids.rootItem hfilter (fun h p (w : Bits W) => BitsAt h p w) SearchAt
    (fun he _ _ hb => hb.mono he) (fun he _ _ hs => hs.mono he)
    (fun ctx v => isRootE (reachE ctx.1 ctx.2 v) v)
    (rootItemBudget W (adjArcs edges).length nodes.length) v2 (hn.mono e12) hctx
    (fun hv' _ _ _ hx hd => rootItem_compiled ids code hm hv' hx hd)
  refine ⟨out, q, e12.trans he, hv, hq, ?_⟩
  rw [hroots]
  refine (Within.allocate (c := Cell.pair op np) (by reg_simp)
    (Within.allocate (c := Cell.pair ap h.length) (by reg_simp)
    (call_of (by reg_simp) hw (ret_values (by reg_simp) le_rfl)))).mono ?_
  simp [rootsBudget, CellExpr.args]; omega

/-! ## Roots of a graph -/

theorem length_flatMap_const {α β : Type*} (l : List α) (f : α → List β) (k : ℕ)
    (hf : ∀ a, (f a).length = k) : (l.flatMap f).length = k * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, hf, ih, List.length_cons]; ring

theorem rangeWords_eq (W n : ℕ) :
    GraphReachEncoded.rangeWords W n = RibbonTable.rangeWords W n := by
  rw [GraphReachEncoded.rangeWords_eq_range]
  rfl

/-- On the adjacency arcs of the stored table of a ribbon, the procedure
returns the words of the computed component roots. -/
theorem graphRoots_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W n m : ℕ} (hn : n < 2 ^ W) {left right : Fin m → Fin n}
    {h : Heap} (hh : Valid h) {ap op np : Ptr}
    (ha : TableAt h ap (adjArcs (GraphReachEncoded.edgeWords W left right)))
    (ho : BitsAt h op one) (hnp : WordsAt h np (RibbonTable.rangeWords W n)) :
    ∃ out q, Extends h out ∧ Valid out ∧
      ListRep (fun h p (r : Fin n) => BitsAt h p (RibbonTable.word W r.val)) out q
        (ComputedComponents.roots left right) ∧
      Within code h (initialRegisters [.pointer ap, .pointer op, .pointer np]) (code ids.roots)
        [.pointer q] out (rootsBudget W (2 * m) n) := by
  rw [← rangeWords_eq] at hnp
  obtain ⟨out, q, he, hv, hq, hw⟩ := roots_compiled ids code hm hh ha ho hnp
  rw [GraphReachEncoded.roots_encode left right hn] at hq
  refine ⟨out, q, he, hv, listRep_map.mp hq, ?_⟩
  have hlen : (adjArcs (GraphReachEncoded.edgeWords W left right)).length = 2 * m := by
    rw [adjArcs, length_flatMap_const _ _ 2 (fun _ => rfl)]
    simp [GraphReachEncoded.edgeWords]
  simpa [hlen, GraphReachEncoded.rangeWords] using hw

end WeightedMIS.RegisterComponentRoots
