module

public import WeightedMIS.RegisterColumnResize
public import WeightedMIS.RegisterListZip
public import WeightedMIS.SignedWords
public import WeightedMIS.CompiledTemplateSemantics

/-!
# Stored edge records for the expanded-graph generator

The template compiler consumes, for every original edge, the record
`pair column (pair deltas (bit parity (pair weight label)))`
(`CompiledTemplates.EdgeAt key MetadataAt`). The fixed procedure below builds
these records from five parallel stored lists:

* signed columns with state keys at an input width, resized to the vertex width;
* per-edge delta lists of signed words, resized to the vertex width;
* signed parity-row words; the stored parity bit is the low bit of the
  magnitude, computed by the binary right shift;
* cost words, resized to the cost width;
* label pointers, stored without change.

Four list zips combine the lists from the innermost record outward. Every
item allocates its record cell; no record is supplied by the caller.
-/

@[expose] public section

namespace WeightedMIS.RegisterEdgeMetadata

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.Walks WeightedMIS.CompiledTemplates
open WeightedMIS.ExpandedWords WeightedMIS.RegisterColumnResize

variable {p : ℕ}

/-! ## The parity bit of a signed word -/

/-- The low bit of the magnitude of a signed word. -/
def lowBit {n : ℕ} (a : RegisterPotentialStep.Word n) : Bool :=
  (RegisterHalve.shiftRight false a.2).2

theorem lowBit_value {n : ℕ} (a : RegisterPotentialStep.Word n) :
    (if lowBit a then 1 else 0 : ZMod 2) = (RegisterPotentialStep.value a : ZMod 2) := by
  have hv := RegisterHalve.shiftRight_value false a.2
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hv
  have hcast : ((a.2.value : ℕ) : ZMod 2) = (if lowBit a then 1 else 0 : ZMod 2) := by
    rw [← hv]
    unfold lowBit
    cases (RegisterHalve.shiftRight false a.2).2
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.cast_mul, Nat.cast_ofNat]
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
    · simp only [↓reduceIte, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
  rw [← hcast]
  unfold RegisterPotentialStep.value BinaryRational.signed
  cases a.1
  · simp
  · simp only [↓reduceIte, Int.cast_neg, Int.cast_natCast]
    exact (ZMod.neg_eq_self_mod_two _).symm

/-! ## One record allocation after one procedure call -/

/-- Arguments: item, record tail, data. The item is transformed by `proc`
(with the data) and paired with the unchanged tail pointer. -/
def pairItemBody (proc : Fin p) : Command p :=
  .call proc [.register 0, .register 2] [3]
    (.allocate 4 (.pair (.register 3) (.register 1)) (.ret [.register 4]))

theorem pairItem_compiled (code : Code p) (proc item : Fin p)
    (hitem : code item = pairItemBody proc)
    {h mid : Heap} {ap bp dp x : Ptr} {budget : ℕ} (hext : Extends h mid) (hv : Valid mid)
    (hx : x < mid.length) (hb : bp < h.length)
    (run : Within code h (initialRegisters [.pointer ap, .pointer dp]) (code proc) [.pointer x] mid
      budget) :
    Extends h (mid ++ [.pair x bp]) ∧ Valid (mid ++ [.pair x bp]) ∧
      (mid ++ [.pair x bp])[mid.length]? = some (.pair x bp) ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp, .pointer dp]) (code item)
        [.pointer mid.length] (mid ++ [.pair x bp]) (budget + 16) := by
  have a := allocate_cell hv (.pair x bp) (by
    intro y hy
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact hx
    · exact lt_of_lt_of_le hb hext.length_le)
  refine ⟨hext.trans a.1, a.2.1, a.2.2, ?_⟩
  let regs := initialRegisters [Value.pointer ap, .pointer bp, .pointer dp]
  let r1 := bindResults regs [3] [Value.pointer x]
  let r2 := Function.update r1 4 (Value.pointer mid.length)
  have last : Within code (mid ++ [.pair x bp]) r2 (.ret [.register 4]) [.pointer mid.length]
      (mid ++ [.pair x bp]) 3 := by
    simpa [r2, values, Atom.eval] using Within.ret code (mid ++ [.pair x bp]) r2 [.register 4]
  have alloc := Within.allocate (regs := r1) (dst := 4) (expr := .pair (.register 3) (.register 1))
    (c := .pair x bp) (h := mid)
    (by simp [r1, regs, bindResults, initialRegisters, CellExpr.eval, Atom.eval, Value.asPointer])
    last
  have hargs : values regs [.register 0, .register 2] = [.pointer ap, .pointer dp] := by
    simp [regs, values, Atom.eval, initialRegisters]
  have call := Within.call (procedure := proc) (regs := regs)
    (arguments := [.register 0, .register 2]) (results := [3])
    (by simpa only [hargs] using run) alloc
  rw [hitem]
  exact call.mono (by simp [CellExpr.args]; omega)

/-- Arguments: signed parity word, cost-label record, unused data. Allocates
the parity cell `bit (low bit) costLabel`. -/
def parityItemBody (shift : Fin p) : Command p :=
  .load (.register 0) 3 15 4 { CompiledTrie.failCases with
    bit := .call shift [.register 3, .flag false] [5, 6]
      (.allocate 7 (.bit (.register 6) (.register 1)) (.ret [.register 7])) }

def parityItemBudget (n : ℕ) : ℕ := 28 * n + 50

/-! ## Record predicates -/

/-- A stored label pointer, carried unchanged into the records. -/
def LabelAt (h : Heap) (ptr : Ptr) (label : Ptr) : Prop := ptr = label ∧ ptr < h.length

def CostAt {cbits : ℕ} (h : Heap) (ptr : Ptr) (x : Bits cbits × Ptr) : Prop :=
  CostLabelAt h ptr x.1 x.2

def ParityAt {cbits : ℕ} (h : Heap) (ptr : Ptr) (x : Bool × (Bits cbits × Ptr)) : Prop :=
  ∃ cl, h[ptr]? = some (.bit x.1 cl) ∧ CostLabelAt h cl x.2.1 x.2.2

theorem LabelAt.mono {h h' : Heap} (he : Extends h h') {ptr l : Ptr} (hl : LabelAt h ptr l) :
    LabelAt h' ptr l := ⟨hl.1, lt_of_lt_of_le hl.2 he.length_le⟩

theorem ParityAt.mono {cbits : ℕ} {h h' : Heap} (he : Extends h h') {ptr : Ptr}
    {x : Bool × (Bits cbits × Ptr)} (hx : ParityAt h ptr x) : ParityAt h' ptr x := by
  obtain ⟨cl, hc, hcl⟩ := hx
  exact ⟨cl, he.lookup hc, hcl.mono he⟩

theorem ParityAt.allocated {cbits : ℕ} {h : Heap} {ptr : Ptr} {x : Bool × (Bits cbits × Ptr)}
    (hx : ParityAt h ptr x) : ptr < h.length := by
  obtain ⟨_, hc, _⟩ := hx
  exact (List.getElem?_eq_some_iff.mp hc).1

theorem EdgeAt.allocated {Row : Type*} {n vbits cbits : ℕ} {key : State Row → Bits n} {h : Heap}
    {ptr : Ptr} {x : Column Row × ArcMetadata vbits cbits} (hx : EdgeAt key MetadataAt h ptr x) :
    ptr < h.length := by
  obtain ⟨_, _, hc, _⟩ := hx
  exact (List.getElem?_eq_some_iff.mp hc).1

/-- Every item of a stored pointer list of a valid heap is a stored label. -/
theorem labels_of_listAt {h : Heap} (hh : Valid h) {lp : Ptr} {ls : List Ptr}
    (hl : ListAt h lp ls) : ListRep LabelAt h lp ls := by
  refine ⟨ls, hl, ?_⟩
  induction hl with
  | nil _ => exact .nil
  | cons cell _ ih => exact .cons ⟨rfl, RegisterListCommon.ListAt.head_allocated hh cell⟩ ih

/-! ## Procedures -/

structure Procedures (p : ℕ) where
  columns : RegisterColumnResize.Procedures p
  shift : Fin p
  signed : Fin p
  signedList : Fin p
  costItem : Fin p
  costZip : Fin p
  parityItem : Fin p
  parityZip : Fin p
  metaItem : Fin p
  metaZip : Fin p
  edgeItem : Fin p
  edgeZip : Fin p
  edges : Fin p

/-- Arguments: columns, delta lists, parity words, cost words, label
pointers, vertex shape word, cost shape word. Result: edge records. -/
def edgesBody (ids : Procedures p) : Command p :=
  .call ids.costZip [.register 3, .register 4, .register 6] [7]
  (.call ids.parityZip [.register 2, .register 7, .null] [8]
  (.call ids.metaZip [.register 1, .register 8, .register 5] [9]
  (.call ids.edgeZip [.register 0, .register 9, .register 5] [10]
  (.ret [.register 10]))))

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  ids.columns.Matches code ∧
  code ids.shift = RegisterHalve.shiftBody ids.shift ∧
  code ids.signed = RegisterResize.signedBody ids.columns.resize.resize ∧
  code ids.signedList = RegisterListMap.body ids.signedList ids.signed ∧
  code ids.costItem = pairItemBody ids.columns.resize.resize ∧
  code ids.costZip = RegisterListZip.body ids.costZip ids.costItem ∧
  code ids.parityItem = parityItemBody ids.shift ∧
  code ids.parityZip = RegisterListZip.body ids.parityZip ids.parityItem ∧
  code ids.metaItem = pairItemBody ids.signedList ∧
  code ids.metaZip = RegisterListZip.body ids.metaZip ids.metaItem ∧
  code ids.edgeItem = pairItemBody ids.columns.column ∧
  code ids.edgeZip = RegisterListZip.body ids.edgeZip ids.edgeItem ∧
  code ids.edges = edgesBody ids

/-- The metadata record stored for each edge. -/
def metadata {m n1 n2 wc : ℕ} (k cw : ℕ) (D : Fin m → List (SignedWord n1))
    (P : Fin m → RegisterPotentialStep.Word n2) (K : Fin m → Bits wc) (L : Fin m → Ptr)
    (e : Fin m) : ArcMetadata k cw :=
  ⟨(D e).map (SignedWord.resizeTo k), lowBit (P e), Bits.resizeTo cw (K e), L e⟩

def costBudget (cw wc : ℕ) : ℕ := RegisterResize.resizeBudget cw wc + 16

def metaBudget (k n1 d : ℕ) : ℕ := (RegisterResize.signedBudget k n1 + 35) * d + 13 + 16

def edgeBudget (k n0 : ℕ) : ℕ := columnBudget k n0 + 16

def budget (m d n0 n1 n2 wc k cw : ℕ) : ℕ :=
  (costBudget cw wc + 45) * m + (parityItemBudget n2 + 45) * m +
    (metaBudget k n1 d + 45) * m + (edgeBudget k n0 + 45) * m + 130

theorem parityItem_compiled (code : Code p) (ids : Procedures p) (hc : ids.Matches code)
    {n cw : ℕ} {h : Heap} (hh : Valid h) {ap bp dp : Ptr} {a : RegisterPotentialStep.Word n}
    {b : Bits cw × Ptr} (ha : SignedWords.SignedAt h ap a) (hb : CostAt h bp b) :
    ∃ out q, Extends h out ∧ Valid out ∧ ParityAt out q (lowBit a, b) ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp, .pointer dp]) (code ids.parityItem)
        [.pointer q] out (parityItemBudget n) := by
  obtain ⟨-, hshift, -, -, -, -, hitem, -⟩ := hc
  obtain ⟨mag, cell, hmag⟩ := ha
  obtain ⟨h1, q1, e1, v1, hq1, run0⟩ :=
    RegisterHalve.shift_compiled code ids.shift hshift hh hmag false
  have run1 : Within code h (initialRegisters [.pointer mag, .flag false]) (code ids.shift)
      [.pointer q1, .flag (lowBit a)] h1 (28 * n + 15) := run0
  have hbl : bp < h1.length := lt_of_lt_of_le (CostLabelAt.allocated hb) e1.length_le
  have a2 := allocate_cell v1 (.bit (lowBit a) bp) (by
    intro y hy
    simp only [Cell.references, List.mem_singleton] at hy
    subst y
    exact hbl)
  let h2 := h1 ++ [.bit (lowBit a) bp]
  refine ⟨h2, h1.length, e1.trans a2.1, a2.2.1, ⟨bp, a2.2.2, (hb.mono e1).mono a2.1⟩, ?_⟩
  let regs := initialRegisters [Value.pointer ap, .pointer bp, .pointer dp]
  let r1 := loadRegisters regs 3 15 4 (.bit a.1 mag)
  let r2 := bindResults r1 [5, 6] [Value.pointer q1, .flag (lowBit a)]
  let r3 := Function.update r2 7 (Value.pointer h1.length)
  have last : Within code h2 r3 (.ret [.register 7]) [.pointer h1.length] h2 3 := by
    simpa [r3, values, Atom.eval] using Within.ret code h2 r3 [.register 7]
  have alloc := Within.allocate (regs := r2) (dst := 7) (expr := .bit (.register 6) (.register 1))
    (c := .bit (lowBit a) bp) (h := h1)
    (by simp [r2, r1, regs, bindResults, loadRegisters, decoded, initialRegisters, CellExpr.eval,
      Atom.eval, Value.asPointer, Value.asFlag]) last
  have hargs : values r1 [.register 3, .flag false] = [.pointer mag, .flag false] := by
    simp [r1, regs, values, Atom.eval, loadRegisters, decoded]
  have call := Within.call (procedure := ids.shift) (regs := r1)
    (arguments := [.register 3, .flag false]) (results := [5, 6])
    (by simpa only [hargs] using run1) alloc
  have load := Within.load (regs := regs) (address := .register 0) (first := 3) (second := 15)
    (bit := 4) (branches := { CompiledTrie.failCases with
      bit := .call ids.shift [.register 3, .flag false] [5, 6]
        (.allocate 7 (.bit (.register 6) (.register 1)) (.ret [.register 7])) })
    (by simp [regs, initialRegisters, Atom.eval]) cell call
  rw [hitem]
  exact load.mono (by simp [CellExpr.args, parityItemBudget]; omega)

theorem zipWith_ofFn {α β γ : Type*} {m : ℕ} (f : α → β → γ) (a : Fin m → α) (b : Fin m → β) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => f (a i) (b i)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

/-- Exact edge records for the template compiler. -/
theorem edges_compiled (code : Code p) (ids : Procedures p) (hc : ids.Matches code)
    {r m d n0 n1 n2 wc k cw : ℕ} (key : State (Fin r) → Bits n0) (C : Fin m → Column (Fin r))
    (D : Fin m → List (SignedWord n1)) (P : Fin m → RegisterPotentialStep.Word n2)
    (K : Fin m → Bits wc) (L : Fin m → Ptr) (hdlen : ∀ e, (D e).length = d)
    {h : Heap} (hh : Valid h) {cp dp pp kp lp vp sp : Ptr} {vs : Bits k} {cs : Bits cw}
    (hcols : ListRep (ColumnAt key) h cp (List.ofFn C))
    (hds : ListRep DeltasAt h dp (List.ofFn D))
    (hpis : SignedWords.ListAt h pp (List.ofFn P))
    (hcosts : ExpandedWords.WordsAt h kp (List.ofFn K))
    (hlabels : ListAt h lp (List.ofFn L))
    (hv : BitsAt h vp vs) (hs : BitsAt h sp cs) :
    ∃ out q, Extends h out ∧ Valid out ∧
      ListRep (EdgeAt (resizeKey k key) MetadataAt) out q
        (edgeEntries C (metadata k cw D P K L)) ∧
      Within code h (initialRegisters [.pointer cp, .pointer dp, .pointer pp, .pointer kp,
        .pointer lp, .pointer vp, .pointer sp]) (code ids.edges) [.pointer q] out
        (budget m d n0 n1 n2 wc k cw) := by
  have hc' := hc
  obtain ⟨hcolumns, hshift, hsigned, hsignedList, hcostItem, hcostZip, hparityItem, hparityZip,
    hmetaItem, hmetaZip, hedgeItem, hedgeZip, hedges⟩ := hc
  have hres := hcolumns.1
  -- costs and labels
  obtain ⟨h1, q1, e1, v1, hq1, run1⟩ := RegisterListZip.compiled_const code ids.costZip
    ids.costItem hcostZip (fun h p (x : Bits wc) => BitsAt h p x) LabelAt
    (fun h p (s : Bits cw) => BitsAt h p s) CostAt
    (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he)
    (fun he _ _ hx => CostLabelAt.mono he hx) (fun _ hy => CostLabelAt.allocated hy)
    (fun _ a l => (Bits.resizeTo cw a, l)) (costBudget cw wc) hh hcosts
    (labels_of_listAt hh hlabels) hs
    (fun {h} hv {ap bp} {a l} _ ha hl hd => by
      obtain ⟨rfl, hbl⟩ := hl
      obtain ⟨mid, x, he, hm, hx, run⟩ := RegisterResize.resize_compiled code ids.columns.resize
        hres hv ha hd
      obtain ⟨he', hv', hcell, hrun⟩ := pairItem_compiled code _ ids.costItem hcostItem he hm
        hx.allocated hbl run
      exact ⟨_, _, he', hv', ⟨x, hcell, hx.mono ⟨_, rfl⟩, lt_of_lt_of_le hbl he'.length_le⟩, hrun⟩)
  -- parity bits
  obtain ⟨h2, q2, e2, v2, hq2, run2⟩ := RegisterListZip.compiled_const code ids.parityZip
    ids.parityItem hparityZip
    (fun h p (x : RegisterPotentialStep.Word n2) => SignedWords.SignedAt h p x)
    CostAt (fun (_ : Heap) (_ : Ptr) (_ : Unit) => True) ParityAt
    (fun he _ _ hx => hx.mono he) (fun he _ _ hx => CostLabelAt.mono he hx)
    (fun _ _ _ _ => trivial) (fun he _ _ hx => hx.mono he) (fun _ hy => hy.allocated)
    (fun _ a b => (lowBit a, b)) (parityItemBudget n2) (dataPtr := 0) (data := ()) v1
    (hpis.mono e1) hq1 trivial
    (fun {h} hv {ap bp} {a b} _ ha hb _ => parityItem_compiled code ids hc' hv ha hb)
  -- metadata
  have hdmem : ∀ x ∈ List.ofFn D, x.length = d := by
    intro x hx
    obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hx
    exact hdlen e
  obtain ⟨h3, q3, e3, v3, hq3, run3⟩ := RegisterListZip.compiled_const code ids.metaZip
    ids.metaItem hmetaZip (fun h p (x : List (SignedWord n1)) => DeltasAt h p x) ParityAt
    (fun h p (s : Bits k) => BitsAt h p s) (fun h p (x : ArcMetadata k cw) => MetadataAt h p x)
    (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he)
    (fun he _ _ hx => hx.mono he) (fun _ hy => hy.allocated)
    (fun _ ds b => ⟨ds.map (SignedWord.resizeTo k), b.1, b.2.1, b.2.2⟩) (metaBudget k n1 d)
    v2 (ListRep.mono (e1.trans e2) (fun _ _ hx => hx.mono (e1.trans e2)) hds) hq2
    ((hv.mono e1).mono e2)
    (fun {h} hv' {ap bp} {ds b} hmem hd hb hshape => by
      have hlen := hdmem ds (List.of_mem_zip hmem).1
      obtain ⟨mid, x, he, hm, hx, run⟩ := RegisterResize.signedList_compiled code
        ids.columns.resize hres ids.signed ids.signedList hsigned hsignedList hv' hd hshape
      obtain ⟨he', hv'', hcell, hrun⟩ := pairItem_compiled code _ ids.metaItem hmetaItem he hm
        (ListRep.allocated hx) hb.allocated run
      obtain ⟨cl, hpc, hcl⟩ := hb.mono he
      refine ⟨_, _, he', hv'', ⟨x, bp, cl, hcell, ?_, ?_, ?_⟩, ?_⟩
      · exact (Extends.lookup ⟨_, rfl⟩ hpc)
      · exact hx.mono ⟨_, rfl⟩
      · exact hcl.mono ⟨_, rfl⟩
      · refine hrun.mono ?_
        rw [hlen]
        simp only [metaBudget]
        omega)
  -- edges
  obtain ⟨h4, q4, e4, v4, hq4, run4⟩ := RegisterListZip.compiled_const code ids.edgeZip
    ids.edgeItem hedgeZip (ColumnAt key) (fun h p (x : ArcMetadata k cw) => MetadataAt h p x)
    (fun h p (s : Bits k) => BitsAt h p s) (EdgeAt (resizeKey k key) MetadataAt)
    (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he)
    (fun he _ _ hx => EdgeAt.mono (key := resizeKey k key) (metaAt := MetadataAt)
      (fun he' hm => MetadataAt.mono he' hm) he hx)
    (fun _ hy => EdgeAt.allocated hy)
    (fun _ c md => (c, md)) (edgeBudget k n0)
    v3 (ListRep.mono ((e1.trans e2).trans e3)
      (fun _ _ hx => hx.mono ((e1.trans e2).trans e3)) hcols) hq3 (((hv.mono e1).mono e2).mono e3)
    (fun {h} hv' {ap bp} {c md} _ hcol hmd hshape => by
      obtain ⟨mid, x, he, hm, hx, run⟩ := column_compiled code ids.columns hcolumns hv' hcol hshape
      obtain ⟨he', hv'', hcell, hrun⟩ := pairItem_compiled code _ ids.edgeItem hedgeItem he hm
        (ColumnAt.allocated hx) hmd.allocated run
      exact ⟨_, _, he', hv'', ⟨x, bp, hcell, hx.mono ⟨_, rfl⟩, (hmd.mono he).mono ⟨_, rfl⟩⟩,
        hrun⟩)
  have hlist : List.zipWith (fun c md => (c, md)) (List.ofFn C)
      (List.zipWith (fun ds (b : Bool × (Bits cw × Ptr)) =>
        (⟨ds.map (SignedWord.resizeTo k), b.1, b.2.1, b.2.2⟩ : ArcMetadata k cw)) (List.ofFn D)
        (List.zipWith (fun a b => (lowBit a, b)) (List.ofFn P)
          (List.zipWith (fun a l => (Bits.resizeTo cw a, l)) (List.ofFn K) (List.ofFn L)))) =
      edgeEntries C (metadata k cw D P K L) := by
    simp only [zipWith_ofFn]
    simp only [edgeEntries, List.ofFn_eq_map, metadata]
  rw [hlist] at hq4
  refine ⟨h4, q4, ((e1.trans e2).trans e3).trans e4, v4, hq4, ?_⟩
  let regs := initialRegisters [Value.pointer cp, .pointer dp, .pointer pp, .pointer kp,
    .pointer lp, .pointer vp, .pointer sp]
  let r1 := bindResults regs [7] [Value.pointer q1]
  let r2 := bindResults r1 [8] [Value.pointer q2]
  let r3 := bindResults r2 [9] [Value.pointer q3]
  let r4 := bindResults r3 [10] [Value.pointer q4]
  have last : Within code h4 r4 (.ret [.register 10]) [.pointer q4] h4 3 := by
    simpa [r4, values, Atom.eval, bindResults] using Within.ret code h4 r4 [.register 10]
  have a4 : values r3 [.register 0, .register 9, .register 5] =
      [.pointer cp, .pointer q3, .pointer vp] := by
    simp [r3, r2, r1, regs, values, Atom.eval, bindResults, initialRegisters]
  have c4 := Within.call (procedure := ids.edgeZip) (regs := r3)
    (arguments := [.register 0, .register 9, .register 5]) (results := [10])
    (by simpa only [a4] using run4) last
  have a3 : values r2 [.register 1, .register 8, .register 5] =
      [.pointer dp, .pointer q2, .pointer vp] := by
    simp [r2, r1, regs, values, Atom.eval, bindResults, initialRegisters]
  have c3 := Within.call (procedure := ids.metaZip) (regs := r2)
    (arguments := [.register 1, .register 8, .register 5]) (results := [9])
    (by simpa only [a3] using run3) c4
  have a2 : values r1 [.register 2, .register 7, .null] =
      [.pointer pp, .pointer q1, .pointer 0] := by
    simp [r1, regs, values, Atom.eval, bindResults, initialRegisters]
  have c2 := Within.call (procedure := ids.parityZip) (regs := r1)
    (arguments := [.register 2, .register 7, .null]) (results := [8])
    (by simpa only [a2] using run2) c3
  have a1 : values regs [.register 3, .register 4, .register 6] =
      [.pointer kp, .pointer lp, .pointer sp] := by
    simp [regs, values, Atom.eval, initialRegisters]
  have c1 := Within.call (procedure := ids.costZip) (regs := regs)
    (arguments := [.register 3, .register 4, .register 6]) (results := [7])
    (by simpa only [a1] using run1) c2
  rw [hedges]
  refine c1.mono ?_
  simp only [List.length_zipWith, List.length_ofFn, min_self, List.length_cons, List.length_nil,
    budget]
  omega

end WeightedMIS.RegisterEdgeMetadata
