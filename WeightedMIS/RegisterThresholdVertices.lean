module

public import WeightedMIS.RegisterRouteCounts
public import WeightedMIS.RegisterPotentialRoute
public import WeightedMIS.RegisterSignedDot
public import WeightedMIS.RegisterListFilter

/-!
# Vertices with recovered value at least one

For every stored vertex word, the item procedure looks up its stored reverse
route, refills the route arcs with the original edge counts, propagates the
signed root value along the route with `RegisterPotentialRoute`, and tests
whether the resulting signed word is at least one: its sign bit is clear and
its magnitude is not below the stored unit word. A filter traversal keeps
exactly the vertex words passing the test, in their stored order, sharing
the input words.
-/

@[expose] public section

namespace WeightedMIS.RegisterThresholdVertices

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.ResidualWords
open WeightedMIS.RegisterPotentialStep WeightedMIS.RegisterFirstEdge

variable {W B : ℕ}

/-! ## Reference -/

/-- A signed word is at least one: clear sign and magnitude not below one. -/
def positive (one : Bits B) (a : Word B) : Bool :=
  if a.1 then false else !decide ((Bits.compare a.2 one).1 = .lt)

theorem positive_iff (one : Bits B) (a : Word B) (hone : one.value = 1) :
    positive one a = true ↔ 1 ≤ value a := by
  rcases a with ⟨s, a⟩
  have hc := (Bits.compare_correct a one).1
  cases s
  · simp only [positive, Bool.false_eq_true, ↓reduceIte, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, hc, hone, not_lt, value, BinaryRational.signed]
    omega
  · simp only [positive, ↓reduceIte, Bool.false_eq_true, false_iff, not_le, value,
      BinaryRational.signed]
    omega

/-- The per-vertex data. -/
structure Data (W B : ℕ) where
  routes : List (RegisterRouteLookup.Route W 1)
  recs : List (Record W B)
  zero : Bits B
  one : Bits B
  root : Word B

/-- The refilled stored route of a vertex word. -/
def route (d : Data W B) (x : Bits W) : List (Arc W B) :=
  (RegisterRouteLookup.lookup x d.routes).map (RegisterRouteCounts.refill d.zero d.recs)

/-- The propagated signed value of a vertex word. -/
def final (d : Data W B) (x : Bits W) : Word B :=
  RegisterPotentialRoute.recover d.one (route d x) d.root

/-- The filter predicate. -/
def keep (d : Data W B) (x : Bits W) : Bool := positive d.one (final d x)

/-- Data `.pair routes (.pair refillData (.pair one root))`. -/
def DataAt (h : Heap) (p : Ptr) (d : Data W B) : Prop :=
  ∃ rp r1 fp r2 op tp, h[p]? = some (.pair rp r1) ∧ h[r1]? = some (.pair fp r2) ∧
    h[r2]? = some (.pair op tp) ∧ RegisterRouteLookup.RoutesAt h rp d.routes ∧
    RegisterRouteCounts.DataAt h fp (d.recs, d.zero) ∧ BitsAt h op d.one ∧
    SignedWords.SignedAt h tp d.root

theorem DataAt.mono {h h' : Heap} (he : Extends h h') {p : Ptr} {d : Data W B}
    (hd : DataAt h p d) : DataAt h' p d := by
  obtain ⟨rp, r1, fp, r2, op, tp, c1, c2, c3, hr, hf, ho, ht⟩ := hd
  exact ⟨rp, r1, fp, r2, op, tp, he.lookup c1, he.lookup c2, he.lookup c3, hr.mono he,
    hf.mono he, ho.mono he, ht.mono he⟩

/-! ## Procedures -/

variable {p : ℕ}

def testBody (cmp : Fin p) : Command p :=
  .branch (.register 13) (.ret [.flag false])
    (.call cmp [.register 14, .register 6] [15, 0]
      (.branch (.register 15) (.ret [.flag false]) (.ret [.flag true])))

def computeBody (lookup map route cmp : Fin p) : Command p :=
  .call lookup [.register 0, .register 2] [11]
    (.call map [.register 11, .register 4] [12]
      (.call route [.register 12, .register 6, .register 10, .register 8] [13, 14]
        (testBody cmp)))

/-- Arguments: vertex word, data. Result: whether its propagated value is at least one. -/
def vertexBody (lookup map route cmp : Fin p) : Command p :=
  .load (.register 1) 2 3 15 { CompiledTrie.failCases with
    pair := .load (.register 3) 4 5 15 { CompiledTrie.failCases with
      pair := .load (.register 5) 6 7 15 { CompiledTrie.failCases with
        pair := .load (.register 7) 8 9 10 { CompiledTrie.failCases with
          bit := computeBody lookup map route cmp } } } }

structure Procedures (p : ℕ) where
  counts : RegisterRouteCounts.Procedures p
  arith : RegisterSignedDot.Procedures p
  lookup : Fin p
  step : Fin p
  route : Fin p
  item : Fin p
  filter : Fin p

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  d.counts.Matches code ∧ RegisterSignedDot.Matches code d.arith ∧
  code d.lookup = RegisterRouteLookup.lookupBody d.lookup d.arith.cmp ∧
  code d.step = RegisterPotentialStep.stepBody d.arith.signedAdd ∧
  code d.route = RegisterPotentialRoute.routeBody d.route d.step ∧
  code d.item = vertexBody d.lookup d.counts.map d.route d.arith.cmp ∧
  code d.filter = RegisterListFilter.body d.filter d.item

def itemBudget (W B R M L : ℕ) : ℕ :=
  (36 * W + 70) * R + RegisterRouteCounts.budget W M L + 400 * (B + 1) * L + 36 * B + 150

def budget (W B R M L N : ℕ) : ℕ := (itemBudget W B R M L + 35) * N + 13

theorem test_within (code : Code p) (cmp : Fin p)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {h : Heap} {regs : Registers} {mp op : Ptr} {a : Word B} {one : Bits B}
    (h13 : regs 13 = .flag a.1) (h14 : regs 14 = .pointer mp) (h6 : regs 6 = .pointer op)
    (hm : BitsAt h mp a.2) (ho : BitsAt h op one) :
    Within code h regs (testBody cmp) [.flag (positive one a)] h (36 * B + 45) := by
  unfold testBody
  cases hs : a.1
  · have c := RegisterComparator.compiled code cmp hcmp hm ho
    let r1 := bindResults regs [15, 0] (RegisterComparator.flags (Bits.compare a.2 one).1)
    have last : Within code h r1
        (.branch (.register 15) (.ret [.flag false]) (.ret [.flag true]))
        [.flag (positive one a)] h 6 := by
      refine Within.branch (regs := r1) (budget := 3) (test := .register 15)
        (b := decide ((Bits.compare a.2 one).1 = .lt))
        (yes := .ret [.flag false]) (no := .ret [.flag true])
        (by simp [r1, bindResults, Atom.eval, RegisterComparator.flags]) ?_
      cases hl : decide ((Bits.compare a.2 one).1 = .lt)
      · simpa [positive, hs, hl, values, Atom.eval] using Within.ret code h r1 [.flag true]
      · simpa [positive, hs, hl, values, Atom.eval] using Within.ret code h r1 [.flag false]
    have cargs : values regs [.register 14, .register 6] = [.pointer mp, .pointer op] := by
      simp [values, Atom.eval, h14, h6]
    have k := Within.call (procedure := cmp) (regs := regs)
      (arguments := [.register 14, .register 6]) (results := [15, 0])
      (by simpa only [cargs] using c) last
    have b := Within.branch (b := false) (test := .register 13) (regs := regs)
      (yes := .ret [.flag false]) (by simp [Atom.eval, h13, hs]) k
    exact b.mono (by simp; omega)
  · have last := Within.ret code h regs [.flag false]
    have b := Within.branch (b := true) (test := .register 13) (regs := regs)
      (no := .call cmp [.register 14, .register 6] [15, 0]
        (.branch (.register 15) (.ret [.flag false]) (.ret [.flag true])))
      (by simp [Atom.eval, h13, hs]) last
    simpa [positive, hs, values, Atom.eval] using b.mono (b := 36 * B + 45) (by simp)

theorem item_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {R L : ℕ} {h : Heap} (hh : Valid h) {xp dp : Ptr} {x : Bits W} {data : Data W B}
    (hR : data.routes.length ≤ R) (hL : (RegisterRouteLookup.lookup x data.routes).length ≤ L)
    (hx : BitsAt h xp x) (hd : DataAt h dp data) :
    ∃ out, Extends h out ∧ Valid out ∧
      Within code h (initialRegisters [.pointer xp, .pointer dp]) (code d.item)
        [.flag (keep data x)] out (itemBudget W B R data.recs.length L) := by
  obtain ⟨hcounts, harith, hlookup, hstep, hroute, hitem, -⟩ := hm
  have harith' := harith
  obtain ⟨-, hadd, hcmp, hcomp, hsub, -, -, -, -, hsigned⟩ := harith'
  obtain ⟨rp, r1, fp, r2, op, tp, c1, c2, c3, hr, hf, ho, ht⟩ := hd
  obtain ⟨mp, c4, hmag⟩ := ht
  obtain ⟨lp, hlp, lrun⟩ := RegisterRouteLookup.compiled code d.lookup d.arith.cmp hlookup hcmp
    hh hx hr
  obtain ⟨H1, qp, e1, v1, hq, mrun⟩ := RegisterRouteCounts.compiled code d.counts hcounts hh
    hlp hf
  obtain ⟨H2, fres, e2, v2, hfres, rrun⟩ := RegisterPotentialRoute.compiled code d.route d.step
    d.arith.signedAdd d.arith.cmp d.arith.sub d.arith.complement d.arith.add hroute hstep
    hsigned hcmp hsub hcomp hadd v1 hq ((ho.mono e1)) (hmag.mono e1)
  refine ⟨H2, e1.trans e2, v2, ?_⟩
  let regs := initialRegisters [Value.pointer xp, .pointer dp]
  let s1 := loadRegisters regs 2 3 15 (.pair rp r1)
  let s2 := loadRegisters s1 4 5 15 (.pair fp r2)
  let s3 := loadRegisters s2 6 7 15 (.pair op tp)
  let s4 := loadRegisters s3 8 9 10 (.bit data.root.1 mp)
  let s5 := bindResults s4 [11] [.pointer lp]
  let s6 := bindResults s5 [12] [.pointer qp]
  let s7 := bindResults s6 [13, 14] [.flag (final data x).1, .pointer fres]
  have test := test_within code d.arith.cmp hcmp (regs := s7) (mp := fres) (op := op)
    (a := final data x) (one := data.one)
    (by simp [s7, bindResults]) (by simp [s7, bindResults])
    (by simp [s7, s6, s5, s4, s3, s2, s1, bindResults, loadRegisters, decoded])
    hfres ((ho.mono e1).mono e2)
  have rargs : values s6 [.register 12, .register 6, .register 10, .register 8] =
      [.pointer qp, .pointer op, .flag data.root.1, .pointer mp] := by
    simp [s6, s5, s4, s3, s2, s1, regs, bindResults, loadRegisters, decoded,
      values, Atom.eval]
  have rcall := Within.call (procedure := d.route) (regs := s6)
    (arguments := [.register 12, .register 6, .register 10, .register 8]) (results := [13, 14])
    (by simpa only [rargs, final, route] using rrun) test
  have margs : values s5 [.register 11, .register 4] = [.pointer lp, .pointer fp] := by
    simp [s5, s4, s3, s2, s1, regs, bindResults, loadRegisters, decoded,
      values, Atom.eval]
  have mcall := Within.call (procedure := d.counts.map) (regs := s5)
    (arguments := [.register 11, .register 4]) (results := [12])
    (by simpa only [margs] using mrun) rcall
  have largs : values s4 [.register 0, .register 2] = [.pointer xp, .pointer rp] := by
    simp [s4, s3, s2, s1, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
  have lcall := Within.call (procedure := d.lookup) (regs := s4)
    (arguments := [.register 0, .register 2]) (results := [11])
    (by simpa only [largs] using lrun) mcall
  have l4 := Within.load (regs := s3) (address := .register 7) (first := 8) (second := 9)
    (bit := 10) (branches := { CompiledTrie.failCases with
      bit := computeBody d.lookup d.counts.map d.route d.arith.cmp })
    (by simp [s3, loadRegisters, decoded, Atom.eval]) c4 lcall
  have l3 := Within.load (regs := s2) (address := .register 5) (first := 6) (second := 7)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 7) 8 9 10 { CompiledTrie.failCases with
        bit := computeBody d.lookup d.counts.map d.route d.arith.cmp } })
    (by simp [s2, loadRegisters, decoded, Atom.eval]) c3 l4
  have l2 := Within.load (regs := s1) (address := .register 3) (first := 4) (second := 5)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 5) 6 7 15 { CompiledTrie.failCases with
        pair := .load (.register 7) 8 9 10 { CompiledTrie.failCases with
          bit := computeBody d.lookup d.counts.map d.route d.arith.cmp } } })
    (by simp [s1, loadRegisters, decoded, Atom.eval]) c2 l3
  have l1 := Within.load (regs := regs) (address := .register 1) (first := 2) (second := 3)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 3) 4 5 15 { CompiledTrie.failCases with
        pair := .load (.register 5) 6 7 15 { CompiledTrie.failCases with
          pair := .load (.register 7) 8 9 10 { CompiledTrie.failCases with
            bit := computeBody d.lookup d.counts.map d.route d.arith.cmp } } } })
    (by simp [regs, initialRegisters, Atom.eval]) c1 l2
  rw [hitem]
  refine l1.mono ?_
  have hlen : (RegisterRouteLookup.lookup x data.routes).length ≤ L := hL
  have b1 : RegisterRouteCounts.budget W data.recs.length
      (RegisterRouteLookup.lookup x data.routes).length ≤
      RegisterRouteCounts.budget W data.recs.length L := by
    unfold RegisterRouteCounts.budget
    have := Nat.mul_le_mul_left (RegisterRouteCounts.itemBudget W data.recs.length + 35) hlen
    omega
  have b2 : RegisterPotentialRoute.budget B
      ((RegisterRouteLookup.lookup x data.routes).map
        (RegisterRouteCounts.refill data.zero data.recs)).length ≤
      400 * (B + 1) * L + 15 := by
    unfold RegisterPotentialRoute.budget
    rw [List.length_map]
    have := Nat.mul_le_mul_left (400 * (B + 1)) hlen
    omega
  have b3 := Nat.mul_le_mul_left (36 * W + 70) hR
  simp only [itemBudget, RegisterRouteLookup.budget, List.length_cons, List.length_nil] at b1 b2 ⊢
  omega

/-- The vertex words whose propagated value is at least one, in stored order. -/
theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {R L : ℕ} {h : Heap} (hh : Valid h) {np dp : Ptr} {nodes : List (Bits W)} {data : Data W B}
    (hR : data.routes.length ≤ R)
    (hL : ∀ x, (RegisterRouteLookup.lookup x data.routes).length ≤ L)
    (hn : WordsAt h np nodes) (hd : DataAt h dp data) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (nodes.filter (keep data)) ∧
      Within code h (initialRegisters [.pointer np, .pointer dp]) (code d.filter) [.pointer q] out
        (budget W B R data.recs.length L nodes.length) := by
  obtain ⟨out, q, e, v, hq, run⟩ := RegisterListFilter.compiled_const code d.filter d.item
    hm.2.2.2.2.2.2 (fun h p (x : Bits W) => BitsAt h p x) DataAt (fun he _ _ hx => hx.mono he)
    (fun he _ _ hx => hx.mono he) keep (itemBudget W B R data.recs.length L) hh hn hd
    (fun hv _ _ _ hx hd' => item_compiled code d hm hv hR (hL _) hx hd')
  exact ⟨out, q, e, v, hq, run⟩

end WeightedMIS.RegisterThresholdVertices
