module

public import WeightedMIS.RegisterFirstEdge
public import WeightedMIS.ResidualWords
public import WeightedMIS.RegisterListMap

/-!
# Refilling route arcs with original edge counts

The residual search stores route arcs whose capacity word is the search
threshold. For every stored arc `(u, v)` the first-edge scan over the
edge-count records finds the first record joining `u` and `v`; a new arc
record `.pair u (.pair v count)` sharing the two endpoint words and the
record's count word is allocated. If no record matches, the supplied default
word is used. A map traversal applies this to a whole stored route, keeping
its order.
-/

@[expose] public section

namespace WeightedMIS.RegisterRouteCounts

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ResidualWords
open WeightedMIS.RegisterFirstEdge

variable {W B : ℕ}

/-- The count word of the first record joining the two endpoints, or the default. -/
def countOf (zero : Bits B) (recs : List (Record W B)) (u v : Bits W) : Bits B :=
  ((recs.find? (pred (u, v))).map Prod.snd).getD zero

/-- The arc with its capacity replaced by the original edge count. -/
def refill (zero : Bits B) (recs : List (Record W B)) (a : Arc W 1) : Arc W B :=
  ⟨a.source, a.target, countOf zero recs a.source a.target⟩

/-- Refill data `.pair records defaultWord`. -/
def DataAt (h : Heap) (p : Ptr) (d : List (Record W B) × Bits B) : Prop :=
  ∃ rp zp, h[p]? = some (.pair rp zp) ∧ RecordsAt h rp d.1 ∧ BitsAt h zp d.2

theorem DataAt.mono {h h' : Heap} (he : Extends h h') {p : Ptr}
    {d : List (Record W B) × Bits B} (hd : DataAt h p d) : DataAt h' p d := by
  obtain ⟨rp, zp, c, hr, hz⟩ := hd
  exact ⟨rp, zp, he.lookup c, hr.mono he, hz.mono he⟩

variable {p : ℕ}

/-- Allocate the refilled arc from source (2), target (4) and the count register. -/
def finishBody (count : Register) : Command p :=
  .allocate 13 (.pair (.register 4) (.register count))
    (.allocate 14 (.pair (.register 2) (.register 13)) (.ret [.register 14]))

/-- Arguments: stored arc, refill data. Result: the refilled arc. -/
def refillBody (find : Fin p) : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    pair := .load (.register 3) 4 5 15 { CompiledTrie.failCases with
      pair := .load (.register 1) 6 7 15 { CompiledTrie.failCases with
        pair := .allocate 8 (.pair (.register 2) (.register 4))
          (.call find [.register 6, .register 8] [9, 10]
            (.branch (.register 9)
              (.load (.register 10) 11 12 15 { CompiledTrie.failCases with
                pair := finishBody 12 })
              (finishBody 7))) } } }

structure Procedures (p : ℕ) where
  edge : RegisterFirstEdge.Procedures p
  item : Fin p
  map : Fin p

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  d.edge.Matches code ∧
  code d.item = refillBody d.edge.find ∧
  code d.map = RegisterListMap.body d.map d.item

def itemBudget (W M : ℕ) : ℕ := findBudget W M + 80

def budget (W M len : ℕ) : ℕ := (itemBudget W M + 35) * len + 13

theorem finish_within (code : Code p) {h : Heap} (hh : Valid h) {regs : Registers}
    (count : Register) {sp tp cp : Ptr} {u v : Bits W} {c : Bits B}
    (h2 : regs 2 = .pointer sp) (h4 : regs 4 = .pointer tp) (hc : regs count = .pointer cp)
    (hu : BitsAt h sp u) (hv : BitsAt h tp v) (hcw : BitsAt h cp c) :
    ∃ out q, Extends h out ∧ Valid out ∧ ArcAt out q (⟨u, v, c⟩ : Arc W B) ∧
      Within code h regs (finishBody count) [.pointer q] out 19 := by
  let H1 := h ++ [Cell.pair tp cp]
  let H2 := H1 ++ [Cell.pair sp h.length]
  obtain ⟨e1, v1, q1⟩ := allocate_fits hh (pair_fits hv.allocated hcw.allocated)
  obtain ⟨e2, v2, q2⟩ := allocate_fits v1 (pair_fits (h := H1) (a := sp) (b := h.length)
    (lt_of_ext e1 hu.allocated) (by simp [H1]))
  refine ⟨H2, H1.length, e1.trans e2, v2,
    ⟨sp, h.length, tp, cp, q2, e2.lookup q1, (hu.mono e1).mono e2, (hv.mono e1).mono e2,
      (hcw.mono e1).mono e2⟩, ?_⟩
  let r1 := Function.update regs 13 (.pointer h.length)
  let r2 := Function.update r1 14 (.pointer H1.length)
  have last : Within code H2 r2 (.ret [.register 14]) [.pointer H1.length] H2 3 := by
    simpa [r2, values, Atom.eval] using Within.ret code H2 r2 [.register 14]
  have a2 := Within.allocate (regs := r1) (dst := 14) (h := H1)
    (expr := .pair (.register 2) (.register 13)) (c := .pair sp h.length)
    (by simp [CellExpr.eval, Atom.eval, r1, h2, Value.asPointer]) last
  have a1 := Within.allocate (regs := regs) (dst := 13) (h := h)
    (expr := .pair (.register 4) (.register count)) (c := .pair tp cp)
    (by simp [CellExpr.eval, Atom.eval, h4, hc, Value.asPointer]) a2
  exact a1.mono (by simp [CellExpr.args])

theorem item_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {h : Heap} (hh : Valid h) {ap dp : Ptr} {a : Arc W 1} {data : List (Record W B) × Bits B}
    (ha : ArcAt h ap a) (hd : DataAt h dp data) :
    ∃ out q, Extends h out ∧ Valid out ∧ ArcAt out q (refill data.2 data.1 a) ∧
      Within code h (initialRegisters [.pointer ap, .pointer dp]) (code d.item) [.pointer q] out
        (itemBudget W data.1.length) := by
  obtain ⟨recs, zero⟩ := data
  obtain ⟨sp, tail, tp, cp, c1, c2, hs, ht, -⟩ := ha
  obtain ⟨rp, zp, c3, hr, hz⟩ := hd
  simp only at hr hz
  let H1 := h ++ [Cell.pair sp tp]
  obtain ⟨e1, v1, q1⟩ := allocate_fits hh (pair_fits hs.allocated ht.allocated)
  have hq : QueryAt H1 h.length (a.source, a.target) := ⟨sp, tp, q1, hs.mono e1, ht.mono e1⟩
  obtain ⟨H2, fp, e2, v2, hfound, frun⟩ := find_compiled code d.edge hm.1 v1 (hr.mono e1) hq
  have e12 := e1.trans e2
  let regs := initialRegisters [Value.pointer ap, .pointer dp]
  let s1 := loadRegisters regs 2 3 15 (.pair sp tail)
  let s2 := loadRegisters s1 4 5 15 (.pair tp cp)
  let s3 := loadRegisters s2 6 7 15 (.pair rp zp)
  let s4 := Function.update s3 8 (.pointer h.length)
  let s5 := bindResults s4 [9, 10]
    [.flag (recs.find? (pred (a.source, a.target))).isSome, .pointer fp]
  have tailRun : ∃ out q, Extends H2 out ∧ Valid out ∧ ArcAt out q (refill zero recs a) ∧
      Within code H2 s5
        (.branch (.register 9)
          (.load (.register 10) 11 12 15 { CompiledTrie.failCases with pair := finishBody 12 })
          (finishBody 7)) [.pointer q] out 35 := by
    cases hf : recs.find? (pred (a.source, a.target)) with
    | some r =>
      obtain ⟨rep, rcp, rcell, -, hrc⟩ := hfound r hf
      let t1 := loadRegisters s5 11 12 15 (.pair rep rcp)
      obtain ⟨out, q, e3, v3, harc, frun'⟩ := finish_within code v2 (regs := t1) 12
        (sp := sp) (tp := tp) (cp := rcp)
        (by simp [t1, s5, s4, s3, s2, s1, bindResults, loadRegisters, decoded])
        (by simp [t1, s5, s4, s3, s2, s1, bindResults, loadRegisters, decoded])
        (by simp [t1, loadRegisters, decoded]) (hs.mono e12) (ht.mono e12) hrc
      refine ⟨out, q, e3, v3, by simpa [refill, countOf, hf] using harc, ?_⟩
      have l := Within.load (regs := s5) (address := .register 10) (first := 11) (second := 12)
        (bit := 15) (branches := { CompiledTrie.failCases with pair := finishBody 12 })
        (by simp [s5, bindResults, Atom.eval, hf]) rcell frun'
      have b := Within.branch (b := true) (test := .register 9) (regs := s5)
        (no := finishBody 7) (by simp [s5, bindResults, Atom.eval, hf]) l
      exact b.mono (by omega)
    | none =>
      obtain ⟨out, q, e3, v3, harc, frun'⟩ := finish_within code v2 (regs := s5) 7
        (sp := sp) (tp := tp) (cp := zp)
        (by simp [s5, s4, s3, s2, s1, bindResults, loadRegisters, decoded])
        (by simp [s5, s4, s3, s2, s1, bindResults, loadRegisters, decoded])
        (by simp [s5, s4, s3, bindResults, loadRegisters, decoded]) (hs.mono e12) (ht.mono e12)
        (hz.mono e12)
      refine ⟨out, q, e3, v3, by simpa [refill, countOf, hf] using harc, ?_⟩
      have b := Within.branch (b := false) (test := .register 9) (regs := s5)
        (yes := .load (.register 10) 11 12 15 { CompiledTrie.failCases with pair := finishBody 12 })
        (by simp [s5, bindResults, Atom.eval, hf]) frun'
      exact b.mono (by omega)
  obtain ⟨out, q, e3, v3, harc, trun⟩ := tailRun
  refine ⟨out, q, e12.trans e3, v3, harc, ?_⟩
  have fargs : values s4 [.register 6, .register 8] = [.pointer rp, .pointer h.length] := by
    simp [s4, s3, s2, s1, regs, loadRegisters, decoded, values, Atom.eval]
  have fcall := Within.call (procedure := d.edge.find) (regs := s4)
    (arguments := [.register 6, .register 8]) (results := [9, 10])
    (by simpa only [fargs] using frun) trun
  have al := Within.allocate (regs := s3) (dst := 8) (h := h)
    (expr := .pair (.register 2) (.register 4)) (c := .pair sp tp)
    (by simp [CellExpr.eval, Atom.eval, s3, s2, s1, loadRegisters, decoded, Value.asPointer]) fcall
  have l3 := Within.load (regs := s2) (address := .register 1) (first := 6) (second := 7)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .allocate 8 (.pair (.register 2) (.register 4))
        (.call d.edge.find [.register 6, .register 8] [9, 10]
          (.branch (.register 9)
            (.load (.register 10) 11 12 15 { CompiledTrie.failCases with pair := finishBody 12 })
            (finishBody 7))) })
    (by simp [s2, s1, regs, loadRegisters, decoded, initialRegisters, Atom.eval]) c3 al
  have l2 := Within.load (regs := s1) (address := .register 3) (first := 4) (second := 5)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 1) 6 7 15 { CompiledTrie.failCases with
        pair := .allocate 8 (.pair (.register 2) (.register 4))
          (.call d.edge.find [.register 6, .register 8] [9, 10]
            (.branch (.register 9)
              (.load (.register 10) 11 12 15 { CompiledTrie.failCases with pair := finishBody 12 })
              (finishBody 7))) } })
    (by simp [s1, loadRegisters, decoded, Atom.eval]) c2 l3
  have l1 := Within.load (regs := regs) (address := .register 0) (first := 2) (second := 3)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 3) 4 5 15 { CompiledTrie.failCases with
        pair := .load (.register 1) 6 7 15 { CompiledTrie.failCases with
          pair := .allocate 8 (.pair (.register 2) (.register 4))
            (.call d.edge.find [.register 6, .register 8] [9, 10]
              (.branch (.register 9)
                (.load (.register 10) 11 12 15 { CompiledTrie.failCases with
                  pair := finishBody 12 })
                (finishBody 7))) } } })
    (by simp [regs, initialRegisters, Atom.eval]) c1 l2
  rw [hm.2.1]
  exact l1.mono (by simp [itemBudget, CellExpr.args]; omega)

/-- Refill a whole stored route. -/
theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {h : Heap} (hh : Valid h) {lp dp : Ptr} {arcs : List (Arc W 1)}
    {data : List (Record W B) × Bits B} (hl : TableAt h lp arcs) (hd : DataAt h dp data) :
    ∃ out q, Extends h out ∧ Valid out ∧ TableAt out q (arcs.map (refill data.2 data.1)) ∧
      Within code h (initialRegisters [.pointer lp, .pointer dp]) (code d.map) [.pointer q] out
        (budget W data.1.length arcs.length) := by
  obtain ⟨out, q, e, v, hq, run⟩ := RegisterListMap.compiled_const code d.map d.item hm.2.2
    ResidualWords.ArcAt DataAt ResidualWords.ArcAt (fun he _ _ hx => hx.mono he)
    (fun he _ _ hx => hx.mono he)
    (fun he _ _ hx => hx.mono he) (fun _ hx => hx.allocated)
    (fun data a => refill data.2 data.1 a) (itemBudget W data.1.length) hh hl hd
    (fun hv _ _ _ hx hd' => item_compiled code d hm hv hx hd')
  exact ⟨out, q, e, v, hq, run⟩

end WeightedMIS.RegisterRouteCounts
