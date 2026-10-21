module

public import WeightedMIS.RibbonTable
public import WeightedMIS.CompiledTrie
public import WeightedMIS.EfficientSearchCodeBounds
public import WeightedMIS.RegisterComparator

/-!
# Closed register code for stored flag keys

A flag key `side :: endpoint :: edge` is a chain of two bit cells followed by
the stored edge word. Splitting a key performs two loads and shares the edge
word; crossing and turning along an edge allocate at most two bit cells and
share the rest of the key. Every procedure has a constant event budget.
-/

@[expose] public section

namespace WeightedMIS.RegisterFlagKeys

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable

variable {p : ℕ}

/-- The equality flag of the comparator decides equality of equal-width words. -/
theorem compare_eq_decide {n : ℕ} (a b : Bits n) :
    decide ((Bits.compare a b).1 = .eq) = decide (a = b) := by
  apply decide_eq_decide.mpr
  rw [(Bits.compare_correct a b).2.1]
  exact ⟨fun h => value_injective h, fun h => h ▸ rfl⟩

/-- Evaluate register lookups after loads, calls, copies, and allocations. -/
syntax "reg_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| reg_simp) => `(tactic| (set_option linter.unusedSimpArgs false in
      simp [values, Atom.eval, loadRegisters, decoded, bindResults, initialRegisters,
        CellExpr.eval, Value.asPointer, Value.asFlag, RegisterComparator.flags,
        compare_eq_decide]))
  | `(tactic| reg_simp [$args,*]) => `(tactic| (set_option linter.unusedSimpArgs false in
      simp [values, Atom.eval, loadRegisters, decoded, bindResults, initialRegisters,
        CellExpr.eval, Value.asPointer, Value.asFlag, RegisterComparator.flags,
        compare_eq_decide, $args,*]))

/-! ## Allocation facts -/

/-- One allocated bit cell extends a stored word by one leading bit. -/
theorem alloc_bit {h : Heap} (hh : Valid h) {n : ℕ} {t : Ptr} {bits : Bits n} (b : Bool)
    (ht : BitsAt h t bits) :
    Extends h (h ++ [.bit b t]) ∧ Valid (h ++ [.bit b t]) ∧
      BitsAt (h ++ [.bit b t]) h.length (.cons b bits) := by
  obtain ⟨hs, hb⟩ := allocate_bit hh b ht
  exact ⟨hs.1, hs.2.1, by simpa [Program.allocate] using hb⟩

/-- One allocated pair cell of allocated fields keeps the heap valid. -/
theorem alloc_pair {h : Heap} (hh : Valid h) {a b : Ptr} (ha : a < h.length)
    (hb : b < h.length) :
    Extends h (h ++ [.pair a b]) ∧ Valid (h ++ [.pair a b]) ∧
      (h ++ [.pair a b])[h.length]? = some (.pair a b) := by
  have hs := safe_allocate h hh (.pair a b) (by
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> assumption)
  refine ⟨hs.1, hs.2.1, ?_⟩
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- A return whose atoms evaluate to the expected values. -/
theorem ret_values {code : Code p} {h : Heap} {regs : Registers} {outs : List Atom}
    {vs : List Value} {b : ℕ} (hv : values regs outs = vs) (hb : 1 + 2 * outs.length ≤ b) :
    Within code h regs (.ret outs) vs h b :=
  hv ▸ (Within.ret code h regs outs).mono hb

/-- A call whose argument atoms evaluate to the stated values. -/
theorem call_of {code : Code p} {h mid final : Heap} {regs : Registers}
    {procedure : Fin p} {arguments : List Atom} {args : List Value} {results : List Register}
    {next : Command p} {returned outputs : List Value} {cb rb : ℕ}
    (hargs : values regs arguments = args)
    (body : Within code h (initialRegisters args) (code procedure) returned mid cb)
    (rest : Within code mid (bindResults regs results returned) next outputs final rb) :
    Within code h regs (.call procedure arguments results next) outputs final
      (1 + 2 * arguments.length + cb + rb) :=
  Within.call (hargs ▸ body) rest

/-! ## Procedure bodies -/

/-- Argument 0 = key; results are the side flag, the endpoint flag, and the
shared edge word. -/
def splitBody : Command p :=
  .load (.register 0) 1 2 3 { CompiledTrie.failCases with
    bit := .load (.register 1) 4 5 6 { CompiledTrie.failCases with
      bit := .ret [.register 3, .register 6, .register 4] } }

/-- Arguments 0 = side flag, 1 = endpoint flag, 2 = edge word. -/
def mkBody : Command p :=
  .allocate 3 (.bit (.register 1) (.register 2))
    (.allocate 4 (.bit (.register 0) (.register 3)) (.ret [.register 4]))

/-- Argument 0 = key; the result is the shared edge word. -/
def edgePartBody : Command p :=
  .load (.register 0) 1 2 3 { CompiledTrie.failCases with
    bit := .load (.register 1) 4 5 6 { CompiledTrie.failCases with
      bit := .ret [.register 4] } }

/-- Argument 0 = key; the result flips the side bit. -/
def acrossBody : Command p :=
  .load (.register 0) 1 2 3 { CompiledTrie.failCases with
    bit := .branch (.register 3)
      (.allocate 4 (.bit (.flag false) (.register 1)) (.ret [.register 4]))
      (.allocate 4 (.bit (.flag true) (.register 1)) (.ret [.register 4])) }

/-- Argument 0 = key; the result flips the endpoint bit. -/
def alongBody : Command p :=
  .load (.register 0) 1 2 3 { CompiledTrie.failCases with
    bit := .load (.register 1) 4 5 6 { CompiledTrie.failCases with
      bit := .branch (.register 6)
        (.allocate 7 (.bit (.flag false) (.register 4))
          (.allocate 8 (.bit (.register 3) (.register 7)) (.ret [.register 8])))
        (.allocate 7 (.bit (.flag true) (.register 4))
          (.allocate 8 (.bit (.register 3) (.register 7)) (.ret [.register 8]))) } }

/-! ## Correctness -/

theorem split_compiled (code : Code p) (self : Fin p) (hself : code self = splitBody)
    {W : ℕ} {h : Heap} {kp : Ptr} {k : Bits (W + 2)} (hk : BitsAt h kp k) :
    ∃ wp, BitsAt h wp (edgePart k) ∧
      Within code h (initialRegisters [.pointer kp]) (code self)
        [.flag (sideBit k), .flag (endBit k), .pointer wp] h 27 := by
  rcases k with _ | ⟨s, _ | ⟨t, w⟩⟩
  cases hk with
  | @cons _ t1 _ _ _ c1 h1 =>
  cases h1 with
  | @cons _ t2 _ _ _ c2 h2 =>
  refine ⟨t2, h2, ?_⟩
  rw [hself]
  apply Within.load (budget := 17) (pointer := kp) (c := .bit s t1)
  · simp [Atom.eval, initialRegisters]
  · exact c1
  apply Within.load (budget := 7) (pointer := t1) (c := .bit t t2)
  · simp [Atom.eval, loadRegisters, decoded]
  · exact c2
  exact ret_values (by simp [values, Atom.eval, loadRegisters, decoded, sideBit, endBit]) (by simp)

theorem edgePart_compiled (code : Code p) (self : Fin p) (hself : code self = edgePartBody)
    {W : ℕ} {h : Heap} {kp : Ptr} {k : Bits (W + 2)} (hk : BitsAt h kp k) :
    ∃ wp, BitsAt h wp (edgePart k) ∧
      Within code h (initialRegisters [.pointer kp]) (code self) [.pointer wp] h 23 := by
  rcases k with _ | ⟨s, _ | ⟨t, w⟩⟩
  cases hk with
  | @cons _ t1 _ _ _ c1 h1 =>
  cases h1 with
  | @cons _ t2 _ _ _ c2 h2 =>
  refine ⟨t2, h2, ?_⟩
  rw [hself]
  apply Within.load (budget := 13) (pointer := kp) (c := .bit s t1)
  · simp [Atom.eval, initialRegisters]
  · exact c1
  apply Within.load (budget := 3) (pointer := t1) (c := .bit t t2)
  · simp [Atom.eval, loadRegisters, decoded]
  · exact c2
  exact ret_values (by simp [values, Atom.eval, loadRegisters, decoded]) (by simp)

theorem mk_compiled (code : Code p) (self : Fin p) (hself : code self = mkBody)
    {W : ℕ} {h : Heap} (hh : Valid h) {wp : Ptr} {w : Bits W} (hw : BitsAt h wp w) (s t : Bool) :
    ∃ out q, Extends h out ∧ Valid out ∧ BitsAt out q (mkKey s t w) ∧
      Within code h (initialRegisters [.flag s, .flag t, .pointer wp]) (code self)
        [.pointer q] out 19 := by
  obtain ⟨e1, v1, b1⟩ := alloc_bit hh t hw
  obtain ⟨e2, v2, b2⟩ := alloc_bit v1 s b1
  refine ⟨_, _, e1.trans e2, v2, b2, ?_⟩
  rw [hself]
  apply Within.allocate (budget := 11) (c := .bit t wp)
  · simp [CellExpr.eval, Atom.eval, initialRegisters, Value.asFlag, Value.asPointer]
  apply Within.allocate (budget := 3) (c := .bit s h.length)
  · simp [CellExpr.eval, Atom.eval, initialRegisters, Value.asFlag, Value.asPointer]
  exact ret_values (by simp [values, Atom.eval]) (by simp)

theorem across_compiled (code : Code p) (self : Fin p) (hself : code self = acrossBody)
    {W : ℕ} {h : Heap} (hh : Valid h) {kp : Ptr} {k : Bits (W + 2)} (hk : BitsAt h kp k) :
    ∃ out q, Extends h out ∧ Valid out ∧ BitsAt out q (acrossKey k) ∧
      Within code h (initialRegisters [.pointer kp]) (code self) [.pointer q] out 24 := by
  rcases k with _ | ⟨s, rest⟩
  cases hk with
  | @cons _ t1 _ _ _ c1 h1 =>
  obtain ⟨e1, v1, b1⟩ := alloc_bit hh (!s) h1
  refine ⟨_, _, e1, v1, b1, ?_⟩
  rw [hself]
  apply Within.load (budget := 14) (pointer := kp) (c := .bit s t1)
  · simp [Atom.eval, initialRegisters]
  · exact c1
  apply Within.branch (budget := 11) (b := s)
  · simp [Atom.eval, loadRegisters, decoded]
  cases s
  · apply Within.allocate (budget := 3) (c := .bit true t1)
    · simp [CellExpr.eval, Atom.eval, loadRegisters, decoded, Value.asFlag, Value.asPointer]
    exact ret_values (by simp [values, Atom.eval, loadRegisters, decoded]) (by simp)
  · apply Within.allocate (budget := 3) (c := .bit false t1)
    · simp [CellExpr.eval, Atom.eval, loadRegisters, decoded, Value.asFlag, Value.asPointer]
    exact ret_values (by simp [values, Atom.eval, loadRegisters, decoded]) (by simp)

theorem along_compiled (code : Code p) (self : Fin p) (hself : code self = alongBody)
    {W : ℕ} {h : Heap} (hh : Valid h) {kp : Ptr} {k : Bits (W + 2)} (hk : BitsAt h kp k) :
    ∃ out q, Extends h out ∧ Valid out ∧ BitsAt out q (alongKey k) ∧
      Within code h (initialRegisters [.pointer kp]) (code self) [.pointer q] out 42 := by
  rcases k with _ | ⟨s, _ | ⟨t, w⟩⟩
  cases hk with
  | @cons _ t1 _ _ _ c1 h1 =>
  cases h1 with
  | @cons _ t2 _ _ _ c2 h2 =>
  obtain ⟨e1, v1, b1⟩ := alloc_bit hh (!t) h2
  obtain ⟨e2, v2, b2⟩ := alloc_bit v1 s b1
  refine ⟨_, _, e1.trans e2, v2, b2, ?_⟩
  rw [hself]
  apply Within.load (budget := 32) (pointer := kp) (c := .bit s t1)
  · simp [Atom.eval, initialRegisters]
  · exact c1
  apply Within.load (budget := 22) (pointer := t1) (c := .bit t t2)
  · simp [Atom.eval, loadRegisters, decoded]
  · exact c2
  apply Within.branch (budget := 19) (b := t)
  · simp [Atom.eval, loadRegisters, decoded]
  cases t
  · apply Within.allocate (budget := 11) (c := .bit true t2)
    · simp [CellExpr.eval, Atom.eval, loadRegisters, decoded, Value.asFlag, Value.asPointer]
    apply Within.allocate (budget := 3) (c := .bit s h.length)
    · simp [CellExpr.eval, Atom.eval, loadRegisters, decoded, Value.asFlag, Value.asPointer]
    exact ret_values (by simp [values, Atom.eval, loadRegisters, decoded]) (by simp)
  · apply Within.allocate (budget := 11) (c := .bit false t2)
    · simp [CellExpr.eval, Atom.eval, loadRegisters, decoded, Value.asFlag, Value.asPointer]
    apply Within.allocate (budget := 3) (c := .bit s h.length)
    · simp [CellExpr.eval, Atom.eval, loadRegisters, decoded, Value.asFlag, Value.asPointer]
    exact ret_values (by simp [values, Atom.eval, loadRegisters, decoded]) (by simp)

end WeightedMIS.RegisterFlagKeys
