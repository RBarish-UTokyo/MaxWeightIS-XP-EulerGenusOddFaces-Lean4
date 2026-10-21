module

public import WeightedMIS.CompiledTemplates
public import WeightedMIS.RegisterMachineFrames

/-! # Checked constant-size template primitives -/

@[expose] public section

namespace WeightedMIS.CompiledTemplates

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.CompiledTrie WeightedMIS.Walks

variable {p : ℕ} {Row Metadata : Type*} {width : ℕ}
    {key : State Row → Bits width} {metaAt : Heap → Ptr → Metadata → Prop}

theorem StubAt.mono {h h' : Heap} (ext : Extends h h') {ptr s}
    (hs : StubAt key h ptr s) : StubAt key h' ptr s := by
  obtain ⟨row, minus, plus, hc, hr, hm, hp⟩ := hs
  exact ⟨row, minus, plus, ext.lookup hc, ext.lookup hr, hm.mono ext, hp.mono ext⟩

theorem ColumnAt.mono {h h' : Heap} (ext : Extends h h') {ptr c}
    (hc : ColumnAt key h ptr c) : ColumnAt key h' ptr c := by
  cases hc with
  | zero cell => exact .zero (ext.lookup cell)
  | one cell stub => exact .one (ext.lookup cell) (stub.mono ext)
  | two cell first second => exact .two (ext.lookup cell) (first.mono ext) (second.mono ext)

theorem TemplateAt.mono
    (mono : ∀ {h h' ptr a}, Extends h h' → metaAt h ptr a → metaAt h' ptr a)
    {h h' : Heap} (ext : Extends h h') {ptr a} (ht : TemplateAt key metaAt h ptr a) :
    TemplateAt key metaAt h' ptr a := by
  obtain ⟨source, target, mp, inside, hc, hi, hs, ht, hm⟩ := ht
  exact ⟨source, target, mp, inside, ext.lookup hc, ext.lookup hi,
    hs.mono ext, ht.mono ext, mono ext hm⟩

theorem EdgeAt.mono
    (mono : ∀ {h h' ptr a}, Extends h h' → metaAt h ptr a → metaAt h' ptr a)
    {h h' : Heap} (ext : Extends h h') {ptr a} (ht : EdgeAt key metaAt h ptr a) :
    EdgeAt key metaAt h' ptr a := by
  obtain ⟨column, mp, hc, hcol, hm⟩ := ht
  exact ⟨column, mp, ext.lookup hc, hcol.mono ext, mono ext hm⟩

/-- Two actual tagged loads choose the opposite and own signed state keys. -/
theorem stub_within (code : Code p) {h : Heap} {regs : Registers} {ptr : Ptr}
    {s : Stub Row} (hreg : regs 0 = .pointer ptr) (hs : StubAt key h ptr s) :
    ∃ oppositeKey ownKey, Within code h regs stubBody
      [.pointer oppositeKey, .pointer ownKey] h 28 ∧
      BitsAt h oppositeKey (key (some (opposite s))) ∧ BitsAt h ownKey (key (some s)) := by
  obtain ⟨row, minus, plus, hc, hr, hm, hp⟩ := hs
  rcases s with ⟨v, sign⟩
  cases sign
  case false =>
    let r1 := loadRegisters regs 2 3 4 (.bit false row)
    let r2 := loadRegisters r1 5 6 7 (.pair minus plus)
    have last : Within code h r2 (.ret [.register 6, .register 5])
        [.pointer plus, .pointer minus] h 5 := by
      simpa [values, Atom.eval, r2, loadRegisters, decoded] using
        Within.ret code h r2 [.register 6, .register 5]
    have branch := Within.branch (test := .register 4)
      (yes := .ret [.register 5, .register 6])
      (no := .ret [.register 6, .register 5]) (b := false)
      (by simp [Atom.eval, r2, r1, loadRegisters, decoded]) last
    have pairLoad := Within.load (address := .register 2) (first := 5) (second := 6) (bit := 7)
      (branches := ⟨.fail, .fail, .fail, .fail, .fail,
        .branch (.register 4) (.ret [.register 5, .register 6]) (.ret [.register 6, .register 5])⟩)
      (by simp [Atom.eval, r1, loadRegisters, decoded]) hr branch
    have bitLoad := Within.load (address := .register 0) (first := 2) (second := 3) (bit := 4)
      (branches := ⟨.fail, .load (.register 2) 5 6 7
        ⟨.fail, .fail, .fail, .fail, .fail, .branch (.register 4)
          (.ret [.register 5, .register 6]) (.ret [.register 6, .register 5])⟩,
        .fail, .fail, .fail, .fail⟩)
      (by simpa [Atom.eval] using hreg) hc pairLoad
    exact ⟨plus, minus, bitLoad, hp, hm⟩
  case true =>
    let r1 := loadRegisters regs 2 3 4 (.bit true row)
    let r2 := loadRegisters r1 5 6 7 (.pair minus plus)
    have last : Within code h r2 (.ret [.register 5, .register 6])
        [.pointer minus, .pointer plus] h 5 := by
      simpa [values, Atom.eval, r2, loadRegisters, decoded] using
        Within.ret code h r2 [.register 5, .register 6]
    have branch := Within.branch (test := .register 4)
      (yes := .ret [.register 5, .register 6])
      (no := .ret [.register 6, .register 5]) (b := true)
      (by simp [Atom.eval, r2, r1, loadRegisters, decoded]) last
    have pairLoad := Within.load (address := .register 2) (first := 5) (second := 6) (bit := 7)
      (branches := ⟨.fail, .fail, .fail, .fail, .fail,
        .branch (.register 4) (.ret [.register 5, .register 6]) (.ret [.register 6, .register 5])⟩)
      (by simp [Atom.eval, r1, loadRegisters, decoded]) hr branch
    have bitLoad := Within.load (address := .register 0) (first := 2) (second := 3) (bit := 4)
      (branches := ⟨.fail, .load (.register 2) 5 6 7
        ⟨.fail, .fail, .fail, .fail, .fail, .branch (.register 4)
          (.ret [.register 5, .register 6]) (.ret [.register 6, .register 5])⟩,
        .fail, .fail, .fail, .fail⟩)
      (by simpa [Atom.eval] using hreg) hc pairLoad
    exact ⟨minus, plus, bitLoad, hm, hp⟩

/-- The exact three-cell extension made by the finite emitter. -/
def emittedHeap (h : Heap) (source target mp tail : Ptr) : Heap :=
  ((h ++ [.pair target mp]) ++ [.pair source h.length]) ++ [.cons (h.length + 1) tail]

theorem emit_within (code : Code p) (h : Heap) (regs : Registers) (source target mp tail : Ptr)
    (h0 : regs 0 = .pointer source) (h1 : regs 1 = .pointer target)
    (h2 : regs 2 = .pointer mp) (h3 : regs 3 = .pointer tail) :
    Within code h regs emitBody [.pointer (h.length + 2)]
      (emittedHeap h source target mp tail) 27 := by
  let h1' := h ++ [.pair target mp]
  let h2' := h1' ++ [.pair source h.length]
  let r1 := Function.update regs 4 (.pointer h.length)
  let r2 := Function.update r1 5 (.pointer (h.length + 1))
  let r3 := Function.update r2 6 (.pointer (h.length + 2))
  have last : Within code (emittedHeap h source target mp tail) r3
      (.ret [.register 6]) [.pointer (h.length + 2)] (emittedHeap h source target mp tail) 3 := by
    simpa [values, Atom.eval, r3] using Within.ret code _ r3 [.register 6]
  have a3 := Within.allocate (h := h2') (regs := r2) (dst := 6)
    (expr := .cons (.register 5) (.register 3)) (c := .cons (h.length + 1) tail)
    (by simp [CellExpr.eval, Atom.eval, Value.asPointer, r2, r1, h3])
    (by simpa [h2', h1', r3, emittedHeap] using last)
  have a2 := Within.allocate (h := h1') (regs := r1) (dst := 5)
    (expr := .pair (.register 0) (.register 4)) (c := .pair source h.length)
    (by simp [CellExpr.eval, Atom.eval, Value.asPointer, r1, h0])
    (by simpa [h2', h1', r2] using a3)
  simpa [emitBody, emittedHeap, CellExpr.args, List.append_assoc] using
    (Within.allocate (dst := 4) (expr := .pair (.register 1) (.register 2))
      (by simp [CellExpr.eval, Atom.eval, Value.asPointer, h1, h2]) a2)

/-- The emitted record represents precisely the supplied actual template. -/
theorem emit_refines
    (mono : ∀ {h h' ptr a}, Extends h h' → metaAt h ptr a → metaAt h' ptr a)
    {h : Heap} (hh : Valid h) {source target mp tail : Ptr} {xs : List Ptr}
    {a : Template Row Metadata} (hs : BitsAt h source (key a.source))
    (ht : BitsAt h target (key a.target)) (hm : metaAt h mp a.metadata)
    (hmalloc : mp < h.length) (hl : ListAt h tail xs) :
    Valid (emittedHeap h source target mp tail) ∧
    Extends h (emittedHeap h source target mp tail) ∧
    ListAt (emittedHeap h source target mp tail) (h.length + 2) ((h.length + 1) :: xs) ∧
    TemplateAt key metaAt (emittedHeap h source target mp tail) (h.length + 1) a := by
  let h1 := h ++ [.pair target mp]
  let h2 := h1 ++ [.pair source h.length]
  have s1 := safe_allocate h hh (.pair target mp) (by
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ht.allocated
    · exact hmalloc)
  have s2 := safe_allocate h1 s1.2.1 (.pair source h.length) (by
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact lt_of_lt_of_le hs.allocated s1.1.length_le
    · simp [h1])
  have s3 := allocate_cons s2.2.1 (a := h.length + 1)
    (by simp [Program.allocate, h1]) (hl.mono (s1.1.trans s2.1))
  have ext : Extends h (emittedHeap h source target mp tail) := s1.1.trans (s2.1.trans s3.1.1)
  refine ⟨s3.1.2.1, ext, ?_, source, target, mp, h.length, ?_, ?_,
    hs.mono ext, ht.mono ext, mono ext hm⟩
  · simpa [Program.allocate, h2, h1, emittedHeap] using s3.2
  · have hc : h2[h.length + 1]? = some (.pair source h.length) := by simp [h2, h1]
    exact s3.1.1.lookup hc
  · have hc : h1[h.length]? = some (.pair target mp) := by simp [h1]
    exact (s2.1.trans s3.1.1).lookup hc

end WeightedMIS.CompiledTemplates
