module

public import WeightedMIS.BinaryRationalInterface
public import WeightedMIS.RegisterAdder

/-!
# Shared heap representation of rational words

A rational occupies two record cells pointing to its separately stored
numerator and denominator words. Fixed finite bodies read and construct the
record; arithmetic procedures receive the sign and the two word pointers.
-/

@[expose] public section

namespace WeightedMIS.StoredRational

open PointerMemory RegisterMachine EfficientSearch

variable {p width : ℕ}

def At (h : Heap) (rp : Ptr) (q : BinaryRational.Word width) : Prop :=
  ∃ sp np dp, h[rp]? = some (.pair sp dp) ∧ h[sp]? = some (.bit q.negative np) ∧
    BitsAt h np q.magnitude ∧ BitsAt h dp q.denominator

theorem At.mono {h out : Heap} (ext : Extends h out) {rp : Ptr}
    {q : BinaryRational.Word width} (hq : At h rp q) : At out rp q := by
  obtain ⟨sp, np, dp, pair, bit, num, den⟩ := hq
  exact ⟨sp, np, dp, ext.lookup pair, ext.lookup bit, num.mono ext, den.mono ext⟩

theorem At.allocated {h : Heap} {rp : Ptr} {q : BinaryRational.Word width}
    (hq : At h rp q) : rp < h.length := by
  obtain ⟨sp, np, dp, pair, _⟩ := hq
  exact List.getElem?_eq_some_iff.mp pair |>.1

def readBody : Command p :=
  .load (.register 0) 1 2 15 {
    nil := .fail
    bit := .fail
    cons := .fail
    fork := .fail
    bucket := .fail
    pair := .load (.register 1) 3 14 4
      (RegisterAdder.nilBitCases .fail (.ret [.register 4, .register 3, .register 2]))
  }

def storeBody : Command p :=
  .allocate 3 (.bit (.register 0) (.register 1))
    (.allocate 4 (.pair (.register 3) (.register 2)) (.ret [.register 4]))

/-- Reading a represented rational uses exactly two record loads. -/
theorem read_compiled (code : Code p) {h : Heap} {rp : Ptr}
    {q : BinaryRational.Word width} (hq : At h rp q) :
    ∃ np dp, BitsAt h np q.magnitude ∧ BitsAt h dp q.denominator ∧
      Within code h (initialRegisters [.pointer rp]) readBody
        [.flag q.negative, .pointer np, .pointer dp] h 27 := by
  obtain ⟨sp, np, dp, pair, bit, num, den⟩ := hq
  let r₀ := initialRegisters [Value.pointer rp]
  let r₁ := loadRegisters r₀ 1 2 15 (.pair sp dp)
  let r₂ := loadRegisters r₁ 3 14 4 (.bit q.negative np)
  have last : Within code h r₂ (.ret [.register 4, .register 3, .register 2])
      [.flag q.negative, .pointer np, .pointer dp] h 7 := by
    simpa [values, Atom.eval, r₂, r₁, loadRegisters, decoded] using
      Within.ret code h r₂ [.register 4, .register 3, .register 2]
  have bitLoad := Within.load (address := .register 1) (first := 3) (second := 14) (bit := 4)
    (branches := RegisterAdder.nilBitCases .fail (.ret [.register 4, .register 3, .register 2]))
    (by simp [Atom.eval, r₁, loadRegisters, decoded]) bit last
  have pairLoad := Within.load (address := .register 0) (first := 1) (second := 2) (bit := 15)
    (branches := ⟨.fail, .fail, .fail, .fail, .fail,
      .load (.register 1) 3 14 4
        (RegisterAdder.nilBitCases .fail (.ret [.register 4, .register 3, .register 2]))⟩)
    (by simp [Atom.eval, r₀, initialRegisters]) pair bitLoad
  exact ⟨np, dp, num, den, pairLoad⟩

/-- Constructing a rational record shares both immutable binary words. -/
theorem store_compiled (code : Code p) {h : Heap} (hh : Valid h)
    (q : BinaryRational.Word width) {np dp : Ptr}
    (hn : BitsAt h np q.magnitude) (hd : BitsAt h dp q.denominator) :
    ∃ out : Heap, ∃ rp : Ptr, Extends h out ∧ Valid out ∧ At out rp q ∧
      Within code h (initialRegisters [.flag q.negative, .pointer np, .pointer dp])
        storeBody [.pointer rp] out 19 := by
  let mid := h ++ [.bit q.negative np]
  let out := mid ++ [.pair h.length dp]
  have bitSafe := safe_allocate h hh (.bit q.negative np) (by
    intro x hx
    simp only [Cell.references, List.mem_singleton] at hx
    exact hx ▸ hn.allocated)
  have midExt : Extends h mid := bitSafe.1
  have midValid : Valid mid := bitSafe.2.1
  have pairSafe := safe_allocate mid midValid (.pair h.length dp) (by
    intro x hx
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simp [mid]
    · exact (hd.mono midExt).allocated)
  have outExt : Extends mid out := pairSafe.1
  have outValid : Valid out := pairSafe.2.1
  have hbit : mid[h.length]? = some (.bit q.negative np) := by simp [mid]
  have hpair : out[mid.length]? = some (.pair h.length dp) := by simp [out]
  let r₀ := initialRegisters [Value.flag q.negative, .pointer np, .pointer dp]
  let r₁ := Function.update r₀ 3 (Value.pointer h.length)
  let r₂ := Function.update r₁ 4 (Value.pointer mid.length)
  have last : Within code out r₂ (.ret [.register 4]) [.pointer mid.length] out 3 := by
    simpa [values, Atom.eval, r₂] using Within.ret code out r₂ [.register 4]
  have allocPair := Within.allocate (h := mid) (regs := r₁) (dst := 4)
    (expr := .pair (.register 3) (.register 2))
    (by simp [CellExpr.eval, Atom.eval, r₁, r₀, initialRegisters, Value.asPointer]) last
  have allocBit := Within.allocate (h := h) (regs := r₀) (dst := 3)
    (expr := .bit (.register 0) (.register 1))
    (by simp [CellExpr.eval, Atom.eval, r₀, initialRegisters, Value.asPointer, Value.asFlag]) allocPair
  refine ⟨out, mid.length, midExt.trans outExt, outValid,
    ⟨h.length, np, dp, hpair, outExt.lookup hbit,
      hn.mono (midExt.trans outExt), hd.mono (midExt.trans outExt)⟩, ?_⟩
  simpa [storeBody, r₀, CellExpr.args] using allocBit

end WeightedMIS.StoredRational
