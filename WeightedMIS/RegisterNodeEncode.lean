module

public import WeightedMIS.RegisterNodeDecode
public import WeightedMIS.RegisterWordArithmetic
public import WeightedMIS.RegisterHorner

/-!
# Closed register encoding of expanded-node scalar fields

One fixed body multiplies and adds the stored positional digits. The same
body covers both hubs and working nodes; all arithmetic is binary word code.
-/

@[expose] public section

namespace WeightedMIS.RegisterNodeEncode

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open ScalarNodeCodec RegisterNodeDecode

variable {p width : ℕ}

def workBody (mul add : Fin p) : Command p :=
  .call mul [.register 5, .register 1] [9]
    (.call add [.register 9, .register 2, .flag false] [11, 15]
      (.call add [.register 11, .register 7, .flag false] [12, 15]
        (.call mul [.register 6, .register 12] [13]
          (.call add [.register 13, .register 10, .flag false] [14, 15]
            (.ret [.register 14])))))

def encodeBody (mul add : Fin p) : Command p :=
  .call mul [.register 8, .register 3] [9]
    (.call add [.register 9, .register 4, .flag false] [10, 15]
      (.branch (.register 0) (.ret [.register 10]) (workBody mul add)))

/-- Interpret the fixed encoder body on concrete represented fields. -/
theorem compiled (code : Code p) (ids : RegisterHorner.Procedures p)
    (hcode : ids.Matches code) {h : Heap} (hh : Valid h)
    (node : Words width) (ptrs : Pointers) (hn : At h ptrs node)
    {sp tp op dp : Ptr} {S T one two : Bits width}
    (hs : BitsAt h sp S) (ht : BitsAt h tp T) (ho : BitsAt h op one) (hd : BitsAt h dp two) :
    ∃ final : Heap, ∃ result : Ptr, Extends h final ∧ Valid final ∧
      BitsAt final result (encodeWords S T one two node) ∧
      Within code h (initialRegisters
        (ptrs.outputs ++ [.pointer sp, .pointer tp, .pointer op, .pointer dp]))
        (encodeBody ids.mul ids.add) [.pointer result] final (1200 * (width + 1) ^ 2) := by
  obtain ⟨_selfCode, mulCode, zeroCode, accCode, shiftCode, snocCode, addCode⟩ := hcode
  obtain ⟨hubEq, anchorAt, currentAt, boxAt, parityAt⟩ := hn
  have multiply {heap : Heap} (valid : Valid heap) {ap bp : Ptr} {a b : Bits width}
      (ha : BitsAt heap ap a) (hb : BitsAt heap bp b) :=
    RegisterMultiplier.multiply_compiled code ids.zero ids.mulAcc ids.shift
      ids.snoc ids.add zeroCode accCode shiftCode snocCode addCode valid ha hb
  obtain ⟨h₁, mp, ext₁, valid₁, productAt, multiply₁⟩ := multiply hh hd boxAt
  rw [← mulCode] at multiply₁
  obtain ⟨h₂, tailp, ext₂, valid₂, tailAt, add₁⟩ :=
    RegisterWordArithmetic.add_compiled code ids.add addCode valid₁ productAt (parityAt.mono ext₁)
  have ext₀ := ext₁.trans ext₂
  let tail := (Bits.add (Bits.multiply two node.box).1 node.parity).1
  let tailCarry := (Bits.add (Bits.multiply two node.box).1 node.parity).2.1
  let r₀ := initialRegisters (ptrs.outputs ++ [Value.pointer sp, .pointer tp, .pointer op, .pointer dp])
  let r₁ := bindResults r₀ [9] [Value.pointer mp]
  let r₂ := bindResults r₁ [10, 15] [Value.pointer tailp, .flag tailCarry]
  have h0 : r₂ 0 = .flag node.hub := by
    simp [r₂, r₁, r₀, bindResults, initialRegisters, Pointers.outputs, hubEq]
  obtain ⟨final, result, finalExt, finalValid, finalAt, branch⟩ :
      ∃ final : Heap, ∃ result : Ptr, Extends h₂ final ∧ Valid final ∧
        BitsAt final result (encodeWords S T one two node) ∧
        Within code h₂ r₂ (.branch (.register 0) (.ret [.register 10]) (workBody ids.mul ids.add))
          [.pointer result] final (800 * (width + 1) ^ 2) := by
    cases hhub : node.hub with
    | true =>
      have last : Within code h₂ r₂ (.ret [.register 10]) [.pointer tailp] h₂ 3 := by
        simpa [values, Atom.eval, r₂, bindResults] using Within.ret code h₂ r₂ [.register 10]
      have branch := Within.branch (test := .register 0) (yes := .ret [.register 10])
        (no := workBody ids.mul ids.add) (b := true) (by simpa [Atom.eval, hhub] using h0) last
      exact ⟨h₂, tailp, .refl h₂, valid₂, by simpa [encodeWords, hhub] using tailAt,
        branch.mono (by nlinarith only [Nat.zero_le width])⟩
    | false =>
      obtain ⟨h₃, sap, ext₃, valid₃, saAt, multiply₂⟩ :=
        multiply valid₂ (hs.mono ext₀) (anchorAt.mono ext₀)
      rw [← mulCode] at multiply₂
      have ext₀₃ := ext₀.trans ext₃
      obtain ⟨h₄, avp, ext₄, valid₄, avAt, add₂⟩ :=
        RegisterWordArithmetic.add_compiled code ids.add addCode valid₃ saAt
          (currentAt.mono ext₀₃)
      obtain ⟨h₅, indexp, ext₅, valid₅, indexAt, add₃⟩ :=
        RegisterWordArithmetic.add_compiled code ids.add addCode valid₄ avAt
          (ho.mono (ext₀₃.trans ext₄))
      obtain ⟨h₆, group, ext₆, valid₆, groupAt, multiply₃⟩ :=
        multiply valid₅ (ht.mono (ext₀₃.trans (ext₄.trans ext₅))) indexAt
      rw [← mulCode] at multiply₃
      obtain ⟨h₇, out, ext₇, valid₇, outAt, add₄⟩ :=
        RegisterWordArithmetic.add_compiled code ids.add addCode valid₆ groupAt
          (tailAt.mono (ext₃.trans (ext₄.trans (ext₅.trans ext₆))))
      let av := (Bits.add (Bits.multiply S node.anchor).1 node.current).1
      let index := (Bits.add av one).1
      let r₃ := bindResults r₂ [9] [Value.pointer sap]
      let r₄ := bindResults r₃ [11, 15]
        [Value.pointer avp, .flag (Bits.add (Bits.multiply S node.anchor).1 node.current).2.1]
      let r₅ := bindResults r₄ [12, 15] [Value.pointer indexp, .flag (Bits.add av one).2.1]
      let r₆ := bindResults r₅ [13] [Value.pointer group]
      let r₇ := bindResults r₆ [14, 15]
        [Value.pointer out, .flag (Bits.add (Bits.multiply T index).1 tail).2.1]
      have last : Within code h₇ r₇ (.ret [.register 14]) [.pointer out] h₇ 3 := by
        simpa [values, Atom.eval, r₇, bindResults] using Within.ret code h₇ r₇ [.register 14]
      have args₇ : values r₆ [.register 13, .register 10, .flag false] =
          [.pointer group, .pointer tailp, .flag false] := by
        simp [values, Atom.eval, r₆, r₅, r₄, r₃, r₂, bindResults]
      have call₇ := Within.call (procedure := ids.add)
        (arguments := [.register 13, .register 10, .flag false]) (results := [14, 15]) (regs := r₆)
        (by simpa only [args₇] using add₄) last
      have args₆ : values r₅ [.register 6, .register 12] = [.pointer tp, .pointer indexp] := by
        simp [values, Atom.eval, r₅, r₄, r₃, r₂, r₁, r₀, bindResults, initialRegisters, Pointers.outputs]
      have call₆ := Within.call (procedure := ids.mul)
        (arguments := [.register 6, .register 12]) (results := [13]) (regs := r₅)
        (by simpa only [args₆] using multiply₃) call₇
      have args₅ : values r₄ [.register 11, .register 7, .flag false] =
          [.pointer avp, .pointer op, .flag false] := by
        simp [values, Atom.eval, r₄, r₃, r₂, r₁, r₀, bindResults, initialRegisters, Pointers.outputs]
      have call₅ := Within.call (procedure := ids.add)
        (arguments := [.register 11, .register 7, .flag false]) (results := [12, 15]) (regs := r₄)
        (by simpa only [args₅] using add₃) call₆
      have args₄ : values r₃ [.register 9, .register 2, .flag false] =
          [.pointer sap, .pointer ptrs.current, .flag false] := by
        simp [values, Atom.eval, r₃, r₂, r₁, r₀, bindResults, initialRegisters, Pointers.outputs]
      have call₄ := Within.call (procedure := ids.add)
        (arguments := [.register 9, .register 2, .flag false]) (results := [11, 15]) (regs := r₃)
        (by simpa only [args₄] using add₂) call₅
      have args₃ : values r₂ [.register 5, .register 1] = [.pointer sp, .pointer ptrs.anchor] := by
        simp [values, Atom.eval, r₂, r₁, r₀, bindResults, initialRegisters, Pointers.outputs]
      have call₃ := Within.call (procedure := ids.mul)
        (arguments := [.register 5, .register 1]) (results := [9]) (regs := r₂)
        (by simpa only [args₃] using multiply₂) call₄
      have branch := Within.branch (test := .register 0) (yes := .ret [.register 10])
        (no := workBody ids.mul ids.add) (b := false) (by simpa [Atom.eval, hhub] using h0) call₃
      refine ⟨h₇, out, ext₃.trans (ext₄.trans (ext₅.trans (ext₆.trans ext₇))), valid₇,
        by simpa [encodeWords, hhub] using outAt, ?_⟩
      exact branch.mono (by simp only [List.length_cons, List.length_nil]; nlinarith only [Nat.zero_le width])
  have args₂ : values r₁ [.register 9, .register 4, .flag false] =
      [.pointer mp, .pointer ptrs.parity, .flag false] := by
    simp [values, Atom.eval, r₁, r₀, bindResults, initialRegisters, Pointers.outputs]
  have call₂ := Within.call (procedure := ids.add)
    (arguments := [.register 9, .register 4, .flag false]) (results := [10, 15]) (regs := r₁)
    (by simpa only [args₂] using add₁) branch
  have args₁ : values r₀ [.register 8, .register 3] = [.pointer dp, .pointer ptrs.box] := by
    simp [values, Atom.eval, r₀, initialRegisters, Pointers.outputs]
  have call₁ := Within.call (procedure := ids.mul)
    (arguments := [.register 8, .register 3]) (results := [9]) (regs := r₀)
    (by simpa only [args₁] using multiply₁) call₂
  exact ⟨final, result, ext₀.trans finalExt, finalValid, finalAt,
    call₁.mono (by simp only [List.length_cons, List.length_nil]; nlinarith only [Nat.zero_le width])⟩

end WeightedMIS.RegisterNodeEncode
