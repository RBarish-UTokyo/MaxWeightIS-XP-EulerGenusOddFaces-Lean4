module

public import WeightedMIS.ScalarNodeCodec
public import WeightedMIS.RegisterQuotRem

/-!
# Closed register decoding of expanded-node IDs

The fixed five-argument procedure uses three binary divisions, comparison,
and subtraction. It returns the hub bit and four equal-width scalar words.
-/

@[expose] public section

namespace WeightedMIS.RegisterNodeDecode

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open ScalarNodeCodec

variable {p width : ℕ}

structure Pointers where
  hub : Bool
  anchor : Ptr
  current : Ptr
  box : Ptr
  parity : Ptr

def Pointers.outputs (ptrs : Pointers) : List Value :=
  [.flag ptrs.hub, .pointer ptrs.anchor, .pointer ptrs.current,
    .pointer ptrs.box, .pointer ptrs.parity]

def At (h : Heap) (ptrs : Pointers) (node : Words width) : Prop :=
  ptrs.hub = node.hub ∧ BitsAt h ptrs.anchor node.anchor ∧
    BitsAt h ptrs.current node.current ∧ BitsAt h ptrs.box node.box ∧
      BitsAt h ptrs.parity node.parity

def workBody (quotRem sub : Fin p) : Command p :=
  .call sub [.register 5, .register 3] [13, 14]
    (.call quotRem [.register 13, .register 1] [5, 7]
      (.ret [.flag false, .register 5, .register 7, .register 8, .register 10]))

def hubBody : Command p :=
  .ret [.flag true, .register 5, .register 5, .register 8, .register 10]

def decodeBody (quotRem cmp sub : Fin p) : Command p :=
  .call quotRem [.register 0, .register 2] [5, 7]
    (.call quotRem [.register 7, .register 4] [8, 10]
      (.call cmp [.register 0, .register 2] [11, 12]
        (.branch (.register 11) hubBody (workBody quotRem sub))))

/-- Every call is to the specified finite divider, comparator, or subtractor;
no width or arithmetic oracle occurs in the program text. -/
theorem compiled (code : Code p) (quotRem : Fin p) (ids : RegisterDivision.Procedures p)
    (hqr : code quotRem = RegisterQuotRem.body ids.divide) (hcode : ids.Matches code)
    {h : Heap} (hh : Valid h) {ip sp tp op dp : Ptr} {id S T one two : Bits width}
    (hi : BitsAt h ip id) (hs : BitsAt h sp S) (ht : BitsAt h tp T)
    (ho : BitsAt h op one) (hd : BitsAt h dp two) :
    ∃ final : Heap, ∃ result : Pointers, Extends h final ∧ Valid final ∧
      At final result (decodeWords id S T one two) ∧
      Within code h (initialRegisters
        [.pointer ip, .pointer sp, .pointer tp, .pointer op, .pointer dp])
        (decodeBody quotRem ids.cmp ids.sub) result.outputs final (1600 * (width + 1) ^ 2) := by
  have cmpCode := hcode.2.1
  have subCode := hcode.2.2.2.2.2.1
  have complementCode := hcode.2.2.2.2.2.2.1
  have addCode := hcode.2.2.2.2.2.2.2.1
  obtain ⟨h₁, qp, rp, ext₁, valid₁, qAt, rAt, div₁⟩ :=
    RegisterQuotRem.compiled code ids hcode hh hi ht
  rw [← hqr] at div₁
  obtain ⟨h₂, bp, pp, ext₂, valid₂, bAt, pAt, div₂⟩ :=
    RegisterQuotRem.compiled code ids hcode valid₁ rAt (hd.mono ext₁)
  rw [← hqr] at div₂
  have ext₀ := ext₁.trans ext₂
  have cmp := RegisterComparator.compiled code ids.cmp cmpCode (hi.mono ext₀) (ht.mono ext₀)
  let comparison := (Bits.compare id T).1
  let r₀ := initialRegisters
    [Value.pointer ip, .pointer sp, .pointer tp, .pointer op, .pointer dp]
  let r₁ := bindResults r₀ [5, 7] [Value.pointer qp, .pointer rp]
  let r₂ := bindResults r₁ [8, 10] [Value.pointer bp, .pointer pp]
  let r₃ := bindResults r₂ [11, 12] (RegisterComparator.flags comparison)
  have h11 : r₃ 11 = .flag (decide (comparison = .lt)) := by
    simp [r₃, bindResults, RegisterComparator.flags]
  obtain ⟨final, result, finalExt, finalValid, finalAt, branch⟩ :
      ∃ final : Heap, ∃ result : Pointers, Extends h₂ final ∧ Valid final ∧
        At final result (decodeWords id S T one two) ∧
        Within code h₂ r₃ (.branch (.register 11) hubBody (workBody quotRem ids.sub))
          result.outputs final (600 * (width + 1) ^ 2) := by
    by_cases hub : (Bits.compare id T).1 = .lt
    · let result : Pointers := ⟨true, qp, qp, bp, pp⟩
      have last : Within code h₂ r₃ hubBody result.outputs h₂ 11 := by
        simpa [hubBody, Pointers.outputs, result, values, Atom.eval, r₃, r₂, r₁,
          bindResults, RegisterComparator.flags] using
          Within.ret code h₂ r₃ [.flag true, .register 5, .register 5, .register 8, .register 10]
      have branch := Within.branch (test := .register 11) (yes := hubBody)
        (no := workBody quotRem ids.sub) (b := true)
        (by simpa [Atom.eval, comparison, hub] using h11) last
      refine ⟨h₂, result, .refl h₂, valid₂, ?_, branch.mono (by nlinarith only [Nat.zero_le width])⟩
      exact ⟨by simp [result, decodeWords, hub],
        by simpa [result, decodeWords, hub] using qAt.mono ext₂,
        by simpa [result, decodeWords, hub] using qAt.mono ext₂,
        by simpa [result, decodeWords, hub] using bAt,
        by simpa [result, decodeWords, hub] using pAt⟩
    · obtain ⟨h₃, kp, ext₃, valid₃, kAt, subtraction⟩ :=
        RegisterSubtractor.compiled code ids.complement ids.add complementCode addCode valid₂
          (qAt.mono ext₂) (ho.mono ext₀)
      rw [← subCode] at subtraction
      obtain ⟨h₄, ap, vp, ext₄, valid₄, aAt, vAt, div₃⟩ :=
        RegisterQuotRem.compiled code ids hcode valid₃ kAt (hs.mono (ext₀.trans ext₃))
      rw [← hqr] at div₃
      let carry := (Bits.subtract (Bits.divide id T).1 one).2.1
      let r₄ := bindResults r₃ [13, 14] [Value.pointer kp, .flag carry]
      let r₅ := bindResults r₄ [5, 7] [Value.pointer ap, .pointer vp]
      let result : Pointers := ⟨false, ap, vp, bp, pp⟩
      have last : Within code h₄ r₅
          (.ret [.flag false, .register 5, .register 7, .register 8, .register 10])
          result.outputs h₄ 11 := by
        simpa [Pointers.outputs, result, values, Atom.eval, r₅, r₄, r₃, r₂,
          bindResults, RegisterComparator.flags] using
          Within.ret code h₄ r₅ [.flag false, .register 5, .register 7, .register 8, .register 10]
      have args₃ : values r₄ [.register 13, .register 1] = [.pointer kp, .pointer sp] := by
        simp [values, Atom.eval, r₄, r₃, r₂, r₁, r₀, bindResults, initialRegisters,
          RegisterComparator.flags]
      have divCall := Within.call (procedure := quotRem)
        (arguments := [.register 13, .register 1]) (results := [5, 7]) (regs := r₄)
        (by simpa only [args₃] using div₃) last
      have subArgs : values r₃ [.register 5, .register 3] = [.pointer qp, .pointer op] := by
        simp [values, Atom.eval, r₃, r₂, r₁, r₀, bindResults, initialRegisters,
          RegisterComparator.flags]
      have subCall := Within.call (procedure := ids.sub)
        (arguments := [.register 5, .register 3]) (results := [13, 14]) (regs := r₃)
        (by simpa only [subArgs] using subtraction) divCall
      have branch := Within.branch (test := .register 11) (yes := hubBody)
        (no := workBody quotRem ids.sub) (b := false)
        (by simpa [Atom.eval, comparison, hub] using h11) subCall
      refine ⟨h₄, result, ext₃.trans ext₄, valid₄, ?_,
        branch.mono (by simp only [List.length_cons, List.length_nil]; nlinarith only [Nat.zero_le width])⟩
      exact ⟨by simp [result, decodeWords, hub],
        by simpa [result, decodeWords, hub] using aAt,
        by simpa [result, decodeWords, hub] using vAt,
        by simpa [result, decodeWords, hub] using bAt.mono (ext₃.trans ext₄),
        by simpa [result, decodeWords, hub] using pAt.mono (ext₃.trans ext₄)⟩
  have cmpArgs : values r₂ [.register 0, .register 2] = [.pointer ip, .pointer tp] := by
    simp [values, Atom.eval, r₂, r₁, r₀, bindResults, initialRegisters]
  have cmpCall := Within.call (procedure := ids.cmp)
    (arguments := [.register 0, .register 2]) (results := [11, 12]) (regs := r₂)
    (by simpa only [cmpArgs] using cmp) branch
  have args₂ : values r₁ [.register 7, .register 4] = [.pointer rp, .pointer dp] := by
    simp [values, Atom.eval, r₁, r₀, bindResults, initialRegisters]
  have call₂ := Within.call (procedure := quotRem)
    (arguments := [.register 7, .register 4]) (results := [8, 10]) (regs := r₁)
    (by simpa only [args₂] using div₂) cmpCall
  have args₁ : values r₀ [.register 0, .register 2] = [.pointer ip, .pointer tp] := by
    simp [values, Atom.eval, r₀, initialRegisters]
  have call₁ := Within.call (procedure := quotRem)
    (arguments := [.register 0, .register 2]) (results := [5, 7]) (regs := r₀)
    (by simpa only [args₁] using div₁) call₂
  exact ⟨final, result, ext₀.trans finalExt, finalValid, finalAt,
    call₁.mono (by simp only [List.length_cons, List.length_nil]; nlinarith only [Nat.zero_le width])⟩

end WeightedMIS.RegisterNodeDecode
