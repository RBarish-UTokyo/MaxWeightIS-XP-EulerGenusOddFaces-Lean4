module

public import WeightedMIS.ExpandedWords
public import WeightedMIS.RegisterComparator
public import WeightedMIS.RegisterAdder
public import WeightedMIS.PointerArithmeticEval

/-!
# Binary interval enumeration by fixed register code

The input consists of current, exclusive-limit, and one words. The procedure
branches on the compiled comparison, increments with the compiled binary
adder, and builds one shared list cell per result. Its code has no numerical
fuel or host-language enumeration primitive.
-/

@[expose] public section

set_option maxRecDepth 2048

namespace WeightedMIS.RegisterWordRange

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.ExpandedWords

variable {p : ℕ}

def afterIncrement (self : Fin p) : Command p :=
  .call self [.register 5, .register 1, .register 2] [7]
    (.allocate 8 (.cons (.register 0) (.register 7)) (.ret [.register 8]))

def stepBody (self add : Fin p) : Command p :=
  .call add [.register 0, .register 2, .flag false] [5, 6] (afterIncrement self)

def rangeBody (self add cmp : Fin p) : Command p :=
  .call cmp [.register 0, .register 1] [3, 4]
    (.branch (.register 3) (stepBody self add) (.ret [.null]))

def budget (width length : ℕ) : ℕ := 200 * (width + 1) * (length + 1)

/-- The induction parameter proves termination; it is absent from the
compiled program and its input ABI. -/
theorem compiled_aux (code : Code p) (self add cmp : Fin p)
    (hself : code self = rangeBody self add cmp)
    (hadd : code add = RegisterAdder.adderBody add)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (fuel : ℕ) {n : ℕ} {h : Heap} (hh : Valid h) {cp lp op : Ptr}
    {current limit one : Bits n} (hc : BitsAt h cp current)
    (hl : BitsAt h lp limit) (ho : BitsAt h op one) (hone : one.value = 1)
    (hfuel : limit.value - current.value < fuel) :
    ∃ (out : Heap) (result : Ptr) (words : List (Bits n)), Extends h out ∧ Valid out ∧ WordsAt out result words ∧
      words.map Bits.value = List.range' current.value (limit.value - current.value) ∧
      Within code h (initialRegisters [.pointer cp, .pointer lp, .pointer op]) (code self)
        [.pointer result] out (budget n (limit.value - current.value)) := by
  induction fuel generalizing h cp lp op current limit one with
  | zero => omega
  | succ fuel ih =>
    have hcompare := RegisterComparator.compiled code cmp hcmp hc hl
    let regs := initialRegisters [Value.pointer cp, .pointer lp, .pointer op]
    let compared := bindResults regs [3, 4] (RegisterComparator.flags (Bits.compare current limit).1)
    by_cases hlt : current.value < limit.value
    · have hltflag : decide ((Bits.compare current limit).1 = .lt) = true := by
        simp only [decide_eq_true_eq]
        exact (Bits.compare_correct current limit).1.mpr hlt
      have hfits : current.value + one.value < 2 ^ n := by
        have hv := Bits.value_lt limit
        omega
      let next := (Bits.add current one).1
      have hnext : next.value = current.value + 1 := by
        simpa [next, hone] using (Bits.add_value_of_lt current one hfits).2
      let added := addCarryPointer n cp op false h
      obtain ⟨hsafe, hnextRep, _, htrace⟩ := addCarryPointer_refines hh hc ho false
      have hn : BitsAt added.heap added.value.1 next := hnextRep
      obtain ⟨out, result, words, hext, hv, hwords, hvalues, hrest⟩ :=
        ih hsafe.2.1 hn (hl.mono hsafe.1) (ho.mono hsafe.1) hone (by rw [hnext]; omega)
      have hgap : limit.value - current.value = (limit.value - next.value) + 1 := by
        rw [hnext]; omega
      have hallExt := hsafe.1.trans hext
      have hcons := allocate_word_cons hv (hc.mono hallExt) hwords
      let incremented := bindResults compared [5, 6] [.pointer added.value.1, .flag added.value.2]
      let recursed := bindResults incremented [7] [Value.pointer result]
      have last : Within code (out ++ [.cons cp result])
          (Function.update recursed 8 (.pointer out.length)) (.ret [.register 8])
          [.pointer out.length] (out ++ [.cons cp result]) 3 := by
        simpa [values, Atom.eval] using Within.ret code (out ++ [.cons cp result])
          (Function.update recursed 8 (.pointer out.length)) [.register 8]
      have alloc := Within.allocate (dst := 8) (expr := .cons (.register 0) (.register 7))
        (by simp [recursed, incremented, compared, regs, bindResults, initialRegisters,
          CellExpr.eval, Atom.eval, Value.asPointer, RegisterComparator.flags]) last
      have hrargs : values incremented [.register 5, .register 1, .register 2] =
          [.pointer added.value.1, .pointer lp, .pointer op] := by
        simp [incremented, compared, regs, bindResults, initialRegisters, values, Atom.eval, RegisterComparator.flags]
      have recurse := Within.call (procedure := self) (regs := incremented)
        (arguments := [.register 5, .register 1, .register 2]) (results := [7])
        (by simpa only [hrargs] using hrest) alloc
      have haexec := RegisterAdder.compiled code add hadd (addCarryPointer_eval hh hc ho false)
      have haargs : values compared [.register 0, .register 2, .flag false] =
          [.pointer cp, .pointer op, .flag false] := by
        simp [compared, regs, bindResults, initialRegisters, values, Atom.eval, RegisterComparator.flags]
      have addcall := Within.call (procedure := add) (regs := compared)
        (arguments := [.register 0, .register 2, .flag false]) (results := [5, 6])
        (by simpa only [haargs] using haexec) recurse
      have branch := Within.branch (test := .register 3) (b := true)
        (yes := stepBody self add) (no := .ret [.null])
        (by simp [compared, bindResults, Atom.eval, RegisterComparator.flags, hltflag]) addcall
      have hcargs : values regs [.register 0, .register 1] = [.pointer cp, .pointer lp] := by
        simp [regs, initialRegisters, values, Atom.eval]
      have call := Within.call (procedure := cmp) (regs := regs)
        (arguments := [.register 0, .register 1]) (results := [3, 4])
        (by simpa only [hcargs] using hcompare) branch
      refine ⟨out ++ [.cons cp result], out.length, current :: words,
        hallExt.trans hcons.1.1, hcons.1.2.1, hcons.2, ?_, ?_⟩
      · simp only [List.map_cons, hvalues, hgap]
        rw [List.range'_succ]
        rw [hnext]
      · rw [hself]
        apply call.mono
        rw [htrace, hgap]
        simp only [budget, List.length_cons, List.length_nil, CellExpr.args]
        nlinarith
    · have hge : limit.value ≤ current.value := by omega
      have hltflag : decide ((Bits.compare current limit).1 = .lt) = false := by
        simp only [decide_eq_false_iff_not]
        exact mt (Bits.compare_correct current limit).1.mp hlt
      have last : Within code h compared (.ret [.null]) [.pointer 0] h 3 := by
        simpa [values, Atom.eval] using Within.ret code h compared [.null]
      have branch := Within.branch (test := .register 3) (b := false)
        (yes := stepBody self add) (no := .ret [.null])
        (by simp [compared, bindResults, Atom.eval, RegisterComparator.flags, hltflag]) last
      have hcargs : values regs [.register 0, .register 1] = [.pointer cp, .pointer lp] := by
        simp [regs, initialRegisters, values, Atom.eval]
      have call := Within.call (procedure := cmp) (regs := regs)
        (arguments := [.register 0, .register 1]) (results := [3, 4])
        (by simpa only [hcargs] using hcompare) branch
      refine ⟨h, 0, [], Extends.refl h, hh, WordsAt.nil hh.1, ?_, ?_⟩
      · simp [Nat.sub_eq_zero_of_le hge]
      · rw [hself]
        exact call.mono (by simp [budget, Nat.sub_eq_zero_of_le hge]; omega)

/-- Exactly the requested interval is enumerated, in increasing order, by a
fixed tag-directed program. Its work is linear in output length and word size. -/
theorem compiled (code : Code p) (self add cmp : Fin p)
    (hself : code self = rangeBody self add cmp)
    (hadd : code add = RegisterAdder.adderBody add)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {n : ℕ} {h : Heap} (hh : Valid h) {cp lp op : Ptr}
    {current limit one : Bits n} (hc : BitsAt h cp current)
    (hl : BitsAt h lp limit) (ho : BitsAt h op one) (hone : one.value = 1) :
    ∃ (out : Heap) (result : Ptr) (words : List (Bits n)), Extends h out ∧ Valid out ∧ WordsAt out result words ∧
      words.map Bits.value = List.range' current.value (limit.value - current.value) ∧
      Within code h (initialRegisters [.pointer cp, .pointer lp, .pointer op]) (code self)
        [.pointer result] out (budget n (limit.value - current.value)) :=
  compiled_aux code self add cmp hself hadd hcmp (limit.value - current.value + 1)
    hh hc hl ho hone (by omega)

end WeightedMIS.RegisterWordRange
