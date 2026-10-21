module

public import WeightedMIS.CompiledTrie
public import WeightedMIS.ExpandedCoordinate
public import WeightedMIS.RegisterComparator
public import WeightedMIS.RegisterSubtractor

/-! # Closed register code for a signed coordinate update -/

@[expose] public section

namespace WeightedMIS.RegisterCoordinate

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords

variable {p : ℕ}

def rejected : Command p := .ret [.flag false, .null]
def accepted : Command p := .ret [.flag true, .register 7]

def negativeBody (cmp sub : Fin p) : Command p :=
  .call cmp [.register 1, .register 3] [5, 6]
    (.branch (.register 5) rejected
      (.call sub [.register 1, .register 3] [7, 8] accepted))

def positiveBody (add cmp : Fin p) : Command p :=
  .call add [.register 1, .register 3, .flag false] [7, 8]
    (.branch (.register 8) rejected
      (.call cmp [.register 7, .register 0] [5, 6]
        (.branch (.register 5) accepted rejected)))

/-- Arguments: base, unsigned digit, signed magnitude record.
Results: in-range flag and result word (zero pointer on failure). -/
def digitBody (add cmp sub : Fin p) : Command p :=
  .load (.register 2) 3 15 4 { CompiledTrie.failCases with
    bit := .branch (.register 4) (negativeBody cmp sub) (positiveBody add cmp) }

theorem rejected_compiled (code : Code p) (h : Heap) (regs : Registers) :
    Within code h regs rejected [.flag false, .pointer 0] h 5 := by
  simpa [rejected, values, Atom.eval] using Within.ret code h regs [.flag false, .null]

theorem accepted_compiled (code : Code p) (h : Heap) (regs : Registers) {q : Ptr}
    (hq : regs 7 = .pointer q) :
    Within code h regs accepted [.flag true, .pointer q] h 5 := by
  simpa [accepted, values, Atom.eval, hq] using Within.ret code h regs [.flag true, .register 7]

theorem negative_compiled (code : Code p) (cmp sub complement add : Fin p)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (hsub : code sub = RegisterSubtractor.subtractorBody complement add)
    (hcomp : code complement = RegisterComplement.complementBody complement)
    (hadd : code add = RegisterAdder.adderBody add)
    {n : ℕ} {h : Heap} (hh : Valid h) {digit mag : Bits n} {xp mp : Ptr}
    (hx : BitsAt h xp digit) (hm : BitsAt h mp mag) (regs : Registers)
    (h1 : regs 1 = .pointer xp) (h3 : regs 3 = .pointer mp) :
    ∃ out q, Extends h out ∧ Valid out ∧
      OptionWordAt out q (if (Bits.compare digit mag).1 = .lt then none else some (Bits.subtract digit mag).1) ∧
      Within code h regs (negativeBody cmp sub)
        [.flag (!(decide ((Bits.compare digit mag).1 = .lt))), .pointer q] out (300 * (n + 1)) := by
  have hc := RegisterComparator.compiled code cmp hcmp hx hm
  let rs := bindResults regs [5, 6] (RegisterComparator.flags (Bits.compare digit mag).1)
  have h5 : rs 5 = .flag (decide ((Bits.compare digit mag).1 = .lt)) := by
    simp [rs, bindResults, RegisterComparator.flags]
  have hargs : values regs [.register 1, .register 3] = [.pointer xp, .pointer mp] := by
    simp [values, Atom.eval, h1, h3]
  by_cases hl : (Bits.compare digit mag).1 = .lt
  · refine ⟨h, 0, .refl h, hh, ?_, ?_⟩
    · simp [hl, OptionWordAt]
    · have hr := rejected_compiled code h rs
      have hb := Within.branch (test := .register 5) (b := true)
        (yes := rejected) (no := .call sub [.register 1, .register 3] [7, 8] accepted)
        (by simpa [Atom.eval, hl] using h5) hr
      have call := Within.call (procedure := cmp) (arguments := [.register 1, .register 3])
        (results := [5, 6]) (regs := regs) (returned := RegisterComparator.flags (Bits.compare digit mag).1)
        (by simpa only [hargs] using hc) hb
      simpa only [negativeBody, hl, decide_true, Bool.not_true] using
        call.mono (b := 300 * (n + 1)) (by simp; omega)
  · obtain ⟨out, q, he, ho, hq, hs⟩ := RegisterSubtractor.compiled code complement add hcomp hadd hh hx hm
    refine ⟨out, q, he, ho, ?_, ?_⟩
    · simpa [hl, OptionWordAt] using hq
    · have hsubargs : values rs [.register 1, .register 3] = [.pointer xp, .pointer mp] := by
        simp [rs, values, Atom.eval, bindResults, RegisterComparator.flags, h1, h3]
      have hr := accepted_compiled code out
        (bindResults rs [7, 8] [.pointer q, .flag (Bits.subtract digit mag).2.1])
        (q := q) (by simp [bindResults])
      have hs' : Within code h (initialRegisters (values rs [.register 1, .register 3]))
          (code sub) [.pointer q, .flag (Bits.subtract digit mag).2.1] out (137 * n + 58) := by
        simpa only [hsubargs, hsub] using hs
      have sc := Within.call (procedure := sub) (arguments := [.register 1, .register 3])
        (results := [7, 8]) (regs := rs) hs' hr
      have hb := Within.branch (test := .register 5) (b := false)
        (yes := rejected) (no := .call sub [.register 1, .register 3] [7, 8] accepted)
        (by simpa [Atom.eval, hl] using h5) sc
      have call := Within.call (procedure := cmp) (arguments := [.register 1, .register 3])
        (results := [5, 6]) (regs := regs) (returned := RegisterComparator.flags (Bits.compare digit mag).1)
        (by simpa only [hargs] using hc) hb
      simpa only [negativeBody, hl, decide_false, Bool.not_false] using
        call.mono (b := 300 * (n + 1)) (by simp; omega)

theorem positive_compiled (code : Code p) (add cmp : Fin p)
    (hadd : code add = RegisterAdder.adderBody add)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {n : ℕ} {h : Heap} (hh : Valid h) {base digit mag : Bits n} {bp xp mp : Ptr}
    (hb : BitsAt h bp base) (hx : BitsAt h xp digit) (hm : BitsAt h mp mag)
    (regs : Registers) (h0 : regs 0 = .pointer bp) (h1 : regs 1 = .pointer xp) (h3 : regs 3 = .pointer mp) :
    ∃ out q, Extends h out ∧ Valid out ∧ OptionWordAt out q (updateDigit base digit ⟨false, mag⟩) ∧
      Within code h regs (positiveBody add cmp)
        [.flag (updateDigit base digit ⟨false, mag⟩).isSome, .pointer q] out (300 * (n + 1)) := by
  let addition := addCarryPointer n xp mp false h
  have hs := addCarryPointer_refines hh hx hm false
  have he := addCarryPointer_eval hh hx hm false
  have hc := RegisterAdder.compiled code add hadd he
  have hv : addition.value.2 = (Bits.add digit mag).2.1 := hs.2.2.1
  have hrep : BitsAt addition.heap addition.value.1 (Bits.add digit mag).1 := hs.2.1
  have hlen : addition.trace.length = 11 * n + 3 := hs.2.2.2
  have hc' : Within code h (initialRegisters [.pointer xp, .pointer mp, .flag false]) (code add)
      [.pointer addition.value.1, .flag addition.value.2] addition.heap (110 * n + 30) := by
    apply hc.mono
    change 10 * addition.trace.length ≤ _
    rw [hlen]
    omega
  let rs := bindResults regs [7, 8] [.pointer addition.value.1, .flag addition.value.2]
  have h7 : rs 7 = .pointer addition.value.1 := by simp [rs, bindResults]
  have h8 : rs 8 = .flag addition.value.2 := by simp [rs, bindResults]
  have hargs : values regs [.register 1, .register 3, .flag false] =
      [.pointer xp, .pointer mp, .flag false] := by simp [values, Atom.eval, h1, h3]
  cases hcarry : addition.value.2 with
  | true =>
    refine ⟨addition.heap, 0, hs.1.1, hs.1.2.1, ?_, ?_⟩
    · simp [updateDigit, ← hv, hcarry, OptionWordAt]
    · have hr := rejected_compiled code addition.heap rs
      have hbranch := Within.branch (test := .register 8) (b := true)
        (yes := rejected) (no := .call cmp [.register 7, .register 0] [5, 6]
          (.branch (.register 5) accepted rejected))
        (by simpa [Atom.eval, hcarry] using h8) hr
      have call := Within.call (procedure := add) (arguments := [.register 1, .register 3, .flag false])
        (results := [7, 8]) (regs := regs) (returned := [.pointer addition.value.1, .flag addition.value.2])
        (by simpa only [hargs] using hc') hbranch
      simpa only [positiveBody, updateDigit, Bool.false_eq_true, if_false, ← hv, hcarry,
        if_true, Option.isSome_none] using call.mono (b := 300 * (n + 1)) (by simp; omega)
  | false =>
    have hbc := hb.mono hs.1.1
    have hcompare := RegisterComparator.compiled code cmp hcmp hrep hbc
    let rt := bindResults rs [5, 6] (RegisterComparator.flags (Bits.compare (Bits.add digit mag).1 base).1)
    have h5 : rt 5 = .flag (decide ((Bits.compare (Bits.add digit mag).1 base).1 = .lt)) := by
      simp [rt, bindResults, RegisterComparator.flags]
    have hcmpArgs : values rs [.register 7, .register 0] = [.pointer addition.value.1, .pointer bp] := by
      simp [values, Atom.eval, rs, bindResults, h0]
    by_cases hless : (Bits.compare (Bits.add digit mag).1 base).1 = .lt
    · refine ⟨addition.heap, addition.value.1, hs.1.1, hs.1.2.1, ?_, ?_⟩
      · simpa [updateDigit, ← hv, hcarry, hless, OptionWordAt] using hrep
      · have hr := accepted_compiled code addition.heap rt (q := addition.value.1)
          (by simp [rt, bindResults, RegisterComparator.flags, h7])
        have hbr := Within.branch (test := .register 5) (b := true) (yes := accepted) (no := rejected)
          (by simpa [Atom.eval, hless] using h5) hr
        have hcc := Within.call (procedure := cmp) (arguments := [.register 7, .register 0])
          (results := [5, 6]) (regs := rs)
          (by simpa only [hcmpArgs] using hcompare) hbr
        have hbranch := Within.branch (test := .register 8) (b := false)
          (yes := rejected) (no := .call cmp [.register 7, .register 0] [5, 6]
            (.branch (.register 5) accepted rejected))
          (by simpa [Atom.eval, hcarry] using h8) hcc
        have call := Within.call (procedure := add) (arguments := [.register 1, .register 3, .flag false])
          (results := [7, 8]) (regs := regs) (returned := [.pointer addition.value.1, .flag addition.value.2])
          (by simpa only [hargs] using hc') hbranch
        simpa [positiveBody, updateDigit, ← hv, hcarry, hless] using
          call.mono (b := 300 * (n + 1)) (by simp; omega)
    · refine ⟨addition.heap, 0, hs.1.1, hs.1.2.1, ?_, ?_⟩
      · simp [updateDigit, ← hv, hcarry, hless, OptionWordAt]
      · have hr := rejected_compiled code addition.heap rt
        have hbr := Within.branch (test := .register 5) (b := false) (yes := accepted) (no := rejected)
          (by simpa [Atom.eval, hless] using h5) hr
        have hcc := Within.call (procedure := cmp) (arguments := [.register 7, .register 0])
          (results := [5, 6]) (regs := rs)
          (by simpa only [hcmpArgs] using hcompare) hbr
        have hbranch := Within.branch (test := .register 8) (b := false)
          (yes := rejected) (no := .call cmp [.register 7, .register 0] [5, 6]
            (.branch (.register 5) accepted rejected))
          (by simpa [Atom.eval, hcarry] using h8) hcc
        have call := Within.call (procedure := add) (arguments := [.register 1, .register 3, .flag false])
          (results := [7, 8]) (regs := regs) (returned := [.pointer addition.value.1, .flag addition.value.2])
          (by simpa only [hargs] using hc') hbranch
        simpa [positiveBody, updateDigit, ← hv, hcarry, hless] using
          call.mono (b := 300 * (n + 1)) (by simp; omega)

theorem compiled (code : Code p) (add cmp sub complement : Fin p)
    (hadd : code add = RegisterAdder.adderBody add)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (hsub : code sub = RegisterSubtractor.subtractorBody complement add)
    (hcomp : code complement = RegisterComplement.complementBody complement)
    {n : ℕ} {h : Heap} (hh : Valid h) {base digit : Bits n} {delta : SignedWord n} {bp xp dp : Ptr}
    (hb : BitsAt h bp base) (hx : BitsAt h xp digit) (hd : SignedAt h dp delta) :
    ∃ out q, Extends h out ∧ Valid out ∧ OptionWordAt out q (updateDigit base digit delta) ∧
      Within code h (initialRegisters [.pointer bp, .pointer xp, .pointer dp]) (digitBody add cmp sub)
        [.flag (updateDigit base digit delta).isSome, .pointer q] out (400 * (n + 1)) := by
  obtain ⟨mp, hrecord, hm⟩ := hd
  let regs := initialRegisters [Value.pointer bp, .pointer xp, .pointer dp]
  let rs := loadRegisters regs 3 15 4 (.bit delta.negative mp)
  have h0 : rs 0 = .pointer bp := by simp [rs, regs, loadRegisters, decoded, initialRegisters]
  have h1 : rs 1 = .pointer xp := by simp [rs, regs, loadRegisters, decoded, initialRegisters]
  have h3 : rs 3 = .pointer mp := by simp [rs, loadRegisters, decoded]
  have h4 : rs 4 = .flag delta.negative := by simp [rs, loadRegisters, decoded]
  rcases delta with ⟨negative, magnitude⟩
  cases negative with
  | true =>
    obtain ⟨out, q, he, ho, hq, hc⟩ := negative_compiled code cmp sub complement add hcmp hsub hcomp hadd
      hh hx hm rs h1 h3
    refine ⟨out, q, he, ho, ?_, ?_⟩
    · simpa [updateDigit] using hq
    · have hb := Within.branch (test := .register 4) (b := true)
        (yes := negativeBody cmp sub) (no := positiveBody add cmp)
        (show (.register 4 : Atom).eval rs = .flag true from h4) hc
      have hl := Within.load (address := .register 2) (first := 3) (second := 15) (bit := 4)
        (branches := {CompiledTrie.failCases with bit := (.branch (.register 4)
          (negativeBody cmp sub) (positiveBody add cmp))})
        (by simp [Atom.eval, regs, initialRegisters]) hrecord hb
      by_cases hless : (Bits.compare digit magnitude).1 = .lt <;>
        simpa [digitBody, updateDigit, hless] using hl.mono (b := 400 * (n + 1)) (by omega)
  | false =>
    obtain ⟨out, q, he, ho, hq, hc⟩ := positive_compiled code add cmp hadd hcmp hh hb hx hm rs h0 h1 h3
    refine ⟨out, q, he, ho, hq, ?_⟩
    have hb := Within.branch (test := .register 4) (b := false)
      (yes := negativeBody cmp sub) (no := positiveBody add cmp)
      (show (.register 4 : Atom).eval rs = .flag false from h4) hc
    have hl := Within.load (address := .register 2) (first := 3) (second := 15) (bit := 4)
      (branches := {CompiledTrie.failCases with bit := (.branch (.register 4)
        (negativeBody cmp sub) (positiveBody add cmp))})
      (by simp [Atom.eval, regs, initialRegisters]) hrecord hb
    exact hl.mono (by omega)

end WeightedMIS.RegisterCoordinate
