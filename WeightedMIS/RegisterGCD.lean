module

public import WeightedMIS.RegisterRemainder

/-!
# Closed register implementation of Euclid's algorithm

The finite body performs at most two remainder computations before recursively
calling itself. Termination follows from the proved binary halving argument;
there is no fuel parameter or unbounded arithmetic opcode in the program.
-/

@[expose] public section

namespace WeightedMIS.RegisterGCD

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

variable {p : ℕ}

def afterSecond (self : Fin p) : Command p :=
  .call self [.register 5, .register 8] [9] (.ret [.register 9])

def secondBranch (self rem : Fin p) : Command p :=
  .branch (.register 7) (.ret [.register 1])
    (.call rem [.register 1, .register 5] [8] (afterSecond self))

def firstRemainder (self rem cmp : Fin p) : Command p :=
  .call rem [.register 0, .register 1] [5]
    (.call cmp [.register 5, .register 2] [6, 7] (secondBranch self rem))

def gcdBody (self rem zero cmp : Fin p) : Command p :=
  .call zero [.register 1] [2]
    (.call cmp [.register 1, .register 2] [3, 4]
      (.branch (.register 4) (.ret [.register 0]) (firstRemainder self rem cmp)))

theorem euclid_zero {n : ℕ} (k : ℕ) (a b : Bits n) (hb : b.value = 0) :
    (Bits.euclid k a b).1 = a := by
  have hc : (Bits.compare b (Bits.zero n)).1 = .eq := by
    exact (Bits.compare_correct b (Bits.zero n)).2.1.mpr (by simpa using hb)
  cases k <;> simp [Bits.euclid, hc]

/-- The zero-divisor branch terminates after constructing and comparing its
actual zero word. -/
theorem stop_compiled (code : Code p) (d : RegisterDivision.Procedures p)
    (hm : d.Matches code) (self rem : Fin p)
    (hself : code self = gcdBody self rem d.zero d.cmp)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap bp : Ptr} {a b : Bits n}
    (ha : BitsAt h ap a) (hb : BitsAt h bp b) (hb0 : b.value = 0) :
    ∃ out : Heap, Extends h out ∧ Valid out ∧ BitsAt out ap a ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp]) (code self)
        [.pointer ap] out (100 * (n + 1)) := by
  obtain ⟨out, zp, hext, hvalid, hzrep, hlen, hze⟩ :=
    RegisterZero.compiled code d.zero hm.1 hh hb
  have hcmp := RegisterComparator.compiled code d.cmp hm.2.1 (hb.mono hext) hzrep
  have hceq : (Bits.compare b (Bits.zero n)).1 = .eq :=
    (Bits.compare_correct b (Bits.zero n)).2.1.mpr (by simpa using hb0)
  rw [hceq] at hcmp
  let regs := initialRegisters [Value.pointer ap, .pointer bp]
  let zeroed := bindResults regs [2] [Value.pointer zp]
  let compared := bindResults zeroed [3, 4] (RegisterComparator.flags .eq)
  have last : Within code out compared (.ret [.register 0]) [.pointer ap] out 3 := by
    simpa [compared, zeroed, regs, bindResults, RegisterComparator.flags, initialRegisters,
      values, Atom.eval] using Within.ret code out compared [.register 0]
  have hbranch := Within.branch (b := true) (test := .register 4)
    (yes := .ret [.register 0]) (no := firstRemainder self rem d.cmp)
    (by simp [Atom.eval, compared, bindResults, RegisterComparator.flags]) last
  have hargsC : values zeroed [.register 1, .register 2] = [.pointer bp, .pointer zp] := by
    simp [zeroed, regs, bindResults, values, Atom.eval, initialRegisters]
  have hcallC := Within.call (procedure := d.cmp) (arguments := [.register 1, .register 2])
    (results := [3, 4]) (regs := zeroed) (returned := RegisterComparator.flags .eq)
    (by simpa only [hargsC] using hcmp) hbranch
  have hargsZ : values regs [.register 1] = [.pointer bp] := by
    simp [regs, values, Atom.eval, initialRegisters]
  have hcallZ := Within.call (procedure := d.zero) (arguments := [.register 1]) (results := [2])
    (regs := regs) (returned := [.pointer zp]) (by simpa only [hargsZ] using hze) hcallC
  refine ⟨out, hext, hvalid, ha.mono hext, ?_⟩
  rw [hself]
  exact hcallZ.mono (by simp only [List.length_cons, List.length_nil]; omega)

/-- A binary-width bound on the second argument proves termination and bounds
the actual closed execution. -/
theorem euclid_compiled (code : Code p) (d : RegisterDivision.Procedures p)
    (hm : d.Matches code) (self remProc : Fin p)
    (hself : code self = gcdBody self remProc d.zero d.cmp)
    (hrem : code remProc = RegisterDivision.remainderBody d.divide)
    {n k : ℕ} {h : Heap} (hh : Valid h) {ap bp : Ptr} {a b : Bits n}
    (ha : BitsAt h ap a) (hb : BitsAt h bp b) (hwidth : b.value < 2 ^ k) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out result (Bits.euclid k a b).1 ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp]) (code self)
        [.pointer result] out (1200 * (n + 1) ^ 2 * (k + 1)) := by
  induction k generalizing h ap bp a b with
  | zero =>
      have hb0 : b.value = 0 := by simpa using hwidth
      obtain ⟨out, hx, hv, hr, he⟩ := stop_compiled code d hm self remProc hself hh ha hb hb0
      refine ⟨out, ap, hx, hv, ?_, he.mono (by nlinarith)⟩
      simpa [Bits.euclid] using hr
  | succ k ih =>
      by_cases hb0 : b.value = 0
      · obtain ⟨out, hx, hv, hr, he⟩ := stop_compiled code d hm self remProc hself hh ha hb hb0
        refine ⟨out, ap, hx, hv, ?_, he.mono (by nlinarith)⟩
        simpa [euclid_zero (k + 1) a b hb0] using hr
      · obtain ⟨zh, zp, hzext, hzvalid, hzrep, hzlen, hze⟩ :=
          RegisterZero.compiled code d.zero hm.1 hh hb
        have haz := ha.mono hzext
        have hbz := hb.mono hzext
        have hbc := RegisterComparator.compiled code d.cmp hm.2.1 hbz hzrep
        let bcmp := (Bits.compare b (Bits.zero n)).1
        have hbn : bcmp ≠ .eq := by
          intro heq
          apply hb0
          exact (Bits.compare_correct b (Bits.zero n)).2.1.mp heq |>.trans (Bits.value_zero n)
        let regs := initialRegisters [Value.pointer ap, .pointer bp]
        let zeroed := bindResults regs [2] [Value.pointer zp]
        let bchecked := bindResults zeroed [3, 4] (RegisterComparator.flags bcmp)
        obtain ⟨rh, rptr, hrext, hrvalid, hrrep, hre⟩ :=
          RegisterDivision.remainder_compiled code d hm hzvalid haz hbz
        rw [← hrem] at hre
        let r := (Bits.remainder a b).1
        have hrv : r.value = a.value % b.value := Bits.remainder_value a b
        have hrlt : r.value < b.value := by rw [hrv]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero hb0)
        have hbrr := hbz.mono hrext
        have hzrr := hzrep.mono hrext
        have hrc := RegisterComparator.compiled code d.cmp hm.2.1 hrrep hzrr
        let rcmp := (Bits.compare r (Bits.zero n)).1
        let firstDone := bindResults bchecked [5] [Value.pointer rptr]
        let rchecked := bindResults firstDone [6, 7] (RegisterComparator.flags rcmp)
        have hb1 : rchecked 1 = .pointer bp := by
          simp [rchecked, firstDone, bchecked, zeroed, regs, bindResults,
            RegisterComparator.flags, initialRegisters]
        have hr5 : rchecked 5 = .pointer rptr := by
          simp [rchecked, firstDone, bindResults, RegisterComparator.flags]
        have hc7 : rchecked 7 = .flag (decide (rcmp = .eq)) := by
          simp [rchecked, bindResults, RegisterComparator.flags]
        obtain ⟨out, result, hx, hv, hrep, hsecond⟩ :
            ∃ out : Heap, ∃ result : Ptr, Extends rh out ∧ Valid out ∧
              BitsAt out result (Bits.euclid (k + 1) a b).1 ∧
              Within code rh rchecked (secondBranch self remProc) [.pointer result] out
                (1200 * (n + 1) ^ 2 * (k + 1) + 400 * (n + 1) ^ 2 + 34) := by
          by_cases hr0 : r.value = 0
          · have hrEq : rcmp = .eq :=
              (Bits.compare_correct r (Bits.zero n)).2.1.mpr (by simpa using hr0)
            have last : Within code rh rchecked (.ret [.register 1]) [.pointer bp] rh 3 := by
              simpa [values, Atom.eval, hb1] using Within.ret code rh rchecked [.register 1]
            have hbranch := Within.branch (b := true) (test := .register 7)
              (yes := .ret [.register 1])
              (no := .call remProc [.register 1, .register 5] [8] (afterSecond self))
              (by simpa [Atom.eval, hrEq] using hc7) last
            refine ⟨rh, bp, .refl rh, hrvalid, ?_, hbranch.mono (by nlinarith)⟩
            simpa [Bits.euclid, bcmp, hbn, rcmp, r, hrEq] using hbrr
          · have hrNe : rcmp ≠ .eq := by
              intro heq
              exact hr0 ((Bits.compare_correct r (Bits.zero n)).2.1.mp heq |>.trans (Bits.value_zero n))
            obtain ⟨th, tptr, htext, htvalid, htrep, hte⟩ :=
              RegisterDivision.remainder_compiled code d hm hrvalid hbrr hrrep
            rw [← hrem] at hte
            let t := (Bits.remainder b r).1
            have htwidth : t.value < 2 ^ k := by
              rw [Bits.remainder_value]
              exact Bits.second_remainder_lt hwidth hrlt hr0
            obtain ⟨out, result, hx, hv, hrep, child⟩ :=
              ih htvalid (hrrep.mono htext) htrep htwidth
            let secondDone := bindResults rchecked [8] [Value.pointer tptr]
            let ready := bindResults secondDone [9] [Value.pointer result]
            have last : Within code out ready (.ret [.register 9]) [.pointer result] out 3 := by
              simpa [ready, bindResults, values, Atom.eval] using Within.ret code out ready [.register 9]
            have hargsE : values secondDone [.register 5, .register 8] =
                [.pointer rptr, .pointer tptr] := by
              simp [secondDone, bindResults, values, Atom.eval, hr5]
            have hcallE := Within.call (procedure := self) (arguments := [.register 5, .register 8])
              (results := [9]) (regs := secondDone) (returned := [.pointer result])
              (by simpa only [hargsE] using child) last
            have hargsR : values rchecked [.register 1, .register 5] = [.pointer bp, .pointer rptr] := by
              simp [values, Atom.eval, hb1, hr5]
            have hcallR := Within.call (procedure := remProc) (arguments := [.register 1, .register 5])
              (results := [8]) (regs := rchecked) (returned := [.pointer tptr])
              (by simpa only [hargsR] using hte) hcallE
            have hbranch := Within.branch (b := false) (test := .register 7)
              (yes := .ret [.register 1])
              (no := .call remProc [.register 1, .register 5] [8] (afterSecond self))
              (by simpa [Atom.eval, hrNe] using hc7) hcallR
            refine ⟨out, result, htext.trans hx, hv, ?_,
              hbranch.mono (by simp only [List.length_cons, List.length_nil]; omega)⟩
            simpa [Bits.euclid, bcmp, hbn, rcmp, r, t, hrNe] using hrep
        refine ⟨out, result, hzext.trans (hrext.trans hx), hv, hrep, ?_⟩
        rw [hself]
        have hargsRC : values firstDone [.register 5, .register 2] = [.pointer rptr, .pointer zp] := by
          simp [firstDone, bchecked, zeroed, bindResults, RegisterComparator.flags, values, Atom.eval]
        have hcallRC := Within.call (procedure := d.cmp) (arguments := [.register 5, .register 2])
          (results := [6, 7]) (regs := firstDone) (returned := RegisterComparator.flags rcmp)
          (by simpa only [hargsRC] using hrc) hsecond
        have hargsR : values bchecked [.register 0, .register 1] = [.pointer ap, .pointer bp] := by
          simp [bchecked, zeroed, regs, bindResults, RegisterComparator.flags,
            values, Atom.eval, initialRegisters]
        have hcallR := Within.call (procedure := remProc) (arguments := [.register 0, .register 1])
          (results := [5]) (regs := bchecked) (returned := [.pointer rptr])
          (by simpa only [hargsR] using hre) hcallRC
        have hc4 : bchecked 4 = .flag false := by
          simp [bchecked, bindResults, RegisterComparator.flags, hbn]
        have hbranch := Within.branch (b := false) (test := .register 4)
          (yes := .ret [.register 0]) (no := firstRemainder self remProc d.cmp)
          (by simpa [Atom.eval] using hc4) hcallR
        have hargsBC : values zeroed [.register 1, .register 2] = [.pointer bp, .pointer zp] := by
          simp [zeroed, regs, bindResults, values, Atom.eval, initialRegisters]
        have hcallBC := Within.call (procedure := d.cmp) (arguments := [.register 1, .register 2])
          (results := [3, 4]) (regs := zeroed) (returned := RegisterComparator.flags bcmp)
          (by simpa only [hargsBC] using hbc) hbranch
        have hargsZ : values regs [.register 1] = [.pointer bp] := by
          simp [regs, values, Atom.eval, initialRegisters]
        have hcallZ := Within.call (procedure := d.zero) (arguments := [.register 1]) (results := [2])
          (regs := regs) (returned := [.pointer zp]) (by simpa only [hargsZ] using hze) hcallBC
        exact hcallZ.mono (by simp only [List.length_cons, List.length_nil]; nlinarith)

/-- The complete closed gcd procedure has a cubic event bound. -/
theorem compiled (code : Code p) (d : RegisterDivision.Procedures p)
    (hm : d.Matches code) (self remProc : Fin p)
    (hself : code self = gcdBody self remProc d.zero d.cmp)
    (hrem : code remProc = RegisterDivision.remainderBody d.divide)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap bp : Ptr} {a b : Bits n}
    (ha : BitsAt h ap a) (hb : BitsAt h bp b) :
    ∃ out : Heap, ∃ result : Ptr, ∃ g : Bits n, Extends h out ∧ Valid out ∧
      BitsAt out result g ∧ g.value = Nat.gcd a.value b.value ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp]) (code self)
        [.pointer result] out (1200 * (n + 1) ^ 3) := by
  obtain ⟨out, result, hx, hv, hr, he⟩ :=
    euclid_compiled code d hm self remProc hself hrem hh ha hb (Bits.value_lt b)
  refine ⟨out, result, (Bits.gcd a b).1, hx, hv, hr, Bits.gcd_value a b, ?_⟩
  convert he using 1 <;> ring

end WeightedMIS.RegisterGCD
