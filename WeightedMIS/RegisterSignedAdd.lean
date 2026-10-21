module

public import WeightedMIS.RegisterNormalization

/-! # Closed register code for signed-magnitude addition -/

@[expose] public section

namespace WeightedMIS.RegisterSignedAdd

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

variable {p : ℕ}

def sameBody (add : Fin p) (sign : Bool) : Command p :=
  .call add [.register 1, .register 3, .flag false] [6, 7]
    (.ret [.flag sign, .register 6])

def subtractCase (sub : Fin p) (left right sign : Register) : Command p :=
  .call sub [.register left, .register right] [6, 7]
    (.ret [.register sign, .register 6])

def oppositeBody (cmp sub : Fin p) : Command p :=
  .call cmp [.register 1, .register 3] [4, 5]
    (.branch (.register 4) (subtractCase sub 3 1 2) (subtractCase sub 1 3 0))

def signedAddBody (add cmp sub : Fin p) : Command p :=
  .branch (.register 0)
    (.branch (.register 2) (sameBody add true) (oppositeBody cmp sub))
    (.branch (.register 2) (oppositeBody cmp sub) (sameBody add false))

theorem same_compiled (code : Code p) (add : Fin p)
    (hadd : code add = RegisterAdder.adderBody add)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap bp : Ptr} {a b : Bits n}
    (ha : BitsAt h ap a) (hb : BitsAt h bp b) (regs : Registers) (sign : Bool)
    (ha1 : regs 1 = .pointer ap) (hb3 : regs 3 = .pointer bp) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out result (Bits.add a b).1 ∧
      Within code h regs (sameBody add sign) [.flag sign, .pointer result] out (110 * n + 42) := by
  let r := addCarryPointer n ap bp false h
  have hs := addCarryPointer_refines hh ha hb false
  have he := RegisterAdder.compiled code add hadd (addCarryPointer_eval hh ha hb false)
  change Within code h (initialRegisters [.pointer ap, .pointer bp, .flag false]) (code add)
    [.pointer r.value.1, .flag r.value.2] r.heap (10 * r.trace.length) at he
  have hlen : r.trace.length = 11 * n + 3 := hs.2.2.2
  rw [hlen] at he
  refine ⟨r.heap, r.value.1, hs.1.1, hs.1.2.1, hs.2.1, ?_⟩
  let ready := bindResults regs [6, 7] [Value.pointer r.value.1, .flag r.value.2]
  have last : Within code r.heap ready (.ret [.flag sign, .register 6])
      [.flag sign, .pointer r.value.1] r.heap 5 := by
    simpa [ready, bindResults, values, Atom.eval] using
      Within.ret code r.heap ready [.flag sign, .register 6]
  have hargs : values regs [.register 1, .register 3, .flag false] =
      [.pointer ap, .pointer bp, .flag false] := by simp [values, Atom.eval, ha1, hb3]
  have hcall := Within.call (procedure := add) (arguments := [.register 1, .register 3, .flag false])
    (results := [6, 7]) (regs := regs) (returned := [.pointer r.value.1, .flag r.value.2])
    (by simpa only [hargs] using he) last
  exact hcall.mono (by simp only [List.length_cons, List.length_nil]; omega)

theorem subtractCase_compiled (code : Code p) (sub complement add : Fin p)
    (hsub : code sub = RegisterSubtractor.subtractorBody complement add)
    (hcomp : code complement = RegisterComplement.complementBody complement)
    (hadd : code add = RegisterAdder.adderBody add)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap bp : Ptr} {a b : Bits n}
    (ha : BitsAt h ap a) (hb : BitsAt h bp b) (regs : Registers)
    (left right sign : Register) (s : Bool) (hsafe : sign ≠ 6) (hsafe7 : sign ≠ 7)
    (hl : regs left = .pointer ap) (hr : regs right = .pointer bp) (hs : regs sign = .flag s) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out result (Bits.subtract a b).1 ∧
      Within code h regs (subtractCase sub left right sign) [.flag s, .pointer result]
        out (137 * n + 68) := by
  obtain ⟨out, result, hx, hv, hrep, he⟩ :=
    RegisterSubtractor.compiled code complement add hcomp hadd hh ha hb
  rw [← hsub] at he
  let ready := bindResults regs [6, 7] [Value.pointer result, .flag (Bits.subtract a b).2.1]
  have last : Within code out ready (.ret [.register sign, .register 6])
      [.flag s, .pointer result] out 5 := by
    simpa [ready, bindResults, values, Atom.eval, hsafe, hsafe7, hs] using
      Within.ret code out ready [.register sign, .register 6]
  have hargs : values regs [.register left, .register right] = [.pointer ap, .pointer bp] := by
    simp [values, Atom.eval, hl, hr]
  have hcall := Within.call (procedure := sub) (arguments := [.register left, .register right])
    (results := [6, 7]) (regs := regs) (returned := [.pointer result, .flag (Bits.subtract a b).2.1])
    (by simpa only [hargs] using he) last
  exact ⟨out, result, hx, hv, hrep,
    hcall.mono (by simp only [List.length_cons, List.length_nil]; omega)⟩

def opposite (s t : Bool) {n : ℕ} (a b : Bits n) : Bool × Bits n :=
  if (Bits.compare a b).1 = .lt then (t, (Bits.subtract b a).1)
  else (s, (Bits.subtract a b).1)

theorem opposite_compiled (code : Code p) (cmp sub complement add : Fin p)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (hsub : code sub = RegisterSubtractor.subtractorBody complement add)
    (hcomp : code complement = RegisterComplement.complementBody complement)
    (hadd : code add = RegisterAdder.adderBody add)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap bp : Ptr} {a b : Bits n}
    (ha : BitsAt h ap a) (hb : BitsAt h bp b) (regs : Registers) (s t : Bool)
    (ha1 : regs 1 = .pointer ap) (hb3 : regs 3 = .pointer bp)
    (hs0 : regs 0 = .flag s) (ht2 : regs 2 = .flag t) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out result (opposite s t a b).2 ∧
      Within code h regs (oppositeBody cmp sub) [.flag (opposite s t a b).1, .pointer result]
        out (173 * n + 101) := by
  have hce := RegisterComparator.compiled code cmp hcmp ha hb
  let compared := bindResults regs [4, 5] (RegisterComparator.flags (Bits.compare a b).1)
  have hc4 : compared 4 = .flag (decide ((Bits.compare a b).1 = .lt)) := by
    simp [compared, bindResults, RegisterComparator.flags]
  obtain ⟨out, result, hx, hv, hrep, hbranch⟩ :
      ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
        BitsAt out result (opposite s t a b).2 ∧
        Within code h compared
          (.branch (.register 4) (subtractCase sub 3 1 2) (subtractCase sub 1 3 0))
          [.flag (opposite s t a b).1, .pointer result] out (137 * n + 71) := by
    by_cases hlt : (Bits.compare a b).1 = .lt
    · obtain ⟨out, result, hx, hv, hr, he⟩ :=
        subtractCase_compiled code sub complement add hsub hcomp hadd hh hb ha compared 3 1 2 t
          (by decide) (by decide)
          (by simp [compared, bindResults, RegisterComparator.flags, hb3])
          (by simp [compared, bindResults, RegisterComparator.flags, ha1])
          (by simp [compared, bindResults, RegisterComparator.flags, ht2])
      have hbr := Within.branch (b := true) (test := .register 4)
        (yes := subtractCase sub 3 1 2) (no := subtractCase sub 1 3 0)
        (by simpa [Atom.eval, hlt] using hc4) he
      refine ⟨out, result, hx, hv, ?_, ?_⟩
      · simpa [opposite, hlt] using hr
      · simpa [opposite, hlt] using hbr.mono (show 3 + (137 * n + 68) ≤ 137 * n + 71 by omega)
    · obtain ⟨out, result, hx, hv, hr, he⟩ :=
        subtractCase_compiled code sub complement add hsub hcomp hadd hh ha hb compared 1 3 0 s
          (by decide) (by decide)
          (by simp [compared, bindResults, RegisterComparator.flags, ha1])
          (by simp [compared, bindResults, RegisterComparator.flags, hb3])
          (by simp [compared, bindResults, RegisterComparator.flags, hs0])
      have hbr := Within.branch (b := false) (test := .register 4)
        (yes := subtractCase sub 3 1 2) (no := subtractCase sub 1 3 0)
        (by simpa [Atom.eval, hlt] using hc4) he
      refine ⟨out, result, hx, hv, ?_, ?_⟩
      · simpa [opposite, hlt] using hr
      · simpa [opposite, hlt] using hbr.mono (show 3 + (137 * n + 68) ≤ 137 * n + 71 by omega)
  have hargs : values regs [.register 1, .register 3] = [.pointer ap, .pointer bp] := by
    simp [values, Atom.eval, ha1, hb3]
  have hcall := Within.call (procedure := cmp) (arguments := [.register 1, .register 3])
    (results := [4, 5]) (regs := regs) (returned := RegisterComparator.flags (Bits.compare a b).1)
    (by simpa only [hargs] using hce) hbranch
  exact ⟨out, result, hx, hv, hrep,
    hcall.mono (by simp only [List.length_cons, List.length_nil]; omega)⟩

theorem signedAdd_opposite (s t : Bool) {n : ℕ} (a b : Bits n) (hne : s ≠ t) :
    (BinaryRational.signedAdd s t a b).1 = opposite s t a b := by
  simp only [BinaryRational.signedAdd, hne, ↓reduceIte, opposite]
  split <;> rfl

/-- The four-input ABI is sign, magnitude pointer, sign, magnitude pointer. -/
theorem compiled (code : Code p) (cmp sub complement add : Fin p)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (hsub : code sub = RegisterSubtractor.subtractorBody complement add)
    (hcomp : code complement = RegisterComplement.complementBody complement)
    (hadd : code add = RegisterAdder.adderBody add)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap bp : Ptr} {a b : Bits n}
    (ha : BitsAt h ap a) (hb : BitsAt h bp b) (s t : Bool) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out result (BinaryRational.signedAdd s t a b).1.2 ∧
      Within code h (initialRegisters [.flag s, .pointer ap, .flag t, .pointer bp])
        (signedAddBody add cmp sub)
        [.flag (BinaryRational.signedAdd s t a b).1.1, .pointer result]
        out (180 * n + 120) := by
  let regs := initialRegisters [Value.flag s, .pointer ap, .flag t, .pointer bp]
  have ha1 : regs 1 = .pointer ap := by simp [regs, initialRegisters]
  have hb3 : regs 3 = .pointer bp := by simp [regs, initialRegisters]
  have hs0 : regs 0 = .flag s := by simp [regs, initialRegisters]
  have ht2 : regs 2 = .flag t := by simp [regs, initialRegisters]
  cases s <;> cases t
  · obtain ⟨out, result, hx, hv, hr, he⟩ := same_compiled code add hadd hh ha hb regs false ha1 hb3
    have h1 := Within.branch (b := false) (test := .register 2)
      (yes := oppositeBody cmp sub) (no := sameBody add false)
      (by simpa [Atom.eval] using ht2) he
    have h2 := Within.branch (b := false) (test := .register 0)
      (yes := .branch (.register 2) (sameBody add true) (oppositeBody cmp sub))
      (no := .branch (.register 2) (oppositeBody cmp sub) (sameBody add false))
      (by simpa [Atom.eval] using hs0) h1
    refine ⟨out, result, hx, hv, ?_, ?_⟩
    · simpa [BinaryRational.signedAdd, regs, signedAddBody] using hr
    · simpa [BinaryRational.signedAdd, regs, signedAddBody] using h2.mono (show 3 + (3 + (110 * n + 42)) ≤ 180 * n + 120 by omega)
  · obtain ⟨out, result, hx, hv, hr, he⟩ :=
      opposite_compiled code cmp sub complement add hcmp hsub hcomp hadd hh ha hb regs false true ha1 hb3 hs0 ht2
    have h1 := Within.branch (b := true) (test := .register 2)
      (yes := oppositeBody cmp sub) (no := sameBody add false)
      (by simpa [Atom.eval] using ht2) he
    have h2 := Within.branch (b := false) (test := .register 0)
      (yes := .branch (.register 2) (sameBody add true) (oppositeBody cmp sub))
      (no := .branch (.register 2) (oppositeBody cmp sub) (sameBody add false))
      (by simpa [Atom.eval] using hs0) h1
    refine ⟨out, result, hx, hv, ?_, ?_⟩
    · simpa [signedAdd_opposite, regs, signedAddBody] using hr
    · simpa [signedAdd_opposite, regs, signedAddBody] using h2.mono (show 3 + (3 + (173 * n + 101)) ≤ 180 * n + 120 by omega)
  · obtain ⟨out, result, hx, hv, hr, he⟩ :=
      opposite_compiled code cmp sub complement add hcmp hsub hcomp hadd hh ha hb regs true false ha1 hb3 hs0 ht2
    have h1 := Within.branch (b := false) (test := .register 2)
      (yes := sameBody add true) (no := oppositeBody cmp sub)
      (by simpa [Atom.eval] using ht2) he
    have h2 := Within.branch (b := true) (test := .register 0)
      (yes := .branch (.register 2) (sameBody add true) (oppositeBody cmp sub))
      (no := .branch (.register 2) (oppositeBody cmp sub) (sameBody add false))
      (by simpa [Atom.eval] using hs0) h1
    refine ⟨out, result, hx, hv, ?_, ?_⟩
    · simpa [signedAdd_opposite, regs, signedAddBody] using hr
    · simpa [signedAdd_opposite, regs, signedAddBody] using h2.mono (show 3 + (3 + (173 * n + 101)) ≤ 180 * n + 120 by omega)
  · obtain ⟨out, result, hx, hv, hr, he⟩ := same_compiled code add hadd hh ha hb regs true ha1 hb3
    have h1 := Within.branch (b := true) (test := .register 2)
      (yes := sameBody add true) (no := oppositeBody cmp sub)
      (by simpa [Atom.eval] using ht2) he
    have h2 := Within.branch (b := true) (test := .register 0)
      (yes := .branch (.register 2) (sameBody add true) (oppositeBody cmp sub))
      (no := .branch (.register 2) (oppositeBody cmp sub) (sameBody add false))
      (by simpa [Atom.eval] using hs0) h1
    refine ⟨out, result, hx, hv, ?_, ?_⟩
    · simpa [BinaryRational.signedAdd, regs, signedAddBody] using hr
    · simpa [BinaryRational.signedAdd, regs, signedAddBody] using h2.mono (show 3 + (3 + (110 * n + 42)) ≤ 180 * n + 120 by omega)

end WeightedMIS.RegisterSignedAdd
