module

public import WeightedMIS.RegisterSignedAdd
public import WeightedMIS.RegisterHalve

/-!
# The integer-potential update on a represented edge count

The finite code computes `1 - count - current` using two signed binary additions.
Signs are ordinary Boolean registers and magnitudes are represented binary words.
-/

@[expose] public section

namespace WeightedMIS.RegisterPotentialStep

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

abbrev Word (n : ℕ) := Bool × Bits n

def value {n : ℕ} (a : Word n) : ℤ := BinaryRational.signed a.1 a.2.value

def difference {n : ℕ} (one count : Bits n) : Word n :=
  (BinaryRational.signedAdd false true one count).1

def step {n : ℕ} (one count : Bits n) (a : Word n) : Word n :=
  let d := difference one count
  (BinaryRational.signedAdd d.1 (!a.1) d.2 a.2).1

theorem signed_not (s : Bool) (a : ℕ) :
    BinaryRational.signed (!s) a = -BinaryRational.signed s a := by
  cases s <;> simp [BinaryRational.signed]

@[simp] theorem value_natAbs {n : ℕ} (a : Word n) : (value a).natAbs = a.2.value := by
  rcases a with ⟨s, a⟩
  cases s <;> simp [value, BinaryRational.signed]

theorem difference_value {n : ℕ} (one count : Bits n)
    (h : one.value + count.value < 2 ^ n) :
    value (difference one count) = (one.value : ℤ) - count.value := by
  unfold value difference
  rw [BinaryRational.signedAdd_value false true one count h]
  simp [BinaryRational.signed, sub_eq_add_neg]

theorem difference_magnitude_le {n : ℕ} (one count : Bits n)
    (h : one.value + count.value < 2 ^ n) :
    (difference one count).2.value ≤ one.value + count.value := by
  rw [← value_natAbs, difference_value one count h]
  exact le_trans (Int.natAbs_sub_le _ _) (by simp)

theorem step_value {n : ℕ} (one count : Bits n) (a : Word n)
    (hone : one.value = 1)
    (hfit : one.value + count.value + a.2.value < 2 ^ n) :
    value (step one count a) = 1 - (count.value : ℤ) - value a := by
  have hd : one.value + count.value < 2 ^ n := by omega
  have hb : (difference one count).2.value + a.2.value < 2 ^ n :=
    lt_of_le_of_lt (Nat.add_le_add_right (difference_magnitude_le one count hd) _) hfit
  rw [step, value, BinaryRational.signedAdd_value _ _ _ _ hb, signed_not]
  change value (difference one count) + -value a = _
  rw [difference_value one count hd, hone]
  simp [sub_eq_add_neg]

variable {p : ℕ}

def finishBody (signedAdd : Fin p) (negative : Bool) : Command p :=
  .call signedAdd [.register 4, .register 5, .flag negative, .register 3] [6, 7]
    (.ret [.register 6, .register 7])

/-- Input: one word, count word, current sign, current magnitude.
Output: next sign, next magnitude. -/
def stepBody (signedAdd : Fin p) : Command p :=
  .call signedAdd [.flag false, .register 0, .flag true, .register 1] [4, 5]
    (.branch (.register 2) (finishBody signedAdd false) (finishBody signedAdd true))

theorem compiled (code : Code p) (signedAdd cmp sub complement add : Fin p)
    (hsigned : code signedAdd = RegisterSignedAdd.signedAddBody add cmp sub)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (hsub : code sub = RegisterSubtractor.subtractorBody complement add)
    (hcomp : code complement = RegisterComplement.complementBody complement)
    (hadd : code add = RegisterAdder.adderBody add)
    {n : ℕ} {h : Heap} (hh : Valid h) {op cp ap : Ptr}
    {one count : Bits n} {a : Word n}
    (ho : BitsAt h op one) (hc : BitsAt h cp count) (ha : BitsAt h ap a.2) :
    ∃ out result, Extends h out ∧ Valid out ∧ BitsAt out result (step one count a).2 ∧
      Within code h (initialRegisters [.pointer op, .pointer cp, .flag a.1, .pointer ap])
        (stepBody signedAdd) [.flag (step one count a).1, .pointer result] out (360 * n + 270) := by
  obtain ⟨mid, dp, hx, hv, hd, hfirst⟩ :=
    RegisterSignedAdd.compiled code cmp sub complement add hcmp hsub hcomp hadd hh ho hc false true
  obtain ⟨out, result, hy, hw, hr, hsecond⟩ :=
    RegisterSignedAdd.compiled code cmp sub complement add hcmp hsub hcomp hadd hv hd (ha.mono hx)
      (difference one count).1 (!a.1)
  let regs := initialRegisters [Value.pointer op, .pointer cp, .flag a.1, .pointer ap]
  let ready := bindResults regs [4, 5] [Value.flag (difference one count).1, .pointer dp]
  let done := bindResults ready [6, 7] [Value.flag (step one count a).1, .pointer result]
  have last : Within code out done (.ret [.register 6, .register 7])
      [.flag (step one count a).1, .pointer result] out 5 := by
    simpa [done, bindResults, values, Atom.eval] using
      Within.ret code out done [.register 6, .register 7]
  have sargs : values ready [.register 4, .register 5, .flag (!a.1), .register 3] =
      [.flag (difference one count).1, .pointer dp, .flag (!a.1), .pointer ap] := by
    simp [ready, regs, bindResults, initialRegisters, values, Atom.eval]
  have second := Within.call (procedure := signedAdd) (regs := ready)
    (arguments := [.register 4, .register 5, .flag (!a.1), .register 3]) (results := [6, 7])
    (by simpa only [sargs, hsigned, step, difference] using hsecond) last
  have branch : Within code mid ready
      (.branch (.register 2) (finishBody signedAdd false) (finishBody signedAdd true))
      [.flag (step one count a).1, .pointer result] out (3 + (9 + (180*n+120) + 5)) := by
    cases hs : a.1
    · exact Within.branch (b := false) (by simp [Atom.eval, ready, regs, bindResults, initialRegisters, hs])
        (by simpa [hs, finishBody] using second)
    · exact Within.branch (b := true) (by simp [Atom.eval, ready, regs, bindResults, initialRegisters, hs])
        (by simpa [hs, finishBody] using second)
  have fargs : values regs [.flag false, .register 0, .flag true, .register 1] =
      [.flag false, .pointer op, .flag true, .pointer cp] := by
    simp [regs, initialRegisters, values, Atom.eval]
  have first := Within.call (procedure := signedAdd) (regs := regs)
    (arguments := [.flag false, .register 0, .flag true, .register 1]) (results := [4, 5])
    (by simpa only [fargs, hsigned, difference] using hfirst) branch
  exact ⟨out, result, hx.trans hy, hw, hr, first.mono (by simp; omega)⟩

end WeightedMIS.RegisterPotentialStep
