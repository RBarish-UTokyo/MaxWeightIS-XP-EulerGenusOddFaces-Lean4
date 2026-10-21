module

public import WeightedMIS.RegisterSignedDot
public import WeightedMIS.RegisterSignedHalf

/-!
# The compiled root value `(1 - Σ π e y e) / 2`

The signed dot product of the stored odd row with the stored counts is
computed by `RegisterSignedDot`. The numerator `1 - dot` is one signed binary
addition with the opposite sign of the dot product, selected by a branch on
the actual sign bit. The halving keeps the sign and shifts the magnitude
(`RegisterSignedHalf`). Exactness of the halving is a hypothesis: the
numerator must be even, which holds for the actual hard-component data by
`HardSolveReference.hardLabels_even`.
-/

@[expose] public section

namespace WeightedMIS.RegisterRootValue

open scoped BigOperators
open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords
open WeightedMIS.RegisterPotentialStep

variable {B : ℕ}

/-! ## Reference -/

/-- The signed numerator `1 - dot`. -/
def numerator (one : Bits B) (πs : List (Word B)) (ys : List (Bits B)) : Word B :=
  let d := RegisterSignedDot.dot πs ys
  (BinaryRational.signedAdd false (!d.1) one d.2).1

/-- The halved numerator. -/
def rootWord (one : Bits B) (πs : List (Word B)) (ys : List (Bits B)) : Word B :=
  RegisterSignedHalf.half (numerator one πs ys)

theorem numerator_value (one : Bits B) (πs : List (Word B)) (ys : List (Bits B))
    (hone : one.value = 1) (hfit : 1 + RegisterSignedDot.mass πs ys < 2 ^ B) :
    value (numerator one πs ys) = 1 - RegisterSignedDot.integerDot πs ys ∧
      (numerator one πs ys).2.value ≤ 1 + RegisterSignedDot.mass πs ys := by
  obtain ⟨hv, hm⟩ := RegisterSignedDot.dot_correct πs ys (by omega)
  have hsum : one.value + (RegisterSignedDot.dot πs ys).2.value < 2 ^ B := by omega
  have hadd := BinaryRational.signedAdd_value false (!(RegisterSignedDot.dot πs ys).1) one
    (RegisterSignedDot.dot πs ys).2 hsum
  have heq : value (numerator one πs ys) = 1 - RegisterSignedDot.integerDot πs ys := by
    unfold numerator value
    rw [hadd, signed_not, hone, ← hv]
    simp [value, BinaryRational.signed, sub_eq_add_neg]
  refine ⟨heq, ?_⟩
  rw [← value_natAbs, heq]
  have hb := Int.natAbs_sub_le 1 (RegisterSignedDot.integerDot πs ys)
  rw [← hv, value_natAbs] at hb
  simp only [Int.natAbs_one] at hb
  omega

theorem rootWord_value (one : Bits B) (πs : List (Word B)) (ys : List (Bits B))
    (hone : one.value = 1) (hfit : 1 + RegisterSignedDot.mass πs ys < 2 ^ B)
    (heven : Even (1 - RegisterSignedDot.integerDot πs ys)) :
    value (rootWord one πs ys) = (1 - RegisterSignedDot.integerDot πs ys) / 2 ∧
      (rootWord one πs ys).2.value ≤ 1 + RegisterSignedDot.mass πs ys := by
  obtain ⟨hv, hm⟩ := numerator_value one πs ys hone hfit
  constructor
  · rw [rootWord, RegisterSignedHalf.half_div _ (by rw [hv]; exact heven), hv]
  · change (RegisterHalve.halve (numerator one πs ys).2).value ≤ _
    rw [RegisterHalve.halve_value]
    exact le_trans (Nat.div_le_self _ _) hm

theorem integerDot_map {m : ℕ} (πw : Fin m → Word B) (yw : Fin m → Bits B) :
    RegisterSignedDot.integerDot ((List.finRange m).map πw) ((List.finRange m).map yw) =
      ∑ e, value (πw e) * ((yw e).value : ℤ) := by
  rw [← List.sum_ofFn, List.ofFn_eq_map]
  generalize List.finRange m = l
  induction l with
  | nil => rfl
  | cons a l ih => simp [RegisterSignedDot.integerDot, ih]

theorem mass_map {m : ℕ} (πw : Fin m → Word B) (yw : Fin m → Bits B) :
    RegisterSignedDot.mass ((List.finRange m).map πw) ((List.finRange m).map yw) =
      ∑ e, (πw e).2.value * (yw e).value := by
  rw [← List.sum_ofFn, List.ofFn_eq_map]
  generalize List.finRange m = l
  induction l with
  | nil => rfl
  | cons a l ih => simp [RegisterSignedDot.mass, ih]

/-! ## Procedure -/

variable {p : ℕ}

def finishBody (signedAdd half : Fin p) (negative : Bool) : Command p :=
  .call signedAdd [.flag false, .register 3, .flag negative, .register 5] [6, 7]
    (.call half [.register 6, .register 7] [8, 9] (.ret [.register 8, .register 9]))

/-- Arguments: signed coefficients, counts, zero word, one word.
Results: sign and magnitude of the halved numerator. -/
def rootBody (dot signedAdd half : Fin p) : Command p :=
  .call dot [.register 0, .register 1, .register 2] [4, 5]
    (.branch (.register 4) (finishBody signedAdd half false) (finishBody signedAdd half true))

structure Procedures (p : ℕ) where
  arith : RegisterSignedDot.Procedures p
  dot : Fin p
  shift : Fin p
  half : Fin p
  self : Fin p

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  RegisterSignedDot.Matches code d.arith ∧
  code d.dot = RegisterSignedDot.dotBody d.dot d.arith ∧
  code d.shift = RegisterHalve.shiftBody d.shift ∧
  code d.half = RegisterSignedHalf.halfBody d.shift ∧
  code d.self = rootBody d.dot d.arith.signedAdd d.half

def budget (B m : ℕ) : ℕ := 500 * (B + 1) ^ 2 * m + 210 * B + 200

theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {h : Heap} (hh : Valid h) {ap yp zp op : Ptr}
    {πs : List (Word B)} {ys : List (Bits B)} {one : Bits B}
    (ha : SignedWords.ListAt h ap πs) (hy : WordsAt h yp ys)
    (hz : BitsAt h zp (Bits.zero B)) (ho : BitsAt h op one) (hlen : πs.length = ys.length) :
    ∃ out result, Extends h out ∧ Valid out ∧ BitsAt out result (rootWord one πs ys).2 ∧
      Within code h (initialRegisters [.pointer ap, .pointer yp, .pointer zp, .pointer op])
        (code d.self) [.flag (rootWord one πs ys).1, .pointer result] out (budget B πs.length) := by
  obtain ⟨hmatch, hdot, hshift, hhalf, hself⟩ := hm
  have hmatch' := hmatch
  obtain ⟨-, hadd, hcmp, hcomp, hsub, -, -, -, -, hsigned⟩ := hmatch'
  obtain ⟨H1, mp, e1, v1, hmag, drun⟩ :=
    RegisterSignedDot.compiled code d.dot d.arith hdot hmatch hh ha hy hz hlen
  let dd := RegisterSignedDot.dot πs ys
  obtain ⟨H2, np, e2, v2, hnum, arun⟩ := RegisterSignedAdd.compiled code d.arith.cmp d.arith.sub
    d.arith.complement d.arith.add hcmp hsub hcomp hadd v1 (ho.mono e1) hmag false (!dd.1)
  obtain ⟨H3, rp, e3, v3, hres, hrun⟩ := RegisterSignedHalf.compiled code d.shift hshift v2
    (a := numerator one πs ys) hnum
  refine ⟨H3, rp, e1.trans (e2.trans e3), v3, hres, ?_⟩
  let regs := initialRegisters [Value.pointer ap, .pointer yp, .pointer zp, .pointer op]
  let s1 := bindResults regs [4, 5] [.flag dd.1, .pointer mp]
  have fin : Within code H1 s1 (finishBody d.arith.signedAdd d.half (!dd.1))
      [.flag (rootWord one πs ys).1, .pointer rp] H3 (180 * B + 28 * B + 170) := by
    let s2 := bindResults s1 [6, 7] [.flag (numerator one πs ys).1, .pointer np]
    let s3 := bindResults s2 [8, 9] [.flag (rootWord one πs ys).1, .pointer rp]
    have last : Within code H3 s3 (.ret [.register 8, .register 9])
        [.flag (rootWord one πs ys).1, .pointer rp] H3 5 := by
      simpa [s3, bindResults, values, Atom.eval] using
        Within.ret code H3 s3 [.register 8, .register 9]
    have hargs : values s2 [.register 6, .register 7] =
        [.flag (numerator one πs ys).1, .pointer np] := by
      simp [s2, bindResults, values, Atom.eval]
    have hcall := Within.call (procedure := d.half) (regs := s2)
      (arguments := [.register 6, .register 7]) (results := [8, 9])
      (by rw [hargs, hhalf]; exact hrun) last
    have aargs : values s1 [.flag false, .register 3, .flag (!dd.1), .register 5] =
        [.flag false, .pointer op, .flag (!dd.1), .pointer mp] := by
      simp [s1, regs, bindResults, initialRegisters, values, Atom.eval]
    have acall := Within.call (procedure := d.arith.signedAdd) (regs := s1)
      (arguments := [.flag false, .register 3, .flag (!dd.1), .register 5]) (results := [6, 7])
      (by rw [aargs, hsigned]; exact arun) hcall
    exact acall.mono (by simp; omega)
  have br : Within code H1 s1
      (.branch (.register 4) (finishBody d.arith.signedAdd d.half false)
        (finishBody d.arith.signedAdd d.half true))
      [.flag (rootWord one πs ys).1, .pointer rp] H3 (3 + (180 * B + 28 * B + 170)) := by
    apply Within.branch (b := dd.1) (by simp [s1, bindResults, Atom.eval])
    cases hs : dd.1
    · simpa [hs] using fin
    · simpa [hs] using fin
  have dargs : values regs [.register 0, .register 1, .register 2] =
      [.pointer ap, .pointer yp, .pointer zp] := by
    simp [regs, initialRegisters, values, Atom.eval]
  have dcall := Within.call (procedure := d.dot) (regs := regs)
    (arguments := [.register 0, .register 1, .register 2]) (results := [4, 5])
    (by simpa only [dargs] using drun) br
  rw [hself]
  exact dcall.mono (by simp [budget, RegisterSignedDot.budget]; omega)

end WeightedMIS.RegisterRootValue
