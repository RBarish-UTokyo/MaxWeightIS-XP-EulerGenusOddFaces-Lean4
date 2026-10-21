module

public import WeightedMIS.RegisterRationalRow
public import WeightedMIS.RegisterWordFilter
public import WeightedMIS.RegisterListMap
public import WeightedMIS.NegativeWeights

/-!
# Sign mask and truncation of a stored weight row

The input is a row of canonical stored rationals (`StoredRational.At`). A
canonical word with a set sign bit and zero magnitude denotes `0`, so a
weight is nonnegative exactly when its sign bit is clear or its magnitude
word is all zero. The first procedure walks the row and returns the
nonnegativity flags as a stored mask (`RegisterWordFilter.MaskAt`).

The second procedure maps the row to the truncated weights
`NegativeWeights.nonnegative`: a record with a clear sign bit is shared; a
record with a set sign bit is replaced by a fresh canonical zero of the same
width (sign clear, magnitude `0`, denominator `1`), whose two words are built
by one walk over the stored magnitude word. The output representation is
`CanonAt`: a canonical stored rational of the given width with the stated
value.
-/

@[expose] public section

namespace WeightedMIS.RegisterWeightMask

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch WeightedMIS.RegisterFlagKeys WeightedMIS.RegisterWordFilter

variable {p : ℕ}

/-! ## Representations and reference words -/

/-- A canonical stored rational of width `w0` with value `x`. -/
def CanonAt (w0 : ℕ) (h : Heap) (ptr : Ptr) (x : ℚ) : Prop :=
  ∃ y : BinaryRational.Word w0, StoredRational.At h ptr y ∧ y.value = x ∧
    BinaryRational.Canonical y

theorem CanonAt.mono {w0 : ℕ} {h h' : Heap} (he : Extends h h') {ptr : Ptr} {x : ℚ}
    (hx : CanonAt w0 h ptr x) : CanonAt w0 h' ptr x := by
  obtain ⟨y, hy, hv, hc⟩ := hx
  exact ⟨y, hy.mono he, hv, hc⟩

theorem CanonAt.allocated {w0 : ℕ} {h : Heap} {ptr : Ptr} {x : ℚ} (hx : CanonAt w0 h ptr x) :
    ptr < h.length := by
  obtain ⟨y, hy, -⟩ := hx
  exact hy.allocated

/-- The word of value `1` (for positive width). -/
def oneWord : (k : ℕ) → Bits k
  | 0 => .nil
  | k + 1 => .cons (decide (k = 0)) (oneWord k)

theorem oneWord_value : ∀ {k : ℕ}, 0 < k → (oneWord k).value = 1
  | 1, _ => by simp [oneWord, Bits.value]
  | k + 2, _ => by
    have := oneWord_value (k := k + 1) (by omega)
    simpa [oneWord, Bits.value] using this

/-- The sign test of a word with positive denominator. -/
theorem nonneg_iff {k : ℕ} (x : BinaryRational.Word k) (hd : 0 < x.denominator.value) :
    decide (0 ≤ x.value) = (!x.negative || decide (x.magnitude.value = 0)) := by
  have hd' : (0 : ℚ) < x.denominator.value := by exact_mod_cast hd
  unfold BinaryRational.Word.value BinaryRational.Word.numerator
  cases hn : x.negative
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_or, decide_eq_true_eq]
    push_cast
    exact div_nonneg (by positivity) hd'.le
  · simp only [↓reduceIte, Bool.not_true, Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [div_nonneg_iff]
    constructor
    · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · push_cast at h1
        exact_mod_cast (by linarith [(Nat.cast_nonneg x.magnitude.value : (0 : ℚ) ≤ _)] :
          (x.magnitude.value : ℚ) = 0)
      · linarith
    · intro h0
      left
      simp [h0, hd'.le]

/-- A positive denominator forces a positive width. -/
theorem width_pos {k : ℕ} (x : BinaryRational.Word k) (hd : 0 < x.denominator.value) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := Bits.value_lt x.denominator
    simp at this
    omega
  · exact hk

theorem maskAt_allocated {h : Heap} {ptr : Ptr} {bs : List Bool} (hm : MaskAt h ptr bs) :
    ptr < h.length := by
  cases bs with
  | nil => exact (List.getElem?_eq_some_iff.mp hm).1
  | cons b bs =>
    obtain ⟨t, hc, -⟩ := hm
    exact (List.getElem?_eq_some_iff.mp hc).1

/-! ## Zero test of a stored word -/

/-- Argument 0 = word; the result is set when every bit is clear. -/
def zeroTestBody (self : Fin p) : Command p :=
  .load (.register 0) 1 2 3 { CompiledTrie.failCases with
    nil := .ret [.flag true]
    bit := .branch (.register 3) (.ret [.flag false])
      (.call self [.register 1] [4] (.ret [.register 4])) }

def zeroTestBudget (k : ℕ) : ℕ := 19 * k + 13

theorem zeroTest_compiled (code : Code p) (self : Fin p) (hself : code self = zeroTestBody self)
    {h : Heap} {k : ℕ} {ptr : Ptr} {b : Bits k} (hb : BitsAt h ptr b) :
    Within code h (initialRegisters [.pointer ptr]) (code self)
      [.flag (decide (b.value = 0))] h (zeroTestBudget k) := by
  induction hb with
  | nil cell =>
    rw [hself]
    refine (Within.load (c := Cell.nil) (by reg_simp) cell
      (ret_values (by reg_simp [Bits.value]) le_rfl)).mono ?_
    simp [zeroTestBudget]
  | @cons ptr tail n bit bits cell rest ih =>
    rw [hself]
    cases bit
    · refine (Within.load (c := Cell.bit false tail) (by reg_simp) cell
        (Within.branch (b := false) (by reg_simp)
        (call_of (by reg_simp) ih (ret_values (by reg_simp [Bits.value]) le_rfl)))).mono ?_
      simp [zeroTestBudget]; omega
    · refine (Within.load (c := Cell.bit true tail) (by reg_simp) cell
        (Within.branch (b := true) (by reg_simp)
        (ret_values (by reg_simp [Bits.value]) le_rfl))).mono ?_
      simp [zeroTestBudget]; omega

/-! ## The nonnegativity mask -/

/-- Argument 0 = stored rational; the result is its nonnegativity flag. -/
def testBody (zero : Fin p) : Command p :=
  .load (.register 0) 1 2 15 { CompiledTrie.failCases with
    pair := .load (.register 1) 3 4 5 { CompiledTrie.failCases with
      bit := .branch (.register 5) (.call zero [.register 3] [6] (.ret [.register 6]))
        (.ret [.flag true]) } }

/-- Argument 0 = row; the result is the mask of nonnegativity flags. -/
def maskBody (self test : Fin p) : Command p :=
  .load (.register 0) 1 2 15 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := .call self [.register 2] [3]
      (.call test [.register 1] [4]
        (.allocate 5 (.bit (.register 4) (.register 3)) (.ret [.register 5]))) }

def testBudget (k : ℕ) : ℕ := zeroTestBudget k + 30

def maskBudget (k n : ℕ) : ℕ := (testBudget k + 30) * n + 13

theorem test_compiled (code : Code p) (self zero : Fin p) (hself : code self = testBody zero)
    (hzero : code zero = zeroTestBody zero) {k : ℕ} {h : Heap} {rp : Ptr}
    {x : BinaryRational.Word k} (hx : StoredRational.At h rp x) :
    Within code h (initialRegisters [.pointer rp]) (code self)
      [.flag (!x.negative || decide (x.magnitude.value = 0))] h (testBudget k) := by
  obtain ⟨sp, np, dp, c0, c1, hn, -⟩ := hx
  have z := zeroTest_compiled code zero hzero hn
  rw [hself]
  cases hneg : x.negative
  · rw [hneg] at c1
    refine (Within.load (c := Cell.pair sp dp) (by reg_simp) c0
      (Within.load (c := Cell.bit false np) (by reg_simp) c1
      (Within.branch (b := false) (by reg_simp)
      (ret_values (by reg_simp) le_rfl)))).mono ?_
    simp [testBudget, zeroTestBudget]
  · rw [hneg] at c1
    refine (Within.load (c := Cell.pair sp dp) (by reg_simp) c0
      (Within.load (c := Cell.bit true np) (by reg_simp) c1
      (Within.branch (b := true) (by reg_simp)
      (call_of (by reg_simp) z (ret_values (by reg_simp) le_rfl))))).mono ?_
    simp [testBudget]; omega

theorem mask_compiled (code : Code p) (self test zero : Fin p) (hself : code self = maskBody self test)
    (htest : code test = testBody zero) (hzero : code zero = zeroTestBody zero) {k : ℕ}
    {h : Heap} (hh : Valid h) {rp : Ptr} {xs : List (BinaryRational.Word k)}
    (hr : RegisterRationalRow.RowAt h rp xs) (hd : ∀ x ∈ xs, 0 < x.denominator.value) :
    ∃ out q, Extends h out ∧ Valid out ∧ MaskAt out q (xs.map fun x => decide (0 ≤ x.value)) ∧
      Within code h (initialRegisters [.pointer rp]) (code self) [.pointer q] out
        (maskBudget k xs.length) := by
  induction xs generalizing h rp with
  | nil =>
    obtain ⟨ptrs, hl, hrel⟩ := hr
    cases hrel
    cases hl with
    | nil cell =>
      refine ⟨h, 0, .refl h, hh, hh.1, ?_⟩
      rw [hself]
      refine (Within.load (c := Cell.nil) (by reg_simp) cell
        (ret_values (by reg_simp) le_rfl)).mono ?_
      simp [maskBudget]
  | cons x xs ih =>
    obtain ⟨ptrs, hl, hrel⟩ := hr
    cases hrel with
    | @cons xp _ ps _ hx hxs =>
    cases hl with
    | @cons _ _ rest _ cell hrest =>
    obtain ⟨mid, mp, he, hv, hmp, hw⟩ := ih hh ⟨ps, hrest, hxs⟩
      (fun y hy => hd y (List.mem_cons_of_mem x hy))
    have ht := test_compiled code test zero htest hzero (hx.mono he)
    rw [← nonneg_iff x (hd x List.mem_cons_self)] at ht
    have hs := safe_allocate mid hv (.bit (decide (0 ≤ x.value)) mp) (by
      intro q hq
      simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      exact maskAt_allocated hmp)
    have hext := hs.1
    have hnew : (mid ++ [Cell.bit (decide (0 ≤ x.value)) mp])[mid.length]? =
        some (Cell.bit (decide (0 ≤ x.value)) mp) := by
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp
    refine ⟨_, mid.length, he.trans hext, hs.2.1, ⟨mp, hnew, MaskAt.mono hext hmp⟩, ?_⟩
    rw [hself]
    refine (Within.load (c := Cell.cons xp rest) (by reg_simp) cell
      (call_of (by reg_simp) hw
      (call_of (by reg_simp) ht
      (Within.allocate (c := Cell.bit (decide (0 ≤ x.value)) mp) (by reg_simp)
      (ret_values (by reg_simp) le_rfl))))).mono ?_
    simp [maskBudget, CellExpr.args]; ring_nf; omega

/-! ## Zero and one words of a given width -/

/-- Argument 0 = word of width `k`; results are the zero word and the one word
of width `k` (both ending in the input's terminal cell) and the flag `k = 0`. -/
def zeroOneBody (self : Fin p) : Command p :=
  .load (.register 0) 1 2 3 { CompiledTrie.failCases with
    nil := .ret [.register 0, .register 0, .flag true]
    bit := .call self [.register 1] [4, 5, 6]
      (.allocate 7 (.bit (.flag false) (.register 4))
        (.allocate 8 (.bit (.register 6) (.register 5))
          (.ret [.register 7, .register 8, .flag false]))) }

def zeroOneBudget (k : ℕ) : ℕ := 40 * k + 17

theorem zeroOne_compiled (code : Code p) (self : Fin p) (hself : code self = zeroOneBody self)
    {h : Heap} (hh : Valid h) {k : ℕ} {ptr : Ptr} {b : Bits k} (hb : BitsAt h ptr b) :
    ∃ out zp op, Extends h out ∧ Valid out ∧ BitsAt out zp (Bits.zero k) ∧
      BitsAt out op (oneWord k) ∧
      Within code h (initialRegisters [.pointer ptr]) (code self)
        [.pointer zp, .pointer op, .flag (decide (k = 0))] out (zeroOneBudget k) := by
  induction hb with
  | nil cell =>
    refine ⟨h, _, _, .refl h, hh, .nil cell, .nil cell, ?_⟩
    rw [hself]
    refine (Within.load (c := Cell.nil) (by reg_simp) cell
      (ret_values (by reg_simp) le_rfl)).mono ?_
    simp [zeroOneBudget]
  | @cons ptr tail n bit bits cell rest ih =>
    obtain ⟨mid, zp, op, he, hv, hz, ho, hw⟩ := ih
    obtain ⟨e1, v1, b1⟩ := alloc_bit hv false hz
    obtain ⟨e2, v2, b2⟩ := alloc_bit v1 (decide (n = 0)) (ho.mono e1)
    refine ⟨_, _, _, (he.trans e1).trans e2, v2, b1.mono e2, b2, ?_⟩
    rw [hself]
    refine (Within.load (c := Cell.bit bit tail) (by reg_simp) cell
      (call_of (by reg_simp) hw
      (Within.allocate (c := Cell.bit false zp) (by reg_simp)
      (Within.allocate (c := Cell.bit (decide (n = 0)) op) (by reg_simp)
      (ret_values (by reg_simp) le_rfl))))).mono ?_
    simp [zeroOneBudget, CellExpr.args]; omega

/-! ## Truncation -/

/-- Arguments 0 = stored rational, 1 = unused; the result is the stored
truncated rational (shared when the sign bit is clear). -/
def truncItemBody (zeroOne : Fin p) : Command p :=
  .load (.register 0) 1 2 15 { CompiledTrie.failCases with
    pair := .load (.register 1) 3 4 5 { CompiledTrie.failCases with
      bit := .branch (.register 5)
        (.call zeroOne [.register 3] [6, 7, 8]
          (.allocate 9 (.bit (.flag false) (.register 6))
            (.allocate 10 (.pair (.register 9) (.register 7)) (.ret [.register 10]))))
        (.ret [.register 0]) } }

def truncItemBudget (k : ℕ) : ℕ := zeroOneBudget k + 50

def truncBudget (k n : ℕ) : ℕ := (truncItemBudget k + 35) * n + 13

theorem truncItem_compiled (code : Code p) (self zeroOne : Fin p)
    (hself : code self = truncItemBody zeroOne) (hzo : code zeroOne = zeroOneBody zeroOne)
    {k : ℕ} {h : Heap} (hh : Valid h) {rp dp : Ptr} {x : BinaryRational.Word k}
    (hx : StoredRational.At h rp x) (hc : BinaryRational.Canonical x) :
    ∃ out q, Extends h out ∧ Valid out ∧ CanonAt k out q (max x.value 0) ∧
      Within code h (initialRegisters [.pointer rp, .pointer dp]) (code self) [.pointer q] out
        (truncItemBudget k) := by
  have hd' : (0 : ℚ) < x.denominator.value := by exact_mod_cast hc.1
  obtain ⟨sp, np, dp', c0, c1, hn, hdn⟩ := hx
  rw [hself]
  cases hneg : x.negative
  · rw [hneg] at c1
    have hv : 0 ≤ x.value := by
      unfold BinaryRational.Word.value BinaryRational.Word.numerator
      rw [hneg]
      exact div_nonneg (by simp) hd'.le
    refine ⟨h, rp, .refl h, hh, ⟨x, ⟨sp, np, dp', c0, by rw [hneg]; exact c1, hn, hdn⟩,
      (max_eq_left hv).symm, hc⟩, ?_⟩
    refine (Within.load (c := Cell.pair sp dp') (by reg_simp) c0
      (Within.load (c := Cell.bit false np) (by reg_simp) c1
      (Within.branch (b := false) (by reg_simp)
      (ret_values (by reg_simp) le_rfl)))).mono ?_
    simp [truncItemBudget, zeroOneBudget]
  · rw [hneg] at c1
    have hv : x.value ≤ 0 := by
      unfold BinaryRational.Word.value BinaryRational.Word.numerator
      rw [hneg]
      exact div_nonpos_of_nonpos_of_nonneg (by simp) hd'.le
    have hk := width_pos x hc.1
    obtain ⟨o1, zp, op, e1, v1, hz, ho, w1⟩ := zeroOne_compiled code zeroOne hzo hh hn
    obtain ⟨e2, v2, b2⟩ := alloc_bit v1 false hz
    obtain ⟨e3, v3, c3⟩ := alloc_pair v2 (by simp : o1.length < (o1 ++ [Cell.bit false zp]).length) (lt_of_lt_of_le ho.allocated e2.length_le)
    let y : BinaryRational.Word k := ⟨false, Bits.zero k, oneWord k⟩
    have hy : y.value = 0 := by
      simp [y, BinaryRational.Word.value, BinaryRational.Word.numerator]
    have hyc : BinaryRational.Canonical y := by
      refine ⟨by simp [y, oneWord_value hk], ?_, ?_⟩
      · rw [hy]; simp [y]
      · rw [hy]; simp [y, oneWord_value hk]
    refine ⟨_, _, (e1.trans e2).trans e3, v3,
      ⟨y, ⟨o1.length, zp, op, c3, e3.lookup ?_, (hz.mono e2).mono e3, (ho.mono e2).mono e3⟩,
        by rw [hy, max_eq_right hv], hyc⟩, ?_⟩
    · simp [y]
    refine (Within.load (c := Cell.pair sp dp') (by reg_simp) c0
      (Within.load (c := Cell.bit true np) (by reg_simp) c1
      (Within.branch (b := true) (by reg_simp)
      (call_of (by reg_simp) w1
      (Within.allocate (c := Cell.bit false zp) (by reg_simp)
      (Within.allocate (c := Cell.pair o1.length op) (by reg_simp)
      (ret_values (by reg_simp) le_rfl))))))).mono ?_
    simp [truncItemBudget, CellExpr.args]; omega

structure Procedures (p : ℕ) where
  mask : Fin p
  test : Fin p
  zero : Fin p
  trunc : Fin p
  truncItem : Fin p
  zeroOne : Fin p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.mask = maskBody ids.mask ids.test ∧
  code ids.test = testBody ids.zero ∧
  code ids.zero = zeroTestBody ids.zero ∧
  code ids.trunc = RegisterListMap.body ids.trunc ids.truncItem ∧
  code ids.truncItem = truncItemBody ids.zeroOne ∧
  code ids.zeroOne = zeroOneBody ids.zeroOne

/-- The nonnegativity mask of a stored canonical weight row. -/
theorem weightMask_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {k n : ℕ} (weights : Fin n → ℚ) (q : Fin n → BinaryRational.Word k)
    (hq : ∀ v, BinaryRational.Canonical (q v)) (hval : ∀ v, (q v).value = weights v)
    {h : Heap} (hh : Valid h) {rp : Ptr}
    (hr : RegisterRationalRow.RowAt h rp ((List.finRange n).map q)) :
    ∃ out mp, Extends h out ∧ Valid out ∧
      MaskAt out mp (List.ofFn fun v => decide (0 ≤ weights v)) ∧
      Within code h (initialRegisters [.pointer rp]) (code ids.mask) [.pointer mp] out
        (maskBudget k n) := by
  obtain ⟨hmask, htest, hzero, -⟩ := hm
  obtain ⟨out, mp, he, hv, hmp, hw⟩ := mask_compiled code ids.mask ids.test ids.zero hmask htest
    hzero hh hr (by
      intro x hx
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
      exact (hq v).1)
  refine ⟨out, mp, he, hv, ?_, by simpa using hw⟩
  rw [List.map_map] at hmp
  rw [List.ofFn_eq_map]
  convert hmp using 2
  funext v
  simp [hval]

/-- The stored truncated weights of a stored canonical weight row. -/
theorem truncate_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {k n : ℕ} (weights : Fin n → ℚ) (q : Fin n → BinaryRational.Word k)
    (hq : ∀ v, BinaryRational.Canonical (q v)) (hval : ∀ v, (q v).value = weights v)
    {h : Heap} (hh : Valid h) {rp : Ptr}
    (hr : RegisterRationalRow.RowAt h rp ((List.finRange n).map q)) :
    ∃ out tp, Extends h out ∧ Valid out ∧
      ListRep (CanonAt k) out tp (List.ofFn (NegativeWeights.nonnegative weights)) ∧
      Within code h (initialRegisters [.pointer rp, .pointer 0]) (code ids.trunc) [.pointer tp]
        out (truncBudget k n) := by
  obtain ⟨-, -, -, htrunc, hitem, hzo⟩ := hm
  obtain ⟨out, tp, he, hv, htp, hw⟩ := RegisterListMap.compiled_const code ids.trunc
    ids.truncItem htrunc (fun h p (x : BinaryRational.Word k) => StoredRational.At h p x)
    (fun _ _ (_ : Unit) => True) (CanonAt k) (fun he _ _ hx => hx.mono he)
    (fun _ _ _ _ => trivial) (fun he _ _ hx => hx.mono he) (fun _ hx => hx.allocated)
    (fun _ x => max x.value 0) (truncItemBudget k) (data := ()) (dataPtr := 0) hh hr trivial
    (fun hv _ x hmem hx _ => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hmem
      exact truncItem_compiled code ids.truncItem ids.zeroOne hitem hzo hv hx (hq v))
  refine ⟨out, tp, he, hv, ?_, by simpa [truncBudget] using hw⟩
  rw [List.map_map] at htp
  rw [List.ofFn_eq_map]
  convert htp using 2
  funext v
  simp [NegativeWeights.nonnegative, hval]

end WeightedMIS.RegisterWeightMask
