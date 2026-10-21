module

public import WeightedMIS.ExpandedParameterValues
public import WeightedMIS.RegisterSubtractor
public import WeightedMIS.RegisterWordArithmetic
public import WeightedMIS.RegisterListFold

/-!
# Scalar parameters of the expanded search graph at a working width

All words of this file have one working width `G` and are described as
`ExpandedParameters.word G v`, the residue of `v` modulo `2^G`. The first
procedure computes `1`, `4m+1`, `2r+1`, `2r+2m+2` and the cost sum from the
stored row-count word, the stored cost list (whose length is `m`) and the zero
word of width `G`. The second computes `(4m+1)^d` by one multiplication per
item of a list of length `d`, the block size, the node count, the cost-width
product, the word `2` and the start index `(4m+1)^d - 1`.
-/

@[expose] public section

namespace WeightedMIS.RegisterExpandedParameters

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.ExpandedParameters

variable {p : ℕ}

/-- Procedure identifiers of the parameter computation and its libraries. -/
structure Procedures (p : ℕ) where
  parameters : Fin p
  scalars : Fin p
  counts : Fin p
  vertex : Fin p
  countFold : Fin p
  countItem : Fin p
  sumFold : Fin p
  sumItem : Fin p
  powFold : Fin p
  powItem : Fin p
  shapeMap : Fin p
  constItem : Fin p
  strip : Fin p
  zero : Fin p
  add : Fin p
  mul : Fin p
  mulAcc : Fin p
  shift : Fin p
  snoc : Fin p
  sub : Fin p
  complement : Fin p
  resize : RegisterResize.Procedures p

/-- Arguments: item, zero word, counter. Result: counter plus one. -/
def countItemBody (ids : Procedures p) : Command p :=
  .call ids.add [.register 2, .register 1, .flag true] [3, 15] (.ret [.register 3])

/-- Arguments: cost word, zero word of width `G`, sum. Result: the sum plus
the cost resized to width `G`. -/
def sumItemBody (ids : Procedures p) : Command p :=
  .call ids.resize.resize [.register 0, .register 1] [3]
    (.call ids.add [.register 2, .register 3, .flag false] [4, 15] (.ret [.register 4]))

/-- Arguments: item, base, power. Result: power times base. -/
def powItemBody (ids : Procedures p) : Command p :=
  .call ids.mul [.register 2, .register 1] [3] (.ret [.register 3])

/-- Arguments: item, data. Result: the data pointer. -/
def constItemBody : Command p := .ret [.register 1]

/-- Arguments: row-count word, cost list, zero word of width `G`. Results:
`1`, `4m+1`, `2r+1`, `2r+2m+2` and the cost sum. -/
def scalarsBody (ids : Procedures p) : Command p :=
  .call ids.resize.resize [.register 0, .register 2] [3]
  (.call ids.countFold [.register 1, .register 2, .register 2] [4]
  (.call ids.add [.register 2, .register 2, .flag true] [5, 15]
  (.call ids.add [.register 4, .register 4, .flag false] [6, 15]
  (.call ids.add [.register 6, .register 6, .flag true] [6, 15]
  (.call ids.add [.register 3, .register 3, .flag true] [7, 15]
  (.call ids.add [.register 3, .register 4, .flag true] [8, 15]
  (.call ids.add [.register 8, .register 8, .flag false] [8, 15]
  (.call ids.sumFold [.register 1, .register 2, .register 2] [9]
  (.ret [.register 5, .register 6, .register 7, .register 8, .register 9])))))))))

/-- Arguments: dimension list, `1`, base, states, factor, cost sum, zero word.
Results: power, block, node count, cost-width product, `2`, start index. -/
def countsBody (ids : Procedures p) : Command p :=
  .call ids.powFold [.register 0, .register 2, .register 1] [7]
  (.call ids.add [.register 7, .register 7, .flag false] [8, 15]
  (.call ids.mul [.register 3, .register 3] [9]
  (.call ids.add [.register 9, .register 6, .flag true] [9, 15]
  (.call ids.mul [.register 8, .register 9] [9]
  (.call ids.mul [.register 9, .register 4] [10]
  (.call ids.add [.register 1, .register 1, .flag false] [11, 15]
  (.call ids.add [.register 10, .register 11, .flag false] [10, 15]
  (.call ids.mul [.register 10, .register 5] [10]
  (.call ids.sub [.register 7, .register 1] [12, 15]
  (.ret [.register 7, .register 8, .register 9, .register 10, .register 11,
    .register 12]))))))))))

/-- The library and scalar bodies used in this file. -/
def Procedures.ScalarMatches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.scalars = scalarsBody ids ∧
  code ids.counts = countsBody ids ∧
  code ids.countFold = RegisterListFold.body ids.countFold ids.countItem ∧
  code ids.countItem = countItemBody ids ∧
  code ids.sumFold = RegisterListFold.body ids.sumFold ids.sumItem ∧
  code ids.sumItem = sumItemBody ids ∧
  code ids.powFold = RegisterListFold.body ids.powFold ids.powItem ∧
  code ids.powItem = powItemBody ids ∧
  code ids.zero = RegisterZero.zeroBody ids.zero ∧
  code ids.add = RegisterAdder.adderBody ids.add ∧
  code ids.mul = RegisterMultiplier.multiplyBody ids.zero ids.mulAcc ∧
  code ids.mulAcc = RegisterMultiplier.multiplyAccBody ids.mulAcc ids.shift ids.add ∧
  code ids.shift = RegisterShift.shiftInBody ids.snoc ∧
  code ids.snoc = RegisterShift.snocBody ids.snoc ∧
  code ids.sub = RegisterSubtractor.subtractorBody ids.complement ids.add ∧
  code ids.complement = RegisterComplement.complementBody ids.complement ∧
  ids.resize.Matches code

def addBudget (G : ℕ) : ℕ := 110 * G + 30

def mulBudget (G : ℕ) : ℕ := (136 * G + 80) * G + 24 * G + 39

def subBudget (G : ℕ) : ℕ := 137 * G + 58

/-- Addition with an arbitrary incoming carry. -/
theorem addCarry_compiled (code : Code p) (add : Fin p)
    (body : code add = RegisterAdder.adderBody add)
    {h : Heap} (hh : Valid h) {ap bp : Ptr} {n : ℕ} {a b : Bits n}
    (ha : BitsAt h ap a) (hb : BitsAt h bp b) (c : Bool) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out result (Bits.addCarry a b c).1 ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp, .flag c]) (code add)
        [.pointer result, .flag (Bits.addCarry a b c).2.1] out (addBudget n) := by
  let output := addCarryPointer n ap bp c h
  have safe := addCarryPointer_refines hh ha hb c
  have eval := addCarryPointer_eval hh ha hb c
  have run := RegisterAdder.compiled code add body eval
  change Within code h (initialRegisters [.pointer ap, .pointer bp, .flag c]) (code add)
    [.pointer output.value.1, .flag output.value.2] output.heap (10 * output.trace.length) at run
  have len : output.trace.length = 11 * n + 3 := safe.2.2.2
  have bit : output.value.2 = (Bits.addCarry a b c).2.1 := safe.2.2.1
  rw [len, bit] at run
  exact ⟨output.heap, output.value.1, safe.1.1, safe.1.2.1, safe.2.1,
    run.mono (by unfold addBudget; omega)⟩

theorem add_word_compiled (code : Code p) (add : Fin p)
    (body : code add = RegisterAdder.adderBody add)
    {h : Heap} (hh : Valid h) {ap bp : Ptr} {G a b v : ℕ}
    (ha : BitsAt h ap (word G a)) (hb : BitsAt h bp (word G b)) (c : Bool)
    (hv : a + b + (if c then 1 else 0) = v) :
    ∃ out q f, Extends h out ∧ Valid out ∧ BitsAt out q (word G v) ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp, .flag c]) (code add)
        [.pointer q, .flag f] out (addBudget G) := by
  obtain ⟨out, q, he, hv', hq, run⟩ := addCarry_compiled code add body hh ha hb c
  rw [addCarry_word, hv] at hq
  exact ⟨out, q, _, he, hv', hq, run⟩

theorem mul_word_compiled (code : Code p) (ids : Procedures p) (hc : ids.ScalarMatches code)
    {h : Heap} (hh : Valid h) {ap bp : Ptr} {G a b v : ℕ}
    (ha : BitsAt h ap (word G a)) (hb : BitsAt h bp (word G b)) (hv : a * b = v) :
    ∃ out q, Extends h out ∧ Valid out ∧ BitsAt out q (word G v) ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp]) (code ids.mul)
        [.pointer q] out (mulBudget G) := by
  obtain ⟨-, -, -, -, -, -, -, -, hz, hadd, hmul, hacc, hshift, hsnoc, -⟩ := hc
  obtain ⟨out, q, he, hv', hq, run⟩ := RegisterMultiplier.multiply_compiled code ids.zero
    ids.mulAcc ids.shift ids.snoc ids.add hz hacc hshift hsnoc hadd hh ha hb
  rw [multiply_word, hv] at hq
  rw [← hmul] at run
  exact ⟨out, q, he, hv', hq, run⟩

theorem sub_word_compiled (code : Code p) (ids : Procedures p) (hc : ids.ScalarMatches code)
    {h : Heap} (hh : Valid h) {ap bp : Ptr} {G a : ℕ}
    (ha : BitsAt h ap (word G a)) (hb : BitsAt h bp (word G 1))
    (h1 : 1 ≤ a) (hlt : a < 2 ^ G) (hG : 1 < 2 ^ G) :
    ∃ out q f, Extends h out ∧ Valid out ∧ BitsAt out q (word G (a - 1)) ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp]) (code ids.sub)
        [.pointer q, .flag f] out (subBudget G) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hadd, -, -, -, -, hsub, hcomp, -⟩ := hc
  obtain ⟨out, q, he, hv', hq, run⟩ :=
    RegisterSubtractor.compiled code ids.complement ids.add hcomp hadd hh ha hb
  rw [subtract_word h1 hlt hG] at hq
  rw [← hsub] at run
  exact ⟨out, q, _, he, hv', hq, run⟩

/-! ## Folds -/

def countStep (zero acc : Bits G) {wc : ℕ} (_ : Bits wc) : Bits G := (Bits.addCarry acc zero true).1

theorem countStep_foldl {G wc : ℕ} (xs : List (Bits wc)) (a : ℕ) :
    xs.foldl (fun acc x => countStep (word G 0) acc x) (word G a) = word G (a + xs.length) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, countStep, addCarry_word]
    simpa [Nat.add_assoc, Nat.add_comm 1] using ih (a + 0 + 1)

def countFoldBudget (G m : ℕ) : ℕ := (addBudget G + 40) * m + 15

theorem countFold_compiled (code : Code p) (ids : Procedures p) (hc : ids.ScalarMatches code)
    {h : Heap} (hh : Valid h) {cp zp : Ptr} {G wc : ℕ} {costs : List (Bits wc)}
    (hcs : WordsAt h cp costs) (hz : BitsAt h zp (Bits.zero G)) :
    ∃ out q, Extends h out ∧ Valid out ∧ BitsAt out q (word G costs.length) ∧
      Within code h (initialRegisters [.pointer cp, .pointer zp, .pointer zp])
        (code ids.countFold) [.pointer q] out (countFoldBudget G costs.length) := by
  obtain ⟨-, -, hfold, hitem, -, -, -, -, -, hadd, -⟩ := hc
  obtain ⟨out, q, he, hv, hq, run⟩ := RegisterListFold.compiled_const code ids.countFold
    ids.countItem hfold (fun h p (x : Bits wc) => BitsAt h p x)
    (fun h p (z : Bits G) => BitsAt h p z) (fun h p (s : Bits G) => BitsAt h p s)
    (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he)
    (fun zero acc x => countStep zero acc x) (addBudget G + 10) hh hcs hz hz
    (fun pre x post _ h' hv' xp sp _ hd hs => by
      obtain ⟨out, q, he, hv'', hq, run⟩ := addCarry_compiled code ids.add hadd hv' hs hd true
      refine ⟨out, q, he, hv'', hq, ?_⟩
      let regs := initialRegisters [Value.pointer xp, .pointer zp, .pointer sp]
      let r1 := bindResults regs [3, 15] [Value.pointer q,
        .flag (Bits.addCarry (pre.foldl (fun acc x => countStep (Bits.zero G) acc x) (Bits.zero G))
          (Bits.zero G) true).2.1]
      have last : Within code out r1 (.ret [.register 3]) [.pointer q] out 3 := by
        simpa [r1, values, Atom.eval, bindResults] using Within.ret code out r1 [.register 3]
      have hargs : values regs [.register 2, .register 1, .flag true] =
          [.pointer sp, .pointer zp, .flag true] := by
        simp [regs, values, Atom.eval, initialRegisters]
      have call := Within.call (procedure := ids.add) (regs := regs)
        (arguments := [.register 2, .register 1, .flag true]) (results := [3, 15])
        (by simpa only [hargs] using run) last
      rw [hitem]
      exact call.mono (by simp; omega))
  refine ⟨out, q, he, hv, ?_, run.mono (Nat.le_of_eq (by unfold countFoldBudget; ring))⟩
  rw [zero_eq_word] at hq
  rwa [countStep_foldl, Nat.zero_add] at hq

def sumStep (_zero acc : Bits G) {wc : ℕ} (x : Bits wc) : Bits G :=
  (Bits.add acc (Bits.resizeTo G x)).1

theorem sumStep_foldl {G wc : ℕ} (xs : List (Bits wc)) (a : ℕ) :
    xs.foldl (fun acc x => sumStep (Bits.zero G) acc x) (word G a) =
      word G (a + (xs.map Bits.value).sum) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, sumStep, resizeTo_eq_word, add_word, ih]
    simp [Nat.add_assoc]

def sumFoldBudget (G wc m : ℕ) : ℕ :=
  (RegisterResize.resizeBudget G wc + addBudget G + 50) * m + 15

theorem sumFold_compiled (code : Code p) (ids : Procedures p) (hc : ids.ScalarMatches code)
    {h : Heap} (hh : Valid h) {cp zp : Ptr} {G wc : ℕ} {costs : List (Bits wc)}
    (hcs : WordsAt h cp costs) (hz : BitsAt h zp (Bits.zero G)) :
    ∃ out q, Extends h out ∧ Valid out ∧ BitsAt out q (word G (costs.map Bits.value).sum) ∧
      Within code h (initialRegisters [.pointer cp, .pointer zp, .pointer zp])
        (code ids.sumFold) [.pointer q] out (sumFoldBudget G wc costs.length) := by
  obtain ⟨-, -, -, -, hfold, hitem, -, -, -, hadd, -, -, -, -, -, -, hres⟩ := hc
  obtain ⟨out, q, he, hv, hq, run⟩ := RegisterListFold.compiled_const code ids.sumFold
    ids.sumItem hfold (fun h p (x : Bits wc) => BitsAt h p x)
    (fun h p (z : Bits G) => BitsAt h p z) (fun h p (s : Bits G) => BitsAt h p s)
    (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he)
    (fun zero acc x => sumStep zero acc x)
    (RegisterResize.resizeBudget G wc + addBudget G + 20) hh hcs hz hz
    (fun pre x post _ h' hv' xp sp hx hd hs => by
      obtain ⟨h1, q1, e1, v1, hq1, run1⟩ := RegisterResize.resize_compiled code ids.resize hres
        hv' hx hd
      obtain ⟨out, q, e2, v2, hq, run2⟩ := addCarry_compiled code ids.add hadd v1 (hs.mono e1)
        hq1 false
      refine ⟨out, q, e1.trans e2, v2, hq, ?_⟩
      let regs := initialRegisters [Value.pointer xp, .pointer zp, .pointer sp]
      let r1 := bindResults regs [3] [Value.pointer q1]
      let r2 := bindResults r1 [4, 15] [Value.pointer q,
        .flag (Bits.addCarry (pre.foldl (fun acc x => sumStep (Bits.zero G) acc x) (Bits.zero G))
          (Bits.resizeTo G x) false).2.1]
      have last : Within code out r2 (.ret [.register 4]) [.pointer q] out 3 := by
        simpa [r2, values, Atom.eval, bindResults] using Within.ret code out r2 [.register 4]
      have hargs2 : values r1 [.register 2, .register 3, .flag false] =
          [.pointer sp, .pointer q1, .flag false] := by
        simp [r1, regs, bindResults, values, Atom.eval, initialRegisters]
      have call2 := Within.call (procedure := ids.add) (regs := r1)
        (arguments := [.register 2, .register 3, .flag false]) (results := [4, 15])
        (by simpa only [hargs2] using run2) last
      have hargs1 : values regs [.register 0, .register 1] = [.pointer xp, .pointer zp] := by
        simp [regs, values, Atom.eval, initialRegisters]
      have call1 := Within.call (procedure := ids.resize.resize) (regs := regs)
        (arguments := [.register 0, .register 1]) (results := [3])
        (by simpa only [hargs1] using run1) call2
      rw [hitem]
      exact call1.mono (by simp; omega))
  refine ⟨out, q, he, hv, ?_, run.mono (Nat.le_of_eq (by unfold sumFoldBudget; ring))⟩
  have hf := sumStep_foldl (G := G) costs 0
  rw [← zero_eq_word, Nat.zero_add] at hf
  rwa [hf] at hq

def powStep (base acc : Bits G) (_ : Ptr) : Bits G := (Bits.multiply acc base).1

theorem powStep_foldl {G : ℕ} (B : ℕ) (xs : List Ptr) (a : ℕ) :
    xs.foldl (fun acc x => powStep (word G B) acc x) (word G a) = word G (a * B ^ xs.length) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, powStep, multiply_word, ih]
    simp [pow_succ, Nat.mul_assoc, Nat.mul_comm B]

def powFoldBudget (G d : ℕ) : ℕ := (mulBudget G + 40) * d + 15

theorem powFold_compiled (code : Code p) (ids : Procedures p) (hc : ids.ScalarMatches code)
    {h : Heap} (hh : Valid h) {dp bp op : Ptr} {G B : ℕ} {dims : List Ptr}
    (hd : ListAt h dp dims) (hb : BitsAt h bp (word G B)) (ho : BitsAt h op (word G 1)) :
    ∃ out q, Extends h out ∧ Valid out ∧ BitsAt out q (word G (B ^ dims.length)) ∧
      Within code h (initialRegisters [.pointer dp, .pointer bp, .pointer op])
        (code ids.powFold) [.pointer q] out (powFoldBudget G dims.length) := by
  have hc' := hc
  obtain ⟨-, -, -, -, -, -, hfold, hitem, -⟩ := hc
  have hl : ListRep (fun _ p (x : Ptr) => p = x) h dp dims :=
    ⟨dims, hd, List.forall₂_same.mpr (fun _ _ => rfl)⟩
  obtain ⟨out, q, he, hv, hq, run⟩ := RegisterListFold.compiled_const code ids.powFold
    ids.powItem hfold (fun _ p (x : Ptr) => p = x)
    (fun h p (z : Bits G) => BitsAt h p z) (fun h p (s : Bits G) => BitsAt h p s)
    (fun _ _ _ hx => hx) (fun he _ _ hx => hx.mono he)
    (fun base acc x => powStep base acc x) (mulBudget G + 10) hh hl hb ho
    (fun pre x post _ h' hv' xp sp _ hd' hs => by
      obtain ⟨-, -, -, -, -, -, -, -, hz, hadd, hmul, hacc, hshift, hsnoc, -⟩ := hc'
      obtain ⟨out, q, e1, v1, hq1, run1⟩ := RegisterMultiplier.multiply_compiled code ids.zero
        ids.mulAcc ids.shift ids.snoc ids.add hz hacc hshift hsnoc hadd hv' hs hd'
      rw [← hmul] at run1
      refine ⟨out, q, e1, v1, hq1, ?_⟩
      let regs := initialRegisters [Value.pointer xp, .pointer bp, .pointer sp]
      let r1 := bindResults regs [3] [Value.pointer q]
      have last : Within code out r1 (.ret [.register 3]) [.pointer q] out 3 := by
        simpa [r1, values, Atom.eval, bindResults] using Within.ret code out r1 [.register 3]
      have hargs : values regs [.register 2, .register 1] = [.pointer sp, .pointer bp] := by
        simp [regs, values, Atom.eval, initialRegisters]
      have call := Within.call (procedure := ids.mul) (regs := regs)
        (arguments := [.register 2, .register 1]) (results := [3])
        (by simpa only [hargs] using run1) last
      rw [hitem]
      exact call.mono (by unfold mulBudget; simp; omega))
  refine ⟨out, q, he, hv, ?_, run.mono (Nat.le_of_eq (by unfold powFoldBudget; ring))⟩
  have hf := powStep_foldl (G := G) B dims 1
  rw [Nat.one_mul] at hf
  rwa [hf] at hq

/-! ## Scalar words -/

def scalarsBudget (G wr wc m : ℕ) : ℕ :=
  RegisterResize.resizeBudget G wr + countFoldBudget G m + 6 * addBudget G +
    sumFoldBudget G wc m + 100

theorem scalars_compiled (code : Code p) (ids : Procedures p) (hc : ids.ScalarMatches code)
    {h : Heap} (hh : Valid h) {rp cp zp : Ptr} {G wr wc : ℕ} {rw : Bits wr}
    {costs : List (Bits wc)}
    (hr : BitsAt h rp rw) (hcs : WordsAt h cp costs) (hz : BitsAt h zp (Bits.zero G)) :
    ∃ out p1 p2 p3 p4 p5, Extends h out ∧ Valid out ∧
      BitsAt out p1 (word G 1) ∧ BitsAt out p2 (word G (4 * costs.length + 1)) ∧
      BitsAt out p3 (word G (2 * rw.value + 1)) ∧
      BitsAt out p4 (word G (2 * rw.value + 2 * costs.length + 2)) ∧
      BitsAt out p5 (word G (costs.map Bits.value).sum) ∧
      Within code h (initialRegisters [.pointer rp, .pointer cp, .pointer zp]) (code ids.scalars)
        [.pointer p1, .pointer p2, .pointer p3, .pointer p4, .pointer p5] out
        (scalarsBudget G wr wc costs.length) := by
  have hc' := hc
  obtain ⟨hbody, -, -, -, -, -, -, -, -, hadd, -, -, -, -, -, -, hres⟩ := hc
  have hz' : BitsAt h zp (word G 0) := by rwa [← zero_eq_word]
  obtain ⟨h1, q3, e1, v1, hq3, run1⟩ := RegisterResize.resize_compiled code ids.resize hres hh hr hz
  rw [resizeTo_eq_word] at hq3
  obtain ⟨h2, q4, e2, v2, hq4, run2⟩ := countFold_compiled code ids hc' v1 (hcs.mono e1) (hz.mono e1)
  have e02 := e1.trans e2
  obtain ⟨h3, q5, f3, e3, v3, hq5, run3⟩ := add_word_compiled code ids.add hadd v2
    (hz'.mono e02) (hz'.mono e02) true (v := 1) rfl
  obtain ⟨h4, q6a, f4, e4, v4, hq6a, run4⟩ := add_word_compiled code ids.add hadd v3
    (hq4.mono e3) (hq4.mono e3) false (v := 2 * costs.length) (by simp; omega)
  obtain ⟨h5, q6, f5, e5, v5, hq6, run5⟩ := add_word_compiled code ids.add hadd v4
    hq6a hq6a true (v := 4 * costs.length + 1) (by simp; omega)
  have e15 := (e2.trans e3).trans (e4.trans e5)
  obtain ⟨h6, q7, f6, e6, v6, hq7, run6⟩ := add_word_compiled code ids.add hadd v5
    (hq3.mono e15) (hq3.mono e15) true (v := 2 * rw.value + 1) (by simp; omega)
  obtain ⟨h7, q8a, f7, e7, v7, hq8a, run7⟩ := add_word_compiled code ids.add hadd v6
    ((hq3.mono e15).mono e6) (((hq4.mono e3).mono (e4.trans e5)).mono e6) true
    (v := rw.value + costs.length + 1) (by simp)
  obtain ⟨h8, q8, f8, e8, v8, hq8, run8⟩ := add_word_compiled code ids.add hadd v7
    hq8a hq8a false (v := 2 * rw.value + 2 * costs.length + 2) (by simp; omega)
  have e08 := e02.trans ((e3.trans (e4.trans e5)).trans (e6.trans (e7.trans e8)))
  obtain ⟨h9, q9, e9, v9, hq9, run9⟩ := sumFold_compiled code ids hc' v8 (hcs.mono e08)
    (hz.mono e08)
  refine ⟨h9, q5, q6, q7, q8, q9, e08.trans e9, v9,
    (hq5.mono ((e4.trans e5).trans (e6.trans (e7.trans e8)))).mono e9,
    (hq6.mono (e6.trans (e7.trans e8))).mono e9, (hq7.mono (e7.trans e8)).mono e9,
    hq8.mono e9, hq9, ?_⟩
  let r0 := initialRegisters [Value.pointer rp, .pointer cp, .pointer zp]
  let r1 := bindResults r0 [3] [Value.pointer q3]
  let r2 := bindResults r1 [4] [Value.pointer q4]
  let r3 := bindResults r2 [5, 15] [Value.pointer q5, .flag f3]
  let r4 := bindResults r3 [6, 15] [Value.pointer q6a, .flag f4]
  let r5 := bindResults r4 [6, 15] [Value.pointer q6, .flag f5]
  let r6 := bindResults r5 [7, 15] [Value.pointer q7, .flag f6]
  let r7 := bindResults r6 [8, 15] [Value.pointer q8a, .flag f7]
  let r8 := bindResults r7 [8, 15] [Value.pointer q8, .flag f8]
  let r9 := bindResults r8 [9] [Value.pointer q9]
  have last : Within code h9 r9 (.ret [.register 5, .register 6, .register 7, .register 8,
      .register 9]) [.pointer q5, .pointer q6, .pointer q7, .pointer q8, .pointer q9] h9 11 := by
    simpa [r9, r8, r7, r6, r5, r4, r3, values, Atom.eval, bindResults] using
      Within.ret code h9 r9 [.register 5, .register 6, .register 7, .register 8, .register 9]
  have a9 : values r8 [.register 1, .register 2, .register 2] =
      [.pointer cp, .pointer zp, .pointer zp] := by
    simp [r8, r7, r6, r5, r4, r3, r2, r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c9 := Within.call (procedure := ids.sumFold) (regs := r8)
    (arguments := [.register 1, .register 2, .register 2]) (results := [9])
    (by simpa only [a9] using run9) last
  have a8 : values r7 [.register 8, .register 8, .flag false] =
      [.pointer q8a, .pointer q8a, .flag false] := by
    simp [r7, values, Atom.eval, bindResults]
  have c8 := Within.call (procedure := ids.add) (regs := r7)
    (arguments := [.register 8, .register 8, .flag false]) (results := [8, 15])
    (by simpa only [a8] using run8) c9
  have a7 : values r6 [.register 3, .register 4, .flag true] =
      [.pointer q3, .pointer q4, .flag true] := by
    simp [r6, r5, r4, r3, r2, r1, values, Atom.eval, bindResults]
  have c7 := Within.call (procedure := ids.add) (regs := r6)
    (arguments := [.register 3, .register 4, .flag true]) (results := [8, 15])
    (by simpa only [a7] using run7) c8
  have a6 : values r5 [.register 3, .register 3, .flag true] =
      [.pointer q3, .pointer q3, .flag true] := by
    simp [r5, r4, r3, r2, r1, values, Atom.eval, bindResults]
  have c6 := Within.call (procedure := ids.add) (regs := r5)
    (arguments := [.register 3, .register 3, .flag true]) (results := [7, 15])
    (by simpa only [a6] using run6) c7
  have a5 : values r4 [.register 6, .register 6, .flag true] =
      [.pointer q6a, .pointer q6a, .flag true] := by
    simp [r4, values, Atom.eval, bindResults]
  have c5 := Within.call (procedure := ids.add) (regs := r4)
    (arguments := [.register 6, .register 6, .flag true]) (results := [6, 15])
    (by simpa only [a5] using run5) c6
  have a4 : values r3 [.register 4, .register 4, .flag false] =
      [.pointer q4, .pointer q4, .flag false] := by
    simp [r3, r2, values, Atom.eval, bindResults]
  have c4 := Within.call (procedure := ids.add) (regs := r3)
    (arguments := [.register 4, .register 4, .flag false]) (results := [6, 15])
    (by simpa only [a4] using run4) c5
  have a3 : values r2 [.register 2, .register 2, .flag true] =
      [.pointer zp, .pointer zp, .flag true] := by
    simp [r2, r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c3 := Within.call (procedure := ids.add) (regs := r2)
    (arguments := [.register 2, .register 2, .flag true]) (results := [5, 15])
    (by simpa only [a3] using run3) c4
  have a2 : values r1 [.register 1, .register 2, .register 2] =
      [.pointer cp, .pointer zp, .pointer zp] := by
    simp [r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c2 := Within.call (procedure := ids.countFold) (regs := r1)
    (arguments := [.register 1, .register 2, .register 2]) (results := [4])
    (by simpa only [a2] using run2) c3
  have a1 : values r0 [.register 0, .register 2] = [.pointer rp, .pointer zp] := by
    simp [r0, values, Atom.eval, initialRegisters]
  have c1 := Within.call (procedure := ids.resize.resize) (regs := r0)
    (arguments := [.register 0, .register 2]) (results := [3])
    (by simpa only [a1] using run1) c2
  rw [hbody]
  exact c1.mono (by simp only [scalarsBudget, List.length_cons, List.length_nil]; omega)

/-! ## Counts -/

def countsBudget (G d : ℕ) : ℕ := powFoldBudget G d + 4 * addBudget G + 4 * mulBudget G +
  subBudget G + 100

theorem counts_compiled (code : Code p) (ids : Procedures p) (hc : ids.ScalarMatches code)
    {h : Heap} (hh : Valid h) {dp op bp sp fp cp zp : Ptr} {G B S F C : ℕ} {dims : List Ptr}
    (hd : ListAt h dp dims) (ho : BitsAt h op (word G 1)) (hb : BitsAt h bp (word G B))
    (hs : BitsAt h sp (word G S)) (hf : BitsAt h fp (word G F)) (hcs : BitsAt h cp (word G C))
    (hz : BitsAt h zp (Bits.zero G))
    (hpos : 1 ≤ B ^ dims.length) (hpow : B ^ dims.length < 2 ^ G) (hG : 1 < 2 ^ G) :
    ∃ out p1 p2 p3 p4 p5 p6, Extends h out ∧ Valid out ∧
      BitsAt out p1 (word G (B ^ dims.length)) ∧
      BitsAt out p2 (word G (2 * B ^ dims.length)) ∧
      BitsAt out p3 (word G (2 * B ^ dims.length * (1 + S ^ 2))) ∧
      BitsAt out p4 (word G ((2 * B ^ dims.length * (1 + S ^ 2) * F + 2) * C)) ∧
      BitsAt out p5 (word G 2) ∧ BitsAt out p6 (word G (B ^ dims.length - 1)) ∧
      Within code h (initialRegisters [.pointer dp, .pointer op, .pointer bp, .pointer sp,
          .pointer fp, .pointer cp, .pointer zp]) (code ids.counts)
        [.pointer p1, .pointer p2, .pointer p3, .pointer p4, .pointer p5, .pointer p6] out
        (countsBudget G dims.length) := by
  have hc' := hc
  obtain ⟨-, hbody, -, -, -, -, -, -, -, hadd, -⟩ := hc
  have hz' : BitsAt h zp (word G 0) := by rwa [← zero_eq_word]
  obtain ⟨h1, q7, e1, v1, hq7, run1⟩ := powFold_compiled code ids hc' hh hd hb ho
  obtain ⟨h2, q8, f2, e2, v2, hq8, run2⟩ := add_word_compiled code ids.add hadd v1
    hq7 hq7 false (v := 2 * B ^ dims.length) (by simp; omega)
  obtain ⟨h3, q9a, e3, v3, hq9a, run3⟩ := mul_word_compiled code ids hc' v2
    ((hs.mono e1).mono e2) ((hs.mono e1).mono e2) (v := S ^ 2) (by ring)
  have e03 := e1.trans (e2.trans e3)
  obtain ⟨h4, q9b, f4, e4, v4, hq9b, run4⟩ := add_word_compiled code ids.add hadd v3
    hq9a (hz'.mono e03) true (v := 1 + S ^ 2) (by simp; omega)
  obtain ⟨h5, q9, e5, v5, hq9, run5⟩ := mul_word_compiled code ids hc' v4
    ((hq8.mono e3).mono e4) hq9b (v := 2 * B ^ dims.length * (1 + S ^ 2)) rfl
  have e05 := e03.trans (e4.trans e5)
  obtain ⟨h6, q10a, e6, v6, hq10a, run6⟩ := mul_word_compiled code ids hc' v5
    hq9 (hf.mono e05) (v := 2 * B ^ dims.length * (1 + S ^ 2) * F) rfl
  obtain ⟨h7, q11, f7, e7, v7, hq11, run7⟩ := add_word_compiled code ids.add hadd v6
    ((ho.mono e05).mono e6) ((ho.mono e05).mono e6) false (v := 2) rfl
  obtain ⟨h8, q10b, f8, e8, v8, hq10b, run8⟩ := add_word_compiled code ids.add hadd v7
    (hq10a.mono e7) hq11 false (v := 2 * B ^ dims.length * (1 + S ^ 2) * F + 2) (by simp)
  have e08 := e05.trans (e6.trans (e7.trans e8))
  obtain ⟨h9, q10, e9, v9, hq10, run9⟩ := mul_word_compiled code ids hc' v8
    hq10b (hcs.mono e08) (v := (2 * B ^ dims.length * (1 + S ^ 2) * F + 2) * C) rfl
  have e19 := (e2.trans e3).trans ((e4.trans e5).trans ((e6.trans (e7.trans e8)).trans e9))
  obtain ⟨h10, q12, f10, e10, v10, hq12, run10⟩ := sub_word_compiled code ids hc' v9
    (hq7.mono e19) ((ho.mono e08).mono e9) hpos hpow hG
  have e610 := (e6.trans (e7.trans e8)).trans (e9.trans e10)
  refine ⟨h10, q7, q8, q9, q10, q11, q12, e1.trans e19 |>.trans e10, v10,
    (hq7.mono e19).mono e10,
    (hq8.mono ((e3.trans (e4.trans e5)).trans e610)),
    hq9.mono e610, hq10.mono e10, (hq11.mono (e8.trans e9)).mono e10, hq12, ?_⟩
  let r0 := initialRegisters [Value.pointer dp, .pointer op, .pointer bp, .pointer sp,
    .pointer fp, .pointer cp, .pointer zp]
  let r1 := bindResults r0 [7] [Value.pointer q7]
  let r2 := bindResults r1 [8, 15] [Value.pointer q8, .flag f2]
  let r3 := bindResults r2 [9] [Value.pointer q9a]
  let r4 := bindResults r3 [9, 15] [Value.pointer q9b, .flag f4]
  let r5 := bindResults r4 [9] [Value.pointer q9]
  let r6 := bindResults r5 [10] [Value.pointer q10a]
  let r7 := bindResults r6 [11, 15] [Value.pointer q11, .flag f7]
  let r8 := bindResults r7 [10, 15] [Value.pointer q10b, .flag f8]
  let r9 := bindResults r8 [10] [Value.pointer q10]
  let r10 := bindResults r9 [12, 15] [Value.pointer q12, .flag f10]
  have last : Within code h10 r10 (.ret [.register 7, .register 8, .register 9, .register 10,
      .register 11, .register 12])
      [.pointer q7, .pointer q8, .pointer q9, .pointer q10, .pointer q11, .pointer q12] h10 13 := by
    simpa [r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, values, Atom.eval, bindResults] using
      Within.ret code h10 r10 [.register 7, .register 8, .register 9, .register 10,
        .register 11, .register 12]
  have a10 : values r9 [.register 7, .register 1] = [.pointer q7, .pointer op] := by
    simp [r9, r8, r7, r6, r5, r4, r3, r2, r1, r0, values, Atom.eval, bindResults,
      initialRegisters]
  have c10 := Within.call (procedure := ids.sub) (regs := r9)
    (arguments := [.register 7, .register 1]) (results := [12, 15])
    (by simpa only [a10] using run10) last
  have a9 : values r8 [.register 10, .register 5] = [.pointer q10b, .pointer cp] := by
    simp [r8, r7, r6, r5, r4, r3, r2, r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c9 := Within.call (procedure := ids.mul) (regs := r8)
    (arguments := [.register 10, .register 5]) (results := [10])
    (by simpa only [a9] using run9) c10
  have a8 : values r7 [.register 10, .register 11, .flag false] =
      [.pointer q10a, .pointer q11, .flag false] := by
    simp [r7, r6, values, Atom.eval, bindResults]
  have c8 := Within.call (procedure := ids.add) (regs := r7)
    (arguments := [.register 10, .register 11, .flag false]) (results := [10, 15])
    (by simpa only [a8] using run8) c9
  have a7 : values r6 [.register 1, .register 1, .flag false] =
      [.pointer op, .pointer op, .flag false] := by
    simp [r6, r5, r4, r3, r2, r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c7 := Within.call (procedure := ids.add) (regs := r6)
    (arguments := [.register 1, .register 1, .flag false]) (results := [11, 15])
    (by simpa only [a7] using run7) c8
  have a6 : values r5 [.register 9, .register 4] = [.pointer q9, .pointer fp] := by
    simp [r5, r4, r3, r2, r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c6 := Within.call (procedure := ids.mul) (regs := r5)
    (arguments := [.register 9, .register 4]) (results := [10])
    (by simpa only [a6] using run6) c7
  have a5 : values r4 [.register 8, .register 9] = [.pointer q8, .pointer q9b] := by
    simp [r4, r3, r2, values, Atom.eval, bindResults]
  have c5 := Within.call (procedure := ids.mul) (regs := r4)
    (arguments := [.register 8, .register 9]) (results := [9])
    (by simpa only [a5] using run5) c6
  have a4 : values r3 [.register 9, .register 6, .flag true] =
      [.pointer q9a, .pointer zp, .flag true] := by
    simp [r3, r2, r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c4 := Within.call (procedure := ids.add) (regs := r3)
    (arguments := [.register 9, .register 6, .flag true]) (results := [9, 15])
    (by simpa only [a4] using run4) c5
  have a3 : values r2 [.register 3, .register 3] = [.pointer sp, .pointer sp] := by
    simp [r2, r1, r0, values, Atom.eval, bindResults, initialRegisters]
  have c3 := Within.call (procedure := ids.mul) (regs := r2)
    (arguments := [.register 3, .register 3]) (results := [9])
    (by simpa only [a3] using run3) c4
  have a2 : values r1 [.register 7, .register 7, .flag false] =
      [.pointer q7, .pointer q7, .flag false] := by
    simp [r1, values, Atom.eval, bindResults]
  have c2 := Within.call (procedure := ids.add) (regs := r1)
    (arguments := [.register 7, .register 7, .flag false]) (results := [8, 15])
    (by simpa only [a2] using run2) c3
  have a1 : values r0 [.register 0, .register 2, .register 1] =
      [.pointer dp, .pointer bp, .pointer op] := by
    simp [r0, values, Atom.eval, initialRegisters]
  have c1 := Within.call (procedure := ids.powFold) (regs := r0)
    (arguments := [.register 0, .register 2, .register 1]) (results := [7])
    (by simpa only [a1] using run1) c2
  rw [hbody]
  exact c1.mono (by simp only [countsBudget, List.length_cons, List.length_nil]; omega)

end WeightedMIS.RegisterExpandedParameters
