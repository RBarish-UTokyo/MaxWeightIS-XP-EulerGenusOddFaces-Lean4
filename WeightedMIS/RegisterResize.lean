module

public import WeightedMIS.RegisterWiden
public import WeightedMIS.RegisterListMap
public import WeightedMIS.WordNodeCodec
public import WeightedMIS.ExpandedCoordinate

/-!
# Resizing binary words to the width of a shape word

`Bits.resizeTo k x` is the word of width `k` holding `x.value mod 2^k`. The
procedure receives the target width as an arbitrary shape word of width `k`.
It first walks the shape and the word in lockstep. If the shape ends first,
the remaining suffix of the word has length `n - k`; walking that suffix and
the word in lockstep again stops at the suffix of length `k`, which is
returned without allocation. If the word ends first, the remaining part of
the shape has length `k - n` and the word is zero-extended by that many bits.
The cost is linear in `k + n`.

Lists of words and signed words with one sign cell are resized item by item.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Bits

open WeightedMIS.SparseSearchGraph

/-- The word of width `k` holding the low `k` bits of `x`. -/
def resizeTo (k : ℕ) {n : ℕ} (x : Bits n) : Bits k := encodeBits k (x.value % 2 ^ k)

@[simp] theorem resizeTo_value (k : ℕ) {n : ℕ} (x : Bits n) :
    (resizeTo k x).value = x.value % 2 ^ k :=
  encodeBits_value _ _ (Nat.mod_lt _ (by positivity))

theorem resizeTo_value_of_lt {k n : ℕ} (x : Bits n) (h : x.value < 2 ^ k) :
    (resizeTo k x).value = x.value := by
  rw [resizeTo_value, Nat.mod_eq_of_lt h]

/-- A word of width `k` is the resized word as soon as its value agrees. -/
theorem eq_resizeTo {k n : ℕ} {y : Bits k} {x : Bits n} (h : y.value = x.value % 2 ^ k) :
    y = resizeTo k x :=
  ScalarNodeCodec.bits_value_injective k (by rw [resizeTo_value, h])

theorem resizeTo_zero (k n : ℕ) : resizeTo k (zero n) = zero k :=
  (eq_resizeTo (by simp)).symm

theorem resizeTo_self {n : ℕ} (x : Bits n) : resizeTo n x = x :=
  (eq_resizeTo (Nat.mod_eq_of_lt (value_lt x)).symm).symm

end WeightedMIS.EfficientSearch.Bits

namespace WeightedMIS.ExpandedWords

/-- Resize the magnitude of a signed word, keeping its sign bit. -/
def SignedWord.resizeTo (k : ℕ) {n : ℕ} (d : SignedWord n) : SignedWord k :=
  ⟨d.negative, d.magnitude.resizeTo k⟩

theorem SignedWord.resizeTo_value {k n : ℕ} (d : SignedWord n)
    (h : d.magnitude.value < 2 ^ k) : (d.resizeTo k).value = d.value := by
  simp [SignedWord.resizeTo, SignedWord.value,
    EfficientSearch.Bits.resizeTo_value_of_lt _ h]

end WeightedMIS.ExpandedWords

namespace WeightedMIS.RegisterResize

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords

variable {p : ℕ}

/-- Second half of one lockstep round: the first word is nonempty. -/
def excessInner (self : Fin p) : Command p :=
  .load (.register 1) 4 15 5 (RegisterAdder.nilBitCases
    (.ret [.flag false, .register 0])
    (.call self [.register 2, .register 4] [6, 7] (.ret [.register 6, .register 7])))

/-- Arguments: two words. Returns `true` and the remaining suffix of the
second word when the first word ends no later, otherwise `false` and the
remaining nonempty suffix of the first word. -/
def excessBody (self : Fin p) : Command p :=
  .load (.register 0) 2 15 3 (RegisterAdder.nilBitCases
    (.ret [.flag true, .register 1]) (excessInner self))

def excessBudget (j : ℕ) : ℕ := 30 * j + 25

theorem excess_compiled (code : Code p) (self : Fin p) (hself : code self = excessBody self)
    {h : Heap} {j : ℕ} {ap : Ptr} {a : Bits j} (ha : BitsAt h ap a) :
    ∀ {n : ℕ} {bp : Ptr} {b : Bits n}, BitsAt h bp b →
      ∃ (flag : Bool) (q : Ptr) (e : ℕ) (y : Bits e), BitsAt h q y ∧
        (if flag then n = j + e else j = n + e) ∧
        Within code h (initialRegisters [.pointer ap, .pointer bp]) (code self)
          [.flag flag, .pointer q] h (excessBudget j) := by
  induction ha with
  | @nil ap cell =>
    intro n bp b hb
    refine ⟨true, bp, n, b, hb, by simp, ?_⟩
    let regs := initialRegisters [Value.pointer ap, .pointer bp]
    have last : Within code h (loadRegisters regs 2 15 3 .nil)
        (.ret [.flag true, .register 1]) [.flag true, .pointer bp] h 5 := by
      simpa [regs, loadRegisters, decoded, initialRegisters, values, Atom.eval] using
        Within.ret code h (loadRegisters regs 2 15 3 .nil) [.flag true, .register 1]
    have load := Within.load (regs := regs) (address := .register 0)
      (first := 2) (second := 15) (bit := 3)
      (branches := RegisterAdder.nilBitCases (.ret [.flag true, .register 1]) (excessInner self))
      (by simp [regs, initialRegisters, Atom.eval]) cell last
    rw [hself]
    exact load.mono (by simp [excessBudget])
  | @cons ap tail j bit t cell rest ih =>
    intro n bp b hb
    let regs := initialRegisters [Value.pointer ap, .pointer bp]
    let first := loadRegisters regs 2 15 3 (.bit bit tail)
    cases hb with
    | @nil _ cellb =>
      refine ⟨false, ap, j + 1, .cons bit t, .cons cell rest, by simp, ?_⟩
      have last : Within code h (loadRegisters first 4 15 5 .nil)
          (.ret [.flag false, .register 0]) [.flag false, .pointer ap] h 5 := by
        simpa [first, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval] using
          Within.ret code h (loadRegisters first 4 15 5 .nil) [.flag false, .register 0]
      have inner := Within.load (regs := first) (address := .register 1)
        (first := 4) (second := 15) (bit := 5)
        (branches := RegisterAdder.nilBitCases (.ret [.flag false, .register 0])
          (.call self [.register 2, .register 4] [6, 7] (.ret [.register 6, .register 7])))
        (by simp [first, regs, loadRegisters, decoded, initialRegisters, Atom.eval]) cellb last
      have load := Within.load (regs := regs) (address := .register 0)
        (first := 2) (second := 15) (bit := 3)
        (branches := RegisterAdder.nilBitCases (.ret [.flag true, .register 1]) (excessInner self))
        (by simp [regs, initialRegisters, Atom.eval]) cell inner
      rw [hself]
      exact load.mono (by simp [excessBudget])
    | @cons _ btail n bb bt cellb restb =>
      obtain ⟨flag, q, e, y, hy, hcond, hrun⟩ := ih restb
      refine ⟨flag, q, e, y, hy, ?_, ?_⟩
      · cases flag <;> simp only [Bool.false_eq_true, ↓reduceIte] at hcond ⊢ <;> omega
      let second := loadRegisters first 4 15 5 (.bit bb btail)
      let ready := bindResults second [6, 7] [Value.flag flag, .pointer q]
      have last : Within code h ready (.ret [.register 6, .register 7])
          [.flag flag, .pointer q] h 5 := by
        simpa [ready, values, Atom.eval, bindResults] using
          Within.ret code h ready [.register 6, .register 7]
      have hargs : values second [.register 2, .register 4] = [.pointer tail, .pointer btail] := by
        simp [second, first, regs, loadRegisters, decoded, values, Atom.eval]
      have call := Within.call (procedure := self) (regs := second)
        (arguments := [.register 2, .register 4]) (results := [6, 7])
        (by simpa only [hargs] using hrun) last
      have inner := Within.load (regs := first) (address := .register 1)
        (first := 4) (second := 15) (bit := 5)
        (branches := RegisterAdder.nilBitCases (.ret [.flag false, .register 0])
          (.call self [.register 2, .register 4] [6, 7] (.ret [.register 6, .register 7])))
        (by simp [first, regs, loadRegisters, decoded, initialRegisters, Atom.eval]) cellb call
      have load := Within.load (regs := regs) (address := .register 0)
        (first := 2) (second := 15) (bit := 3)
        (branches := RegisterAdder.nilBitCases (.ret [.flag true, .register 1]) (excessInner self))
        (by simp [regs, initialRegisters, Atom.eval]) cell inner
      rw [hself]
      exact load.mono (by simp [excessBudget]; omega)

/-- Second half of one trailing round: the leading word is nonempty. -/
def trailInner (self : Fin p) : Command p :=
  .load (.register 1) 4 15 5 (RegisterAdder.nilBitCases .fail
    (.call self [.register 2, .register 4] [6] (.ret [.register 6])))

/-- Arguments: a leading word of length `e` and a word of length `e + k`.
Returns the suffix of the second word of length `k`. -/
def trailBody (self : Fin p) : Command p :=
  .load (.register 0) 2 15 3 (RegisterAdder.nilBitCases (.ret [.register 1]) (trailInner self))

def trailBudget (e : ℕ) : ℕ := 28 * e + 13

/-- Dropping leading bits keeps the value modulo the remaining width. -/
theorem value_cons_mod {n k : ℕ} (b : Bool) (x : Bits n) (hk : k ≤ n) :
    (Bits.cons b x).value % 2 ^ k = x.value % 2 ^ k := by
  obtain ⟨c, hc⟩ := Nat.pow_dvd_pow 2 hk
  simp only [Bits.value]
  cases b
  · simp
  · simp only [↓reduceIte, hc, Nat.mul_add_mod]

theorem trail_compiled (code : Code p) (self : Fin p) (hself : code self = trailBody self)
    {h : Heap} {e : ℕ} {lp : Ptr} {lead : Bits e} (hl : BitsAt h lp lead) (k : ℕ) :
    ∀ {n : ℕ} {xp : Ptr} {x : Bits n}, BitsAt h xp x → n = e + k →
      ∃ (q : Ptr) (y : Bits k), BitsAt h q y ∧ y.value = x.value % 2 ^ k ∧
        Within code h (initialRegisters [.pointer lp, .pointer xp]) (code self)
          [.pointer q] h (trailBudget e) := by
  induction hl with
  | @nil lp cell =>
    intro n xp x hx hn
    obtain rfl : n = k := by omega
    refine ⟨xp, x, hx, (Nat.mod_eq_of_lt (Bits.value_lt x)).symm, ?_⟩
    let regs := initialRegisters [Value.pointer lp, .pointer xp]
    have last : Within code h (loadRegisters regs 2 15 3 .nil)
        (.ret [.register 1]) [.pointer xp] h 3 := by
      simpa [regs, loadRegisters, decoded, initialRegisters, values, Atom.eval] using
        Within.ret code h (loadRegisters regs 2 15 3 .nil) [.register 1]
    have load := Within.load (regs := regs) (address := .register 0)
      (first := 2) (second := 15) (bit := 3)
      (branches := RegisterAdder.nilBitCases (.ret [.register 1]) (trailInner self))
      (by simp [regs, initialRegisters, Atom.eval]) cell last
    rw [hself]
    exact load.mono (by simp [trailBudget])
  | @cons lp tail e bit t cell rest ih =>
    intro n xp x hx hn
    cases hx with
    | nil _ => omega
    | @cons _ xtail n xb xt cellx restx =>
      obtain ⟨q, y, hy, hval, hrun⟩ := ih restx (by omega)
      refine ⟨q, y, hy, by rw [hval, value_cons_mod xb xt (by omega)], ?_⟩
      let regs := initialRegisters [Value.pointer lp, .pointer xp]
      let first := loadRegisters regs 2 15 3 (.bit bit tail)
      let second := loadRegisters first 4 15 5 (.bit xb xtail)
      let ready := bindResults second [6] [Value.pointer q]
      have last : Within code h ready (.ret [.register 6]) [.pointer q] h 3 := by
        simpa [ready, values, Atom.eval, bindResults] using Within.ret code h ready [.register 6]
      have hargs : values second [.register 2, .register 4] = [.pointer tail, .pointer xtail] := by
        simp [second, first, regs, loadRegisters, decoded, values, Atom.eval]
      have call := Within.call (procedure := self) (regs := second)
        (arguments := [.register 2, .register 4]) (results := [6])
        (by simpa only [hargs] using hrun) last
      have inner := Within.load (regs := first) (address := .register 1)
        (first := 4) (second := 15) (bit := 5)
        (branches := RegisterAdder.nilBitCases .fail
          (.call self [.register 2, .register 4] [6] (.ret [.register 6])))
        (by simp [first, regs, loadRegisters, decoded, initialRegisters, Atom.eval]) cellx call
      have load := Within.load (regs := regs) (address := .register 0)
        (first := 2) (second := 15) (bit := 3)
        (branches := RegisterAdder.nilBitCases (.ret [.register 1]) (trailInner self))
        (by simp [regs, initialRegisters, Atom.eval]) cell inner
      rw [hself]
      exact load.mono (by simp [trailBudget]; omega)

/-- Arguments: word, shape word. Result: the word resized to the shape width. -/
def resizeBody (excess trail widen : Fin p) : Command p :=
  .call excess [.register 1, .register 0] [2, 3]
    (.branch (.register 2)
      (.call trail [.register 3, .register 0] [4] (.ret [.register 4]))
      (.call widen [.register 3, .register 0] [4] (.ret [.register 4])))

structure Procedures (p : ℕ) where
  resize : Fin p
  excess : Fin p
  trail : Fin p
  widen : Fin p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.resize = resizeBody ids.excess ids.trail ids.widen ∧
  code ids.excess = excessBody ids.excess ∧
  code ids.trail = trailBody ids.trail ∧
  code ids.widen = RegisterWiden.widenBody ids.widen

def resizeBudget (k n : ℕ) : ℕ := 60 * k + 30 * n + 60

theorem resize_compiled (code : Code p) (ids : Procedures p) (hc : ids.Matches code)
    {h : Heap} (hh : Valid h) {xp sp : Ptr} {n k : ℕ} {x : Bits n} {s : Bits k}
    (hx : BitsAt h xp x) (hs : BitsAt h sp s) :
    ∃ out q, Extends h out ∧ Valid out ∧ BitsAt out q (Bits.resizeTo k x) ∧
      Within code h (initialRegisters [.pointer xp, .pointer sp]) (code ids.resize)
        [.pointer q] out (resizeBudget k n) := by
  obtain ⟨hresize, hexcess, htrail, hwiden⟩ := hc
  obtain ⟨flag, q, e, y, hy, hcond, hrun⟩ := excess_compiled code ids.excess hexcess hs hx
  let regs := initialRegisters [Value.pointer xp, .pointer sp]
  let r1 := bindResults regs [2, 3] [Value.flag flag, .pointer q]
  have hargs : values regs [.register 1, .register 0] = [.pointer sp, .pointer xp] := by
    simp [regs, initialRegisters, values, Atom.eval]
  have hargs2 : values r1 [.register 3, .register 0] = [.pointer q, .pointer xp] := by
    simp [r1, regs, bindResults, initialRegisters, values, Atom.eval]
  rw [hresize]
  cases flag with
  | true =>
    simp only [↓reduceIte] at hcond
    obtain ⟨q', y', hy', hval, trun⟩ := trail_compiled code ids.trail htrail hy k hx (by omega)
    refine ⟨h, q', .refl h, hh, by rw [← Bits.eq_resizeTo hval]; exact hy', ?_⟩
    let r2 := bindResults r1 [4] [Value.pointer q']
    have last : Within code h r2 (.ret [.register 4]) [.pointer q'] h 3 := by
      simpa [r2, values, Atom.eval, bindResults] using Within.ret code h r2 [.register 4]
    have tcall := Within.call (procedure := ids.trail) (regs := r1)
      (arguments := [.register 3, .register 0]) (results := [4])
      (by simpa only [hargs2] using trun) last
    have br := Within.branch (regs := r1) (test := .register 2) (b := true)
      (yes := .call ids.trail [.register 3, .register 0] [4] (.ret [.register 4]))
      (no := .call ids.widen [.register 3, .register 0] [4] (.ret [.register 4]))
      (by simp [r1, bindResults, Atom.eval]) tcall
    have ecall := Within.call (procedure := ids.excess) (regs := regs)
      (arguments := [.register 1, .register 0]) (results := [2, 3])
      (by simpa only [hargs] using hrun) br
    exact ecall.mono (by simp [excessBudget, trailBudget, resizeBudget]; omega)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hcond
    subst hcond
    obtain ⟨out, q', hext, hv, hw, wrun⟩ := RegisterWiden.widen_compiled code ids.widen hwiden hh hy hx
    have hval : (Bits.widen y x).value = x.value % 2 ^ (n + e) := by
      rw [Bits.widen_value, Nat.mod_eq_of_lt
        ((Bits.value_lt x).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    refine ⟨out, q', hext, hv, by rw [← Bits.eq_resizeTo hval]; exact hw, ?_⟩
    let r2 := bindResults r1 [4] [Value.pointer q']
    have last : Within code out r2 (.ret [.register 4]) [.pointer q'] out 3 := by
      simpa [r2, values, Atom.eval, bindResults] using Within.ret code out r2 [.register 4]
    have wcall := Within.call (procedure := ids.widen) (regs := r1)
      (arguments := [.register 3, .register 0]) (results := [4])
      (by simpa only [hargs2] using wrun) last
    have br := Within.branch (regs := r1) (test := .register 2) (b := false)
      (yes := .call ids.trail [.register 3, .register 0] [4] (.ret [.register 4]))
      (no := .call ids.widen [.register 3, .register 0] [4] (.ret [.register 4]))
      (by simp [r1, bindResults, Atom.eval]) wcall
    have ecall := Within.call (procedure := ids.excess) (regs := regs)
      (arguments := [.register 1, .register 0]) (results := [2, 3])
      (by simpa only [hargs] using hrun) br
    exact ecall.mono (by simp [excessBudget, RegisterWiden.widenBudget, resizeBudget]; omega)

/-- Resize every word of a list to the width of one shape word. -/
theorem resizeList_compiled (code : Code p) (ids : Procedures p) (hc : ids.Matches code)
    (self : Fin p) (hself : code self = RegisterListMap.body self ids.resize)
    {h : Heap} (hh : Valid h) {lp sp : Ptr} {n k : ℕ} {xs : List (Bits n)} {s : Bits k}
    (hl : WordsAt h lp xs) (hs : BitsAt h sp s) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (xs.map (Bits.resizeTo k)) ∧
      Within code h (initialRegisters [.pointer lp, .pointer sp]) (code self)
        [.pointer q] out ((resizeBudget k n + 35) * xs.length + 13) :=
  RegisterListMap.compiled_const code self ids.resize hself
    (fun h p (x : Bits n) => BitsAt h p x) (fun h p (s : Bits k) => BitsAt h p s)
    (fun h p (y : Bits k) => BitsAt h p y)
    (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he)
    (fun _ hy => hy.allocated) (fun _ x => Bits.resizeTo k x) (resizeBudget k n) hh hl hs
    (fun hv _ _ _ hx hs' => resize_compiled code ids hc hv hx hs')

/-- Arguments: signed word, shape word. The sign cell is copied with the
resized magnitude as its tail. -/
def signedBody (resize : Fin p) : Command p :=
  .load (.register 0) 2 15 3 { CompiledTrie.failCases with
    bit := .call resize [.register 2, .register 1] [4]
      (.allocate 5 (.bit (.register 3) (.register 4)) (.ret [.register 5])) }

def signedBudget (k n : ℕ) : ℕ := resizeBudget k n + 30

theorem signed_compiled (code : Code p) (ids : Procedures p) (hc : ids.Matches code)
    (self : Fin p) (hself : code self = signedBody ids.resize)
    {h : Heap} (hh : Valid h) {dp sp : Ptr} {n k : ℕ} {d : SignedWord n} {s : Bits k}
    (hd : SignedAt h dp d) (hs : BitsAt h sp s) :
    ∃ out q, Extends h out ∧ Valid out ∧ SignedAt out q (d.resizeTo k) ∧
      Within code h (initialRegisters [.pointer dp, .pointer sp]) (code self)
        [.pointer q] out (signedBudget k n) := by
  obtain ⟨mag, cell, hmag⟩ := hd
  obtain ⟨mid, q, hext, hv, hq, rrun⟩ := resize_compiled code ids hc hh hmag (s := s) hs
  have hb := allocate_bit hv d.negative hq
  refine ⟨mid ++ [.bit d.negative q], mid.length, hext.trans hb.1.1, hb.1.2.1, ?_, ?_⟩
  · exact ⟨q, by simp [SignedWord.resizeTo], hq.mono hb.1.1⟩
  let regs := initialRegisters [Value.pointer dp, .pointer sp]
  let loaded := loadRegisters regs 2 15 3 (.bit d.negative mag)
  let r1 := bindResults loaded [4] [Value.pointer q]
  have last : Within code (mid ++ [.bit d.negative q])
      (Function.update r1 5 (.pointer mid.length)) (.ret [.register 5])
      [.pointer mid.length] (mid ++ [.bit d.negative q]) 3 := by
    simpa [values, Atom.eval] using Within.ret code (mid ++ [.bit d.negative q])
      (Function.update r1 5 (.pointer mid.length)) [.register 5]
  have alloc := Within.allocate (regs := r1) (dst := 5)
    (expr := .bit (.register 3) (.register 4))
    (by simp [r1, loaded, regs, bindResults, loadRegisters, decoded, CellExpr.eval, Atom.eval,
      Value.asFlag, Value.asPointer]) last
  have hargs : values loaded [.register 2, .register 1] = [.pointer mag, .pointer sp] := by
    simp [loaded, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
  have call := Within.call (procedure := ids.resize) (regs := loaded)
    (arguments := [.register 2, .register 1]) (results := [4])
    (by simpa only [hargs] using rrun) alloc
  have load := Within.load (regs := regs) (address := .register 0)
    (first := 2) (second := 15) (bit := 3)
    (branches := { CompiledTrie.failCases with
      bit := .call ids.resize [.register 2, .register 1] [4]
        (.allocate 5 (.bit (.register 3) (.register 4)) (.ret [.register 5])) })
    (by simp [regs, initialRegisters, Atom.eval]) cell call
  rw [hself]
  exact load.mono (by simp [CellExpr.args, signedBudget]; omega)

/-- Resize every signed word of a list. -/
theorem signedList_compiled (code : Code p) (ids : Procedures p) (hc : ids.Matches code)
    (signed self : Fin p) (hsigned : code signed = signedBody ids.resize)
    (hself : code self = RegisterListMap.body self signed)
    {h : Heap} (hh : Valid h) {lp sp : Ptr} {n k : ℕ} {ds : List (SignedWord n)} {s : Bits k}
    (hl : DeltasAt h lp ds) (hs : BitsAt h sp s) :
    ∃ out q, Extends h out ∧ Valid out ∧ DeltasAt out q (ds.map (SignedWord.resizeTo k)) ∧
      Within code h (initialRegisters [.pointer lp, .pointer sp]) (code self)
        [.pointer q] out ((signedBudget k n + 35) * ds.length + 13) :=
  RegisterListMap.compiled_const code self signed hself
    (fun h p (x : SignedWord n) => SignedAt h p x) (fun h p (s : Bits k) => BitsAt h p s)
    (fun h p (y : SignedWord k) => SignedAt h p y)
    (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he)
    (fun _ hy => hy.allocated) (fun _ x => SignedWord.resizeTo k x) (signedBudget k n) hh hl hs
    (fun hv _ _ _ hx hs' => signed_compiled code ids hc signed hsigned hv hx hs')

end WeightedMIS.RegisterResize
