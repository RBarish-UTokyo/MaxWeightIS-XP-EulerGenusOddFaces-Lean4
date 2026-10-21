module

public import WeightedMIS.HardWidths
public import WeightedMIS.RegisterWiden
public import WeightedMIS.RegisterListMap
public import WeightedMIS.RegisterGraphArcs
public import WeightedMIS.RegisterIncidenceRows
public import WeightedMIS.RegisterWeightMask
public import WeightedMIS.RegisterAdjacencyScan
public import WeightedMIS.RegisterFaceRow

/-!
# Input words of the hard-component solver

* `edges_compiled`: the endpoint-word records `.pair left right` of a stored
  ribbon table, sharing the stored words.
* `doubles_compiled`: `k` successive self-widenings of a zero word.
* `ratConsts_compiled`: from a list of length `n` and a list of length `m`,
  the words `0, 1, 2` of the rational width `ratWidth n m`, the stored
  rationals `0, 1, 2` with unit denominator, and the face constants.
* `searchConsts_compiled`: from lists of lengths `d`, `m`, `n` and a nonempty
  list of cost words of width `c`, the zero and unit words of the search
  width `searchWidth c n m d`.

The file also converts stored lists into functions on `Fin`.
-/

@[expose] public section

namespace WeightedMIS.RegisterHardInputs

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.RibbonTable
open WeightedMIS.RegisterFlagKeys WeightedMIS.HardWidths
open WeightedMIS.RegisterIncidenceRows (EdgeAt)

variable {p : ℕ}

/-! ## Casts and lists -/

theorem zero_cast {h : Heap} {ptr : Ptr} {a b : ℕ} (hx : BitsAt h ptr (Bits.zero a))
    (hab : a = b) : BitsAt h ptr (Bits.zero b) := hab ▸ hx

theorem listRep_listAt {α : Type*} {R : Heap → Ptr → α → Prop} {h : Heap} {ptr : Ptr}
    {l : List α} (hl : ListRep R h ptr l) : ∃ xs, ListAt h ptr xs ∧ xs.length = l.length := by
  obtain ⟨xs, hx, hf⟩ := hl
  exact ⟨xs, hx, hf.length_eq⟩

theorem exists_ofFn {α : Type*} (l : List α) {m : ℕ} (hl : l.length = m) :
    ∃ f : Fin m → α, List.ofFn f = l := by
  subst hl
  exact ⟨fun i => l[i], List.ofFn_getElem⟩

theorem exists_ofFn_map {α β : Type*} (g : α → β) (l : List α) {m : ℕ} (V : Fin m → β)
    (hl : l.map g = List.ofFn V) : ∃ f : Fin m → α, List.ofFn f = l ∧ ∀ e, g (f e) = V e := by
  have hlen : l.length = m := by simpa using congrArg List.length hl
  obtain ⟨f, rfl⟩ := exists_ofFn l hlen
  refine ⟨f, rfl, fun e => ?_⟩
  rw [List.map_ofFn] at hl
  exact congrFun (List.ofFn_injective hl) e

theorem exists_matrix {α β : Type*} (g : α → β) {m d : ℕ} (cols : List (List α))
    (V : Fin m → Fin d → β)
    (hc : cols.map (List.map g) = List.ofFn (fun e => List.ofFn (V e))) :
    ∃ D : Fin m → Fin d → α, List.ofFn (fun e => List.ofFn (D e)) = cols ∧
      ∀ e i, g (D e i) = V e i := by
  obtain ⟨f, hf, hv⟩ := exists_ofFn_map (List.map g) cols (fun e => List.ofFn (V e)) hc
  have hrow : ∀ e, ∃ r : Fin d → α, List.ofFn r = f e ∧ ∀ i, g (r i) = V e i :=
    fun e => exists_ofFn_map g (f e) (V e) (hv e)
  choose D hD1 hD2 using hrow
  refine ⟨D, ?_, hD2⟩
  rw [← hf]
  exact congrArg List.ofFn (funext hD1)

/-- A stored row of canonical rationals of one width is a stored rational row of a function. -/
theorem exists_row {w0 n : ℕ} {h : Heap} {wp : Ptr} {w : Fin n → ℚ}
    (hw : ListRep (RegisterWeightMask.CanonAt w0) h wp (List.ofFn w)) :
    ∃ q : Fin n → BinaryRational.Word w0, (∀ v, BinaryRational.Canonical (q v)) ∧
      (∀ v, (q v).value = w v) ∧
      RegisterRationalRow.RowAt h wp ((List.finRange n).map q) := by
  obtain ⟨xs, hx, hf⟩ := hw
  have hlen : xs.length = n := by simpa using hf.length_eq
  have hget : ∀ v : Fin n, RegisterWeightMask.CanonAt w0 h (xs[v.val]'(by omega)) (w v) := by
    intro v
    have := (List.forall₂_iff_get.mp hf).2 v.val (by omega) (by simp)
    simpa using this
  choose q hq using hget
  refine ⟨q, fun v => (hq v).2.2, fun v => (hq v).2.1, xs, hx, ?_⟩
  rw [List.forall₂_iff_get]
  refine ⟨by simp [hlen], fun i h1 h2 => ?_⟩
  have hi : i < n := by omega
  simpa using (hq ⟨i, hi⟩).1

/-! ## Endpoint-word records -/

/-- Argument 0 = stored edge record; the result is `.pair left right`. -/
def edgeItemBody : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    pair := .load (.register 3) 4 5 15 { CompiledTrie.failCases with
      pair := .load (.register 5) 6 7 15 { CompiledTrie.failCases with
        pair := .allocate 8 (.pair (.register 4) (.register 6)) (.ret [.register 8]) } } }

def edgesBudget (m : ℕ) : ℕ := 80 * m + 13

theorem edges_compiled (code : Code p) (self item : Fin p)
    (hself : code self = RegisterListMap.body self item) (hitem : code item = edgeItemBody)
    {W : ℕ} {h : Heap} (hh : Valid h) {tp : Ptr} {T : List (EdgeRec W)}
    (hT : RecordsAt h tp T) :
    ∃ out q, Extends h out ∧ Valid out ∧ ListRep EdgeAt out q (RegisterGraphArcs.edgePairs T) ∧
      Within code h (initialRegisters [.pointer tp, .pointer 0]) (code self) [.pointer q] out
        (edgesBudget T.length) := by
  obtain ⟨out, q, he, ho, hq, hw⟩ := RegisterListMap.compiled_const code self item hself
    EdgeRecAt (fun _ _ (_ : Unit) => True) (fun h p (e : Bits W × Bits W) => EdgeAt h p e)
    (fun he _ _ hr => hr.mono he) (fun _ _ _ _ => trivial) (fun he _ _ hb => hb.mono he)
    (fun _ hb => by obtain ⟨_, _, c, _⟩ := hb; exact (List.getElem?_eq_some_iff.mp c).1)
    (fun _ r => (r.left, r.right)) 45 (data := ()) (dataPtr := 0) hh hT trivial
    (fun {h} hv {xp} {x} _ hx _ => by
      obtain ⟨kp, a, lp, b, rp, c, _, _, _, _, _, _, c0, -, ca, hl, cb, hr, -⟩ := hx
      obtain ⟨e1, v1, c1⟩ := alloc_pair hv hl.allocated hr.allocated
      refine ⟨_, h.length, e1, v1, ⟨lp, rp, c1, hl.mono e1, hr.mono e1⟩, ?_⟩
      rw [hitem]
      refine (Within.load (pointer := xp) (c := .pair kp a) (by reg_simp) c0
        (Within.load (pointer := a) (c := .pair lp b) (by reg_simp) ca
        (Within.load (pointer := b) (c := .pair rp c) (by reg_simp) cb
        (Within.allocate (c := .pair lp rp) (by reg_simp)
        (ret_values (by reg_simp) le_rfl))))).mono ?_
      simp [CellExpr.args])
  refine ⟨out, q, he, ho, ?_, hw.mono (by simp [edgesBudget])⟩
  simpa [RegisterGraphArcs.edgePairs] using hq

/-- The two stored edge representations coincide. -/
theorem edgeWordsAt_of {W : ℕ} {h : Heap} {ptr : Ptr} {es : List (Bits W × Bits W)}
    (he : ListRep EdgeAt h ptr es) : RegisterAdjacencyScan.EdgeWordsAt h ptr es := he

/-! ## Doubling a zero word -/

def doubles (widen : Fin p) : ℕ → Command p
  | 0 => .ret [.register 0]
  | k + 1 => .call widen [.register 0, .register 0] [0] (doubles widen k)

def doublesBudget : ℕ → ℕ → ℕ
  | 0, _ => 3
  | k + 1, w => 5 + RegisterWiden.widenBudget w + doublesBudget k (w + w)

theorem doubles_compiled (code : Code p) (widen : Fin p)
    (hw : code widen = RegisterWiden.widenBody widen) :
    ∀ (k : ℕ) {h : Heap}, Valid h → ∀ {regs : Registers} {ptr : Ptr} {w : ℕ},
      regs 0 = .pointer ptr → BitsAt h ptr (Bits.zero w) →
      ∃ out q, Extends h out ∧ Valid out ∧ BitsAt out q (Bits.zero (2 ^ k * w)) ∧
        Within code h regs (doubles widen k) [.pointer q] out (doublesBudget k w) := by
  intro k
  induction k with
  | zero =>
    intro h hh regs ptr w hreg hz
    refine ⟨h, ptr, Extends.refl h, hh, zero_cast hz (by ring), ?_⟩
    exact ret_values (by simp [values, Atom.eval, hreg]) (by simp [doublesBudget])
  | succ k ih =>
    intro h hh regs ptr w hreg hz
    obtain ⟨o1, q1, e1, v1, b1, w1⟩ := RegisterWiden.widen_compiled code widen hw hh hz hz
    rw [Bits.widen_zero] at b1
    obtain ⟨o2, q2, e2, v2, b2, w2⟩ := ih v1 (regs := bindResults regs [0] [.pointer q1])
      (by simp [bindResults]) b1
    refine ⟨o2, q2, e1.trans e2, v2, zero_cast b2 (by ring), ?_⟩
    exact (call_of (by simp [values, Atom.eval, hreg]) w1 w2).mono (by simp [doublesBudget])

/-- Argument 0 = a zero word of width one; result: the zero word of `baseWidth`. -/
def dblBody (widen : Fin p) : Command p := doubles widen 13

def dblBudget : ℕ := doublesBudget 13 1

theorem dbl_compiled (code : Code p) (self widen : Fin p) (hself : code self = dblBody widen)
    (hw : code widen = RegisterWiden.widenBody widen) {h : Heap} (hh : Valid h) {ptr : Ptr}
    (hz : BitsAt h ptr (Bits.zero 1)) :
    ∃ out q, Extends h out ∧ Valid out ∧ BitsAt out q (Bits.zero baseWidth) ∧
      Within code h (initialRegisters [.pointer ptr]) (code self) [.pointer q] out dblBudget := by
  obtain ⟨out, q, e, v, b, w⟩ := doubles_compiled code widen hw 13 hh
    (regs := initialRegisters [.pointer ptr]) (by simp [initialRegisters]) hz
  rw [hself]
  exact ⟨out, q, e, v, zero_cast b (by simp [baseWidth]), w⟩

/-! ## Small words -/

theorem cell_last (h : Heap) (c : Cell) : (h ++ [c])[h.length]? = some c := by simp

theorem zero_one {h : Heap} (hh : Valid h) :
    BitsAt (h ++ [.bit false 0]) h.length (Bits.zero 1) ∧ Extends h (h ++ [.bit false 0]) ∧
      Valid (h ++ [.bit false 0]) := by
  obtain ⟨e, v, b⟩ := alloc_bit hh false (BitsAt.nil hh.1)
  exact ⟨b, e, v⟩

theorem widen_word {N : ℕ} (k v : ℕ) (a : Bits k) (hv : a.value = v) (hN : v < 2 ^ (k + N)) :
    Bits.widen (Bits.zero N) a = word (k + N) v := by
  apply ResidualListReach.bits_value_inj
  rw [Bits.widen_value, hv, word_value hN]

/-! ## Rational constants -/

structure ConstsOut (N : ℕ) (h : Heap) (fc oneP zr orr tr : Ptr) : Prop where
  face : RegisterFaceRow.ConstsAt (word N 1) (word N 0) h fc
  one : BitsAt h oneP (word N 1)
  zeroR : StoredRational.At h zr ⟨false, word N 0, word N 1⟩
  oneR : StoredRational.At h orr ⟨false, word N 1, word N 1⟩
  twoR : StoredRational.At h tr ⟨false, word N 2, word N 1⟩

theorem ConstsOut.mono {N : ℕ} {h h' : Heap} (he : Extends h h') {fc oneP zr orr tr : Ptr}
    (c : ConstsOut N h fc oneP zr orr tr) : ConstsOut N h' fc oneP zr orr tr :=
  ⟨c.face.mono he, c.one.mono he, c.zeroR.mono he, c.oneR.mono he, c.twoR.mono he⟩

/-- Arguments 0 = a list of length `n`, 1 = a list of length `m`.
Results: face constants, unit word, stored rationals `0`, `1`, `2`. -/
def ratConstsBody (dbl pad widen : Fin p) : Command p :=
  .allocate 2 (.bit (.flag false) .null)
  (.call dbl [.register 2] [2]
  (.allocate 3 (.cons (.register 0) (.register 0))
  (.allocate 4 (.cons (.register 1) (.register 1))
  (.call pad [.register 3, .register 2] [2]
  (.call pad [.register 3, .register 2] [2]
  (.call pad [.register 3, .register 2] [2]
  (.call pad [.register 4, .register 2] [2]
  (.call pad [.register 4, .register 2] [2]
  (.call pad [.register 4, .register 2] [2]
  (.allocate 5 (.bit (.flag true) .null)
  (.allocate 6 (.bit (.flag false) .null)
  (.allocate 7 (.bit (.flag false) (.register 6))
  (.allocate 8 (.bit (.flag false) (.register 5))
  (.allocate 9 (.bit (.flag true) (.register 6))
  (.call widen [.register 2, .register 7] [7]
  (.call widen [.register 2, .register 8] [8]
  (.call widen [.register 2, .register 9] [9]
  (.allocate 10 (.bit (.flag false) (.register 7))
  (.allocate 11 (.pair (.register 10) (.register 8))
  (.allocate 10 (.bit (.flag false) (.register 8))
  (.allocate 12 (.pair (.register 10) (.register 8))
  (.allocate 10 (.bit (.flag false) (.register 9))
  (.allocate 13 (.pair (.register 10) (.register 8))
  (.allocate 14 (.pair (.register 8) (.register 7))
  (.ret [.register 14, .register 8, .register 11, .register 12, .register 13])))))))))))))))))))))))))

def ratConstsBudget (n m : ℕ) : ℕ :=
  dblBudget + 3 * RegisterWiden.padBudget (ratCore n m) (m + 1) +
    3 * RegisterWiden.padBudget (ratCore n m) (n + 1) +
    3 * RegisterWiden.widenBudget (ratCore n m) + 200

theorem padBudget_mono {w w' L L' : ℕ} (hw : w ≤ w') (hL : L ≤ L') :
    RegisterWiden.padBudget w L ≤ RegisterWiden.padBudget w' L' := by
  unfold RegisterWiden.padBudget RegisterWiden.widenBudget
  gcongr

theorem ratCore_mono_steps (n m : ℕ) :
    padW baseWidth (n + 1) ≤ ratCore n m ∧
    padW (padW baseWidth (n + 1)) (n + 1) ≤ ratCore n m ∧
    padW (padW (padW baseWidth (n + 1)) (n + 1)) (n + 1) ≤ ratCore n m ∧
    padW (padW (padW (padW baseWidth (n + 1)) (n + 1)) (n + 1)) (m + 1) ≤ ratCore n m ∧
    padW (padW (padW (padW (padW baseWidth (n + 1)) (n + 1)) (n + 1)) (m + 1)) (m + 1) ≤
      ratCore n m ∧ baseWidth ≤ ratCore n m := by
  have g : ∀ w L, 1 ≤ L → w ≤ padW w L := fun w L hL => by
    unfold padW; nlinarith
  have h1 := g baseWidth (n + 1) (by omega)
  have h2 := g (padW baseWidth (n + 1)) (n + 1) (by omega)
  have h3 := g (padW (padW baseWidth (n + 1)) (n + 1)) (n + 1) (by omega)
  have h4 := g (padW (padW (padW baseWidth (n + 1)) (n + 1)) (n + 1)) (m + 1) (by omega)
  have h5 := g (padW (padW (padW (padW baseWidth (n + 1)) (n + 1)) (n + 1)) (m + 1)) (m + 1)
    (by omega)
  have h6 := g (padW (padW (padW (padW (padW baseWidth (n + 1)) (n + 1)) (n + 1)) (m + 1))
    (m + 1)) (m + 1) (by omega)
  unfold ratCore
  omega

theorem ratConsts_compiled (code : Code p) (self dbl pad widen : Fin p)
    (hself : code self = ratConstsBody dbl pad widen) (hdbl : code dbl = dblBody widen)
    (hpad : code pad = RegisterWiden.padBody pad widen)
    (hw : code widen = RegisterWiden.widenBody widen)
    {n m : ℕ} {h : Heap} (hh : Valid h) {np mp : Ptr} {xs ys : List Ptr}
    (hxs : ListAt h np xs) (hxl : xs.length = n) (hys : ListAt h mp ys) (hyl : ys.length = m) :
    ∃ out fc oneP zr orr tr, Extends h out ∧ Valid out ∧
      ConstsOut (ratWidth n m) out fc oneP zr orr tr ∧
      Within code h (initialRegisters [.pointer np, .pointer mp]) (code self)
        [.pointer fc, .pointer oneP, .pointer zr, .pointer orr, .pointer tr] out
        (ratConstsBudget n m) := by
  obtain ⟨b0, e0, v0⟩ := zero_one hh
  obtain ⟨o1, k1, e1, v1, b1, w1⟩ := dbl_compiled code dbl widen hdbl hw v0 b0
  have e01 := e0.trans e1
  obtain ⟨e2, v2, c2⟩ := RegisterGraphArcs.alloc_cons v1 (hxs.mono e01).allocated
    (hxs.mono e01).allocated
  have l2 : ListAt (o1 ++ [Cell.cons np np]) o1.length (np :: xs) :=
    PointerMemory.ListAt.cons c2 ((hxs.mono e01).mono e2)
  obtain ⟨e3, v3, c3⟩ := RegisterGraphArcs.alloc_cons v2 ((hys.mono e01).mono e2).allocated
    ((hys.mono e01).mono e2).allocated
  have l3 : ListAt ((o1 ++ [Cell.cons np np]) ++ [Cell.cons mp mp])
      (o1 ++ [Cell.cons np np]).length (mp :: ys) :=
    PointerMemory.ListAt.cons c3 (((hys.mono e01).mono e2).mono e3)
  have l2' := l2.mono e3
  have e03 := e01.trans (e2.trans e3)
  -- three pads over the list of length n + 1
  obtain ⟨o4, k4, e4, v4, b4, w4⟩ := RegisterWiden.pad_compiled code pad widen hpad hw v3 l2'
    ((b1.mono e2).mono e3)
  rw [Bits.pad_eq_zero] at b4
  obtain ⟨o5, k5, e5, v5, b5, w5⟩ := RegisterWiden.pad_compiled code pad widen hpad hw v4
    (l2'.mono e4) b4
  rw [Bits.pad_eq_zero] at b5
  obtain ⟨o6, k6, e6, v6, b6, w6⟩ := RegisterWiden.pad_compiled code pad widen hpad hw v5
    ((l2'.mono e4).mono e5) b5
  rw [Bits.pad_eq_zero] at b6
  have e46 := e4.trans (e5.trans e6)
  obtain ⟨o7, k7, e7, v7, b7, w7⟩ := RegisterWiden.pad_compiled code pad widen hpad hw v6
    (l3.mono e46) b6
  rw [Bits.pad_eq_zero] at b7
  obtain ⟨o8, k8, e8, v8, b8, w8⟩ := RegisterWiden.pad_compiled code pad widen hpad hw v7
    ((l3.mono e46).mono e7) b7
  rw [Bits.pad_eq_zero] at b8
  obtain ⟨o9, k9, e9, v9, b9, w9⟩ := RegisterWiden.pad_compiled code pad widen hpad hw v8
    (((l3.mono e46).mono e7).mono e8) b8
  rw [Bits.pad_eq_zero] at b9
  have bc : BitsAt o9 k9 (Bits.zero (ratCore n m)) := zero_cast b9 (by
    simp only [List.length_cons, hxl, hyl, ratCore, padW])
  -- low words
  obtain ⟨f5, u5, a5⟩ := alloc_bit v9 true (BitsAt.nil v9.1)
  obtain ⟨f6, u6, a6⟩ := alloc_bit u5 false (BitsAt.nil u5.1)
  obtain ⟨f7, u7, a7⟩ := alloc_bit u6 false a6
  obtain ⟨f8, u8, a8⟩ := alloc_bit u7 false ((a5.mono f6).mono f7)
  obtain ⟨f9, u9, a9⟩ := alloc_bit u8 true ((a6.mono f7).mono f8)
  have f59 := f5.trans (f6.trans (f7.trans (f8.trans f9)))
  have bc9 := bc.mono f59
  obtain ⟨o10, k10, e10, v10, b10, w10⟩ := RegisterWiden.widen_compiled code widen hw u9 bc9
    ((a7.mono f8).mono f9)
  obtain ⟨o11, k11, e11, v11, b11, w11⟩ := RegisterWiden.widen_compiled code widen hw v10
    (bc9.mono e10) ((a8.mono f9).mono e10)
  obtain ⟨o12, k12, e12, v12, b12, w12⟩ := RegisterWiden.widen_compiled code widen hw v11
    ((bc9.mono e10).mono e11) ((a9.mono e10).mono e11)
  have hN : ∀ v, v < 4 → v < 2 ^ (2 + ratCore n m) := fun v hv =>
    lt_of_lt_of_le hv (by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [widen_word 2 0 _ (by simp [Bits.value]) (hN 0 (by norm_num))] at b10
  rw [widen_word 2 1 _ (by simp [Bits.value]) (hN 1 (by norm_num))] at b11
  rw [widen_word 2 2 _ (by simp [Bits.value]) (hN 2 (by norm_num))] at b12
  have b10' := (b10.mono e11).mono e12
  have b11' := b11.mono e12
  -- stored rationals
  obtain ⟨g1, t1, c1⟩ := alloc_bit v12 false b10'
  obtain ⟨g2, t2, c2'⟩ := alloc_pair t1 c1.allocated (b11'.mono g1).allocated
  obtain ⟨g3, t3, c3'⟩ := alloc_bit t2 false ((b11'.mono g1).mono g2)
  obtain ⟨g4, t4, c4⟩ := alloc_pair t3 c3'.allocated (((b11'.mono g1).mono g2).mono g3).allocated
  obtain ⟨g5, t5, c5⟩ := alloc_bit t4 false ((((b12.mono g1).mono g2).mono g3).mono g4)
  obtain ⟨g6, t6, c6⟩ := alloc_pair t5 c5.allocated
    (((((b11'.mono g1).mono g2).mono g3).mono g4).mono g5).allocated
  have g16 := g1.trans (g2.trans (g3.trans (g4.trans (g5.trans g6))))
  obtain ⟨g7, t7, c7⟩ := alloc_pair t6 ((b11'.mono g16)).allocated ((b10'.mono g16)).allocated
  refine ⟨o12 ++ [Cell.bit false k10] ++ [Cell.pair (o12).length k11] ++ [Cell.bit false k11] ++ [Cell.pair (o12 ++ [Cell.bit false k10] ++ [Cell.pair (o12).length k11]).length k11] ++ [Cell.bit false k12] ++ [Cell.pair (o12 ++ [Cell.bit false k10] ++ [Cell.pair (o12).length k11] ++ [Cell.bit false k11] ++ [Cell.pair (o12 ++ [Cell.bit false k10] ++ [Cell.pair (o12).length k11]).length k11]).length k11] ++ [Cell.pair k11 k10],
    (o12 ++ [Cell.bit false k10] ++ [Cell.pair (o12).length k11] ++ [Cell.bit false k11] ++ [Cell.pair (o12 ++ [Cell.bit false k10] ++ [Cell.pair (o12).length k11]).length k11] ++ [Cell.bit false k12] ++ [Cell.pair (o12 ++ [Cell.bit false k10] ++ [Cell.pair (o12).length k11] ++ [Cell.bit false k11] ++ [Cell.pair (o12 ++ [Cell.bit false k10] ++ [Cell.pair (o12).length k11]).length k11]).length k11]).length, k11, (o12 ++ [Cell.bit false k10]).length, (o12 ++ [Cell.bit false k10] ++ [Cell.pair (o12).length k11] ++ [Cell.bit false k11]).length, (o12 ++ [Cell.bit false k10] ++ [Cell.pair (o12).length k11] ++ [Cell.bit false k11] ++ [Cell.pair (o12 ++ [Cell.bit false k10] ++ [Cell.pair (o12).length k11]).length k11] ++ [Cell.bit false k12]).length,
    e03.trans (e46.trans (e7.trans (e8.trans (e9.trans
    (f59.trans (e10.trans (e11.trans (e12.trans (g16.trans g7))))))))), t7, ?_, ?_⟩
  · refine ⟨⟨k11, k10, c7, (b11'.mono g16).mono g7, (b10'.mono g16).mono g7⟩,
      (b11'.mono g16).mono g7, ?_, ?_, ?_⟩
    · exact ⟨_, k10, k11, ((g3.trans (g4.trans (g5.trans g6))).trans g7).lookup c2',
        ((g2.trans (g3.trans (g4.trans (g5.trans g6)))).trans g7).lookup (cell_last _ _),
        (b10'.mono g16).mono g7, (b11'.mono g16).mono g7⟩
    · exact ⟨_, k11, k11, ((g5.trans g6).trans g7).lookup c4,
        ((g4.trans (g5.trans g6)).trans g7).lookup (cell_last _ _),
        (b11'.mono g16).mono g7, (b11'.mono g16).mono g7⟩
    · exact ⟨_, k12, k11, g7.lookup c6, (g6.trans g7).lookup (cell_last _ _),
        (((((((b12.mono g1).mono g2).mono g3).mono g4).mono g5).mono g6).mono g7),
        (b11'.mono g16).mono g7⟩
  · rw [hself]
    refine (Within.allocate (c := .bit false 0) (by reg_simp)
      (call_of (by reg_simp) w1
      (Within.allocate (c := .cons np np) (by reg_simp)
      (Within.allocate (c := .cons mp mp) (by reg_simp)
      (call_of (by reg_simp) w4 (call_of (by reg_simp) w5 (call_of (by reg_simp) w6
      (call_of (by reg_simp) w7 (call_of (by reg_simp) w8 (call_of (by reg_simp) w9
      (Within.allocate (c := .bit true 0) (by reg_simp)
      (Within.allocate (c := .bit false 0) (by reg_simp)
      (Within.allocate (c := .bit false _) (by reg_simp)
      (Within.allocate (c := .bit false _) (by reg_simp)
      (Within.allocate (c := .bit true _) (by reg_simp)
      (call_of (by reg_simp) w10 (call_of (by reg_simp) w11 (call_of (by reg_simp) w12
      (Within.allocate (c := .bit false _) (by reg_simp)
      (Within.allocate (c := .pair _ _) (by reg_simp)
      (Within.allocate (c := .bit false _) (by reg_simp)
      (Within.allocate (c := .pair _ _) (by reg_simp)
      (Within.allocate (c := .bit false _) (by reg_simp)
      (Within.allocate (c := .pair _ _) (by reg_simp)
      (Within.allocate (c := .pair _ _) (by reg_simp)
      (ret_values (by reg_simp) le_rfl)))))))))))))))))))))))))).mono ?_
    have s := ratCore_mono_steps n m
    have p1 := padBudget_mono (L := n + 1) (L' := n + 1) s.2.2.2.2.2 le_rfl
    have p2 := padBudget_mono (L := n + 1) (L' := n + 1) s.1 le_rfl
    have p3 := padBudget_mono (L := n + 1) (L' := n + 1) s.2.1 le_rfl
    have p4 := padBudget_mono (L := m + 1) (L' := m + 1) s.2.2.1 le_rfl
    have p5 := padBudget_mono (L := m + 1) (L' := m + 1) s.2.2.2.1 le_rfl
    have p6 := padBudget_mono (L := m + 1) (L' := m + 1) s.2.2.2.2.1 le_rfl
    simp only [padW] at p1 p2 p3 p4 p5 p6
    simp only [ratConstsBudget, ratCore, padW, CellExpr.args, List.length_cons, List.length_nil,
      hxl, hyl] at p1 p2 p3 p4 p5 p6 ⊢
    linarith

end WeightedMIS.RegisterHardInputs

/-! ## Search constants -/

namespace WeightedMIS.RegisterHardInputs

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.RibbonTable
open WeightedMIS.RegisterFlagKeys WeightedMIS.HardWidths

variable {p : ℕ}

/-- Arguments 0 = a list of length `d`, 1 = a nonempty list of words of width
`c`, 2 = a list of length `m`, 3 = a list of length `n`.
Results: the zero word and the unit word of `searchWidth c n m d`. -/
def searchConstsBody (dbl pad widen : Fin p) : Command p :=
  .allocate 4 (.bit (.flag false) .null)
  (.call dbl [.register 4] [4]
  (.call pad [.register 2, .register 4] [5]
  (.call pad [.register 3, .register 4] [6]
  (.load (.register 1) 7 8 15 { CompiledTrie.failCases with
    cons :=
      .call widen [.register 7, .register 4] [9]
      (.call widen [.register 5, .register 9] [9]
      (.call widen [.register 6, .register 9] [9]
      (.allocate 10 (.cons (.register 0) (.register 0))
      (.call pad [.register 10, .register 9] [9]
      (.allocate 11 (.bit (.flag true) .null)
      (.allocate 12 (.bit (.flag false) (.register 11))
      (.allocate 13 (.bit (.flag false) .null)
      (.allocate 14 (.bit (.flag false) (.register 13))
      (.call widen [.register 9, .register 12] [12]
      (.call widen [.register 9, .register 14] [14]
      (.ret [.register 14, .register 12]))))))))))) }))))

def searchConstsBudget (c n m d : ℕ) : ℕ :=
  dblBudget + RegisterWiden.padBudget baseWidth m + RegisterWiden.padBudget baseWidth n +
    RegisterWiden.widenBudget c + RegisterWiden.widenBudget (padW baseWidth m) +
    RegisterWiden.widenBudget (padW baseWidth n) +
    RegisterWiden.padBudget (shapeWidth c n m) (d + 1) +
    2 * RegisterWiden.widenBudget (searchCore c n m d) + 200

theorem searchConsts_compiled (code : Code p) (self dbl pad widen : Fin p)
    (hself : code self = searchConstsBody dbl pad widen) (hdbl : code dbl = dblBody widen)
    (hpad : code pad = RegisterWiden.padBody pad widen)
    (hw : code widen = RegisterWiden.widenBody widen)
    {c n m d : ℕ} {h : Heap} (hh : Valid h) {ap cp mp np : Ptr} {ds ms ns : List Ptr}
    {costs : List (Bits c)}
    (hds : ListAt h ap ds) (hdl : ds.length = d) (hcs : WordsAt h cp costs) (hne : costs ≠ [])
    (hms : ListAt h mp ms) (hml : ms.length = m) (hns : ListAt h np ns) (hnl : ns.length = n) :
    ∃ out zp op, Extends h out ∧ Valid out ∧
      BitsAt out zp (Bits.zero (searchWidth c n m d)) ∧
      BitsAt out op (word (searchWidth c n m d) 1) ∧
      Within code h (initialRegisters [.pointer ap, .pointer cp, .pointer mp, .pointer np])
        (code self) [.pointer zp, .pointer op] out (searchConstsBudget c n m d) := by
  obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨b0, e0, v0⟩ := zero_one hh
  obtain ⟨o1, k1, e1, v1, b1, w1⟩ := dbl_compiled code dbl widen hdbl hw v0 b0
  have e01 := e0.trans e1
  obtain ⟨o2, k2, e2, v2, b2, w2⟩ := RegisterWiden.pad_compiled code pad widen hpad hw v1
    (hms.mono e01) b1
  rw [Bits.pad_eq_zero, hml] at b2
  obtain ⟨o3, k3, e3, v3, b3, w3⟩ := RegisterWiden.pad_compiled code pad widen hpad hw v2
    ((hns.mono e01).mono e2) (b1.mono e2)
  rw [Bits.pad_eq_zero, hnl] at b3
  have e03 := e01.trans (e2.trans e3)
  obtain ⟨x0, rt, cell, hx0, -⟩ := WordsAt.cons_iff.mp (hcs.mono e03)
  obtain ⟨o4, k4, e4, v4, b4, w4⟩ := RegisterWiden.widen_compiled code widen hw v3 hx0
    ((b1.mono e2).mono e3)
  rw [Bits.widen_zero] at b4
  obtain ⟨o5, k5, e5, v5, b5, w5⟩ := RegisterWiden.widen_compiled code widen hw v4
    ((b2.mono e3).mono e4) b4
  rw [Bits.widen_zero] at b5
  obtain ⟨o6, k6, e6, v6, b6, w6⟩ := RegisterWiden.widen_compiled code widen hw v5
    ((b3.mono e4).mono e5) b5
  rw [Bits.widen_zero] at b6
  have e36 := e4.trans (e5.trans e6)
  obtain ⟨f7, u7, c7⟩ := RegisterGraphArcs.alloc_cons v6 ((hds.mono e03).mono e36).allocated
    ((hds.mono e03).mono e36).allocated
  have l7 : ListAt (o6 ++ [Cell.cons ap ap]) o6.length (ap :: ds) :=
    PointerMemory.ListAt.cons c7 (((hds.mono e03).mono e36).mono f7)
  obtain ⟨o8, k8, e8, v8, b8, w8⟩ := RegisterWiden.pad_compiled code pad widen hpad hw u7 l7
    (b6.mono f7)
  rw [Bits.pad_eq_zero] at b8
  have bc : BitsAt o8 k8 (Bits.zero (searchCore c n m d)) := zero_cast b8 (by
    simp only [List.length_cons, hdl, searchCore, shapeWidth, padW])
  obtain ⟨g1, t1, a1⟩ := alloc_bit v8 true (BitsAt.nil v8.1)
  obtain ⟨g2, t2, a2⟩ := alloc_bit t1 false a1
  obtain ⟨g3, t3, a3⟩ := alloc_bit t2 false (BitsAt.nil t2.1)
  obtain ⟨g4, t4, a4⟩ := alloc_bit t3 false a3
  have g14 := g1.trans (g2.trans (g3.trans g4))
  obtain ⟨o9, k9, e9, v9, b9, w9⟩ := RegisterWiden.widen_compiled code widen hw t4 (bc.mono g14)
    ((a2.mono g3).mono g4)
  obtain ⟨o10, k10, e10, v10, b10, w10⟩ := RegisterWiden.widen_compiled code widen hw v9
    ((bc.mono g14).mono e9) (a4.mono e9)
  have hN : ∀ v, v < 4 → v < 2 ^ (2 + searchCore c n m d) := fun v hv =>
    lt_of_lt_of_le hv (by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [widen_word 2 1 _ (by simp [Bits.value]) (hN 1 (by norm_num))] at b9
  rw [widen_word 2 0 _ (by simp [Bits.value]) (hN 0 (by norm_num))] at b10
  have hz0 : word (2 + searchCore c n m d) 0 = Bits.zero (2 + searchCore c n m d) := by
    apply ResidualListReach.bits_value_inj
    rw [word_value (hN 0 (by norm_num)), Bits.value_zero]
  rw [hz0] at b10
  refine ⟨o10, k10, k9, e03.trans (e36.trans (f7.trans (e8.trans (g14.trans (e9.trans e10))))),
    v10, b10, b9.mono e10, ?_⟩
  rw [hself]
  refine (Within.allocate (c := .bit false 0) (by reg_simp)
    (call_of (by reg_simp) w1 (call_of (by reg_simp) w2 (call_of (by reg_simp) w3
    (Within.load (pointer := cp) (c := Cell.cons x0 rt) (by reg_simp) cell
    (call_of (by reg_simp) w4 (call_of (by reg_simp) w5 (call_of (by reg_simp) w6
    (Within.allocate (c := .cons ap ap) (by reg_simp)
    (call_of (by reg_simp) w8
    (Within.allocate (c := .bit true 0) (by reg_simp)
    (Within.allocate (c := .bit false _) (by reg_simp)
    (Within.allocate (c := .bit false 0) (by reg_simp)
    (Within.allocate (c := .bit false _) (by reg_simp)
    (call_of (by reg_simp) w9 (call_of (by reg_simp) w10
    (ret_values (by reg_simp) le_rfl))))))))))))))))).mono ?_
  simp only [searchConstsBudget, searchCore, padW, shapeWidth, CellExpr.args, List.length_cons,
    List.length_nil, hdl, hml, hnl]
  linarith

end WeightedMIS.RegisterHardInputs
