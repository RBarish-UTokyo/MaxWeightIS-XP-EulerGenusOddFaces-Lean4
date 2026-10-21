module

public import WeightedMIS.RegisterDecompose
public import WeightedMIS.DecomposeWords

/-!
# Compiled bounded integral candidate rows

The entry procedure zips the edge index words `rangeWords W m` with the edge
endpoint words `edgeWords W left right` into the edge table, stores the data
record `.pair table consts`, and runs the compiled decomposition once per
stored rational generator row, using the row itself as the round counter, by
the list `flatMap` combinator. The output list of signed-word rows is exactly
`SupportCycleWords.candidatesW`; under the uniform width
`decomposeWidth n m ≤ N` (at most `64 (n + m + 3)^3`) its rows denote, in
order, the integer rows `DeterministicKernel.candidates left right`.

Each integer row is a `SignedWords.ListAt` list of signed words of width `N`
with values in `{-2, …, 2}`; `RegisterDecompose.intRow_compiled` converts such
a row into stored rationals (`ratW` with the shared denominator `1`).
-/

@[expose] public section

namespace WeightedMIS.RegisterCandidates

open PointerMemory RegisterMachine EfficientSearch EfficientSearch.Pointer StoredRational
open SupportCycleWords RegisterSupportArcs RegisterGeneratorWords RegisterDecompose
open RegisterIncidenceRows (EdgeAt)
open RegisterRationalRow (RowAt)
open RegisterRationalCut (RowsAt)

variable {p W N : ℕ}

/-- FlatMap item: arguments 0=row, 1=data, 2=accumulator; the row is its own fuel. -/
def candItemBody (decompose : Fin p) : Command p :=
  .call decompose [.register 0, .register 0, .register 1, .register 2] [3] (.ret [.register 3])

/-- Arguments 0=generator rows, 1=edge index words, 2=edge endpoint words, 3=consts. -/
def body (tableZip candFlat : Fin p) : Command p :=
  .call tableZip [.register 1, .register 2, .null] [4]
    (.allocate 5 (.pair (.register 4) (.register 3))
      (.call candFlat [.register 0, .register 5, .null] [6] (.ret [.register 6])))

/-- Arguments 0,1,2=stored rationals `0`, `1`, `2`; the result is the
magnitude record `.pair one (.pair zero two)`. -/
def constsBody (read : Fin p) : Command p :=
  .call read [.register 0] [3, 4, 5]
    (.call read [.register 1] [6, 7, 8]
      (.call read [.register 2] [9, 10, 11]
        (.allocate 12 (.pair (.register 4) (.register 10))
          (.allocate 13 (.pair (.register 7) (.register 12)) (.ret [.register 13])))))

structure Procedures (p : ℕ) where
  dec : RegisterDecompose.Procedures p
  consts : Fin p
  tableZip : Fin p
  candItem : Fin p
  candFlat : Fin p
  self : Fin p

structure Procedures.Matches (ids : Procedures p) (code : Code p)
    (d : RegisterRationalProducts.Procedures p) : Prop where
  dec : ids.dec.Matches code d
  consts : code ids.consts = constsBody ids.dec.cyc.arcs.read
  tableZip : code ids.tableZip = RegisterListZip.body ids.tableZip ids.dec.pairItem
  candItem : code ids.candItem = candItemBody ids.dec.self
  candFlat : code ids.candFlat = RegisterListFlatMap.body ids.candFlat ids.candItem
  self : code ids.self = body ids.tableZip ids.candFlat

theorem tableItem_compiled (code : Code p) (self : Fin p) (hself : code self = pairItemBody)
    {h : Heap} (hh : Valid h) {ip ep dp : Ptr} {i : Bits W} {e : Bits W × Bits W}
    (hi : BitsAt h ip i) (he : EdgeAt h ep e) :
    ∃ out ptr, Extends h out ∧ Valid out ∧ TableAt out ptr (i, e) ∧
      Within code h (initialRegisters [.pointer ip, .pointer ep, .pointer dp]) (code self)
        [.pointer ptr] out 11 := by
  have hea : ep < h.length := by
    obtain ⟨_, _, c, _⟩ := he
    exact List.getElem?_eq_some_iff.mp c |>.1
  obtain ⟨e1, v1, l1⟩ := alloc hh (.pair ip ep) (by
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hi.allocated
    · exact hea)
  refine ⟨_, h.length, e1, v1, ⟨ip, ep, l1, hi.mono e1, he.mono e1⟩, ?_⟩
  rw [hself]
  exact (Within.allocate (h := h) (regs := initialRegisters [.pointer ip, .pointer ep,
      .pointer dp]) (dst := 3)
    (expr := .pair (.register 0) (.register 1)) (c := .pair ip ep)
    (by simp [CellExpr.eval, Atom.eval, initialRegisters, Value.asPointer])
    (by
      simpa [values, Atom.eval] using
        Within.ret code (h ++ [.pair ip ep]) (Function.update (initialRegisters [.pointer ip,
          .pointer ep, .pointer dp]) 3 (.pointer h.length)) [.register 3])).mono
    (by simp [CellExpr.args])

def itemBudget (W N m : ℕ) : ℕ := decomposeBudget W N m m + 12

def budget (W N m : ℕ) : ℕ := 56 * m + 23 + (itemBudget W N m + 27) * m + 50

/-- Word-level statement: the entry procedure computes `candidatesW`. -/
theorem compiled_words (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d) {m : ℕ}
    {h : Heap} (hh : Valid h) {rp ip ep kp : Ptr} {rows : List (List (BinaryRational.Word N))}
    {idx : List (Bits W)} {edges : List (Bits W × Bits W)} {k : Bits N × Bits N × Bits N}
    (hrows : RowsAt h rp rows) (hrl : rows.length = m) (hlen : ∀ xs ∈ rows, xs.length = m)
    (hidx : ListRep (fun heap ptr (w : Bits W) => BitsAt heap ptr w) h ip idx)
    (hes : ListRep EdgeAt h ep edges) (hil : idx.length = m) (hel : edges.length = m)
    (hk : ConstsAt h kp k) :
    ∃ out q, Extends h out ∧ Valid out ∧ IntRowsAt out q (candidatesW k (idx.zip edges) rows) ∧
      Within code h (initialRegisters [.pointer rp, .pointer ip, .pointer ep, .pointer kp])
        (code ids.self) [.pointer q] out (budget W N m) := by
  obtain ⟨m1, tp, e1, v1, htab, run1⟩ := RegisterListZip.compiled_const code ids.tableZip
    ids.dec.pairItem hcode.tableZip (fun heap ptr (w : Bits W) => BitsAt heap ptr w) EdgeAt
    (fun _ _ (_ : Unit) => True) TableAt (fun ext _ _ hx => hx.mono ext)
    (fun ext _ _ hx => hx.mono ext) (fun _ _ _ _ => trivial) (fun ext _ _ hx => hx.mono ext)
    (fun _ hx => hx.allocated) (fun _ i e => (i, e)) 11 hh hidx hes (data := ()) (dataPtr := 0)
    trivial (fun hv _ _ _ _ _ hi he _ => tableItem_compiled code ids.dec.pairItem
      hcode.dec.pairItem hv hi he)
  have htl : (idx.zip edges).length = m := by simp [hil, hel]
  obtain ⟨e2, v2, l2⟩ := alloc v1 (.pair tp kp) (by
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact htab.allocated
    · exact (hk.mono e1).allocated)
  let m2 := m1 ++ [.pair tp kp]
  have hdata : DataAt m2 m1.length (idx.zip edges, k) :=
    ⟨tp, kp, l2, htab.mono e2 (fun _ _ hx => hx.mono e2), (hk.mono e1).mono e2⟩
  have e12 := e1.trans e2
  have hin : ListRep (fun heap ptr (xs : List (BinaryRational.Word N)) =>
      RowAt heap ptr xs ∧ xs.length = m) m2 rp rows := by
    obtain ⟨ps, hl, hr⟩ := hrows
    exact ⟨ps, hl.mono e12, RationalWordRows.forall₂_imp_mem hr
      (fun _ xs _ hxs hx => ⟨hx.mono e12, hlen xs hxs⟩)⟩
  obtain ⟨out, q, e3, v3, hq, run3⟩ := RegisterListFlatMap.compiled code ids.candFlat
    ids.candItem hcode.candFlat
    (fun heap ptr (xs : List (BinaryRational.Word N)) => RowAt heap ptr xs ∧ xs.length = m)
    (fun heap ptr (dt : List (EdgeW W) × (Bits N × Bits N × Bits N)) =>
      DataAt heap ptr dt ∧ dt.1.length = m) IntRowsAt
    (fun ext _ _ hx => ⟨hx.1.mono ext, hx.2⟩) (fun ext _ _ hx => ⟨hx.1.mono ext, hx.2⟩)
    (fun dt xs => decomposeW dt.2 dt.1 xs xs) (itemBudget W N m)
    (fun {h} hv {xp dp acc} {xs} {dt} {tail} hx hdt hacc => by
      obtain ⟨o, r, e, v, hr, w⟩ := decompose_compiled code ids.dec d hcode.dec hdt.2 xs hv
        hx.1 hx.1 hx.2 hdt.1 hacc
      refine ⟨o, r, e, v, hr, ?_⟩
      let r0 := initialRegisters [Value.pointer xp, .pointer dp, .pointer acc]
      have last : Within code o (bindResults r0 [3] [.pointer r]) (.ret [.register 3])
          [.pointer r] o 3 := by
        simpa [bindResults, values, Atom.eval] using
          Within.ret code o (bindResults r0 [3] [.pointer r]) [.register 3]
      have a : values r0 [.register 0, .register 0, .register 1, .register 2] =
          [.pointer xp, .pointer xp, .pointer dp, .pointer acc] := by
        simp [r0, initialRegisters, values, Atom.eval]
      have c := Within.call (procedure := ids.dec.self) (regs := r0) (results := [3])
        (arguments := [.register 0, .register 0, .register 1, .register 2])
        (by simpa only [a] using w) last
      rw [hcode.candItem]
      exact c.mono (by simp only [itemBudget, hx.2, List.length_cons, List.length_nil]; omega))
    v2 hin (data := (idx.zip edges, k)) ⟨hdata, htl⟩
    (RegisterListCommon.listRep_null v2)
  refine ⟨out, q, e12.trans e3, v3, by simpa [candidatesW] using hq, ?_⟩
  let r0 := initialRegisters [Value.pointer rp, .pointer ip, .pointer ep, .pointer kp]
  let r1 := bindResults r0 [4] [Value.pointer tp]
  let r2 := Function.update r1 5 (Value.pointer m1.length)
  let r3 := bindResults r2 [6] [Value.pointer q]
  have last : Within code out r3 (.ret [.register 6]) [.pointer q] out 3 := by
    simpa [r3, bindResults, values, Atom.eval] using Within.ret code out r3 [.register 6]
  have fargs : values r2 [.register 0, .register 5, .null] =
      [.pointer rp, .pointer m1.length, .pointer 0] := by
    simp [r2, r1, r0, bindResults, initialRegisters, values, Atom.eval]
  have fc := Within.call (procedure := ids.candFlat) (regs := r2) (results := [6])
    (arguments := [.register 0, .register 5, .null]) (by simpa only [fargs] using run3) last
  have al := Within.allocate (h := m1) (regs := r1) (dst := 5)
    (expr := .pair (.register 4) (.register 3)) (c := .pair tp kp)
    (by simp [CellExpr.eval, Atom.eval, r1, r0, bindResults, initialRegisters, Value.asPointer])
    fc
  have zargs : values r0 [.register 1, .register 2, .null] =
      [.pointer ip, .pointer ep, .pointer 0] := by
    simp [r0, initialRegisters, values, Atom.eval]
  have zc := Within.call (procedure := ids.tableZip) (regs := r0) (results := [4])
    (arguments := [.register 1, .register 2, .null]) (by simpa only [zargs] using run1) al
  rw [hcode.self]
  refine zc.mono ?_
  simp only [budget, hrl, hil, hel, min_self, CellExpr.args, List.length_cons, List.length_nil]
  omega

/-- The compiled candidate procedure computes `DeterministicKernel.candidates`
exactly, from the stored rational generators, the edge index words and the
edge endpoint words. -/
theorem compiled {n m : ℕ} (left right : Fin m → Fin n) (hn : n < 2 ^ W) (hm : m < 2 ^ W)
    (hN : decomposeWidth n m ≤ N) (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d)
    {h : Heap} (hh : Valid h) {rp ip ep kp : Ptr} {rows : List (List (BinaryRational.Word N))}
    {k : Bits N × Bits N × Bits N} (hk : k.1.value = 0 ∧ k.2.1.value = 1 ∧ k.2.2.value = 2)
    (hrows : RowsAt h rp rows)
    (hrep : List.Forall₂ RationalWordRows.RowRep rows (DeterministicKernel.initial left right))
    (hidx : ListRep (fun heap ptr (w : Bits W) => BitsAt heap ptr w) h ip
      (GraphReachEncoded.rangeWords W m))
    (hes : ListRep EdgeAt h ep (GraphReachEncoded.edgeWords W left right))
    (hK : ConstsAt h kp k) :
    ∃ out q, ∃ gs : List (List (RegisterPotentialStep.Word N)),
      Extends h out ∧ Valid out ∧ IntRowsAt out q gs ∧
      List.Forall₂ IntRowRep gs (DeterministicKernel.candidates left right) ∧
      gs.length ≤ m * m ∧
      Within code h (initialRegisters [.pointer rp, .pointer ip, .pointer ep, .pointer kp])
        (code ids.self) [.pointer q] out (budget W N m) := by
  have hil : (GraphReachEncoded.rangeWords W m).length = m := by
    simp [GraphReachEncoded.rangeWords]
  have hel : (GraphReachEncoded.edgeWords W left right).length = m := by
    simp [GraphReachEncoded.edgeWords]
  have hrl : rows.length = m := by
    rw [hrep.length_eq, DeterministicKernel.initial_eq,
      ComputedKernel.rationalGenerators_length]
  have hlen : ∀ xs ∈ rows, xs.length = m := by
    intro xs hxs
    obtain ⟨x, _, hx⟩ := RationalWordRows.forall₂_mem_left hrep hxs
    exact RationalWordRows.rowRep_length hx
  obtain ⟨out, q, e, v, hq, w⟩ := compiled_words code ids d hcode hh hrows hrl hlen hidx hes hil
    hel hK
  have hcorr := candidatesW_correct hn hm left right k hk hN rows hrep
  rw [← tableW_eq_zip] at hq
  refine ⟨out, q, _, e, v, hq, hcorr, ?_, w⟩
  rw [hcorr.length_eq]
  exact (DeterministicKernel.candidates_spec left right).1

/-! ## Shared magnitude words -/

theorem consts_values {zero one two : BinaryRational.Word N}
    (hz : RationalWordRows.Rep zero 0) (ho : RationalWordRows.Rep one 1)
    (ht : RationalWordRows.Rep two 2) :
    zero.magnitude.value = 0 ∧ one.magnitude.value = 1 ∧ two.magnitude.value = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hz.2.2.1, hz.1]; rfl
  · rw [ho.2.2.1, ho.1]; rfl
  · rw [ht.2.2.1, ht.1]; rfl

theorem consts_compiled (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d)
    {h : Heap} (hh : Valid h) {zp op tp : Ptr} {zero one two : BinaryRational.Word N}
    (hz : At h zp zero) (ho : At h op one) (ht : At h tp two) :
    ∃ out q, Extends h out ∧ Valid out ∧
      ConstsAt out q (zero.magnitude, one.magnitude, two.magnitude) ∧
      Within code h (initialRegisters [.pointer zp, .pointer op, .pointer tp]) (code ids.consts)
        [.pointer q] out 109 := by
  have hread := hcode.dec.cyc.arcs.read
  obtain ⟨zn, zd, hzn, -, rz⟩ := StoredRational.read_compiled code hz
  obtain ⟨on, od, hon, -, ro⟩ := StoredRational.read_compiled code ho
  obtain ⟨tn, td, htn, -, rt⟩ := StoredRational.read_compiled code ht
  obtain ⟨e1, v1, l1⟩ := alloc hh (.pair zn tn) (by
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hzn.allocated
    · exact htn.allocated)
  let h1 := h ++ [.pair zn tn]
  obtain ⟨e2, v2, l2⟩ := alloc v1 (.pair on h.length) (by
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact (hon.mono e1).allocated
    · simp)
  refine ⟨h1 ++ [.pair on h.length], h1.length, e1.trans e2, v2,
    ⟨on, h.length, zn, tn, l2, e2.lookup l1, (hzn.mono e1).mono e2, (hon.mono e1).mono e2,
      (htn.mono e1).mono e2⟩, ?_⟩
  let r0 := initialRegisters [Value.pointer zp, .pointer op, .pointer tp]
  let r1 := bindResults r0 [3, 4, 5] [Value.flag zero.negative, .pointer zn, .pointer zd]
  let r2 := bindResults r1 [6, 7, 8] [Value.flag one.negative, .pointer on, .pointer od]
  let r3 := bindResults r2 [9, 10, 11] [Value.flag two.negative, .pointer tn, .pointer td]
  let r4 := Function.update r3 12 (Value.pointer h.length)
  have last := RegisterListCommon.within_consRet code h1 (regs := r4) (dst := 13) (head := 7)
    (tail := 12) (a := on) (t := h.length)
    (by simp [r4, r3, r2, bindResults]) (by simp [r4])
  have last' : Within code h1 r4 (.allocate 13 (.pair (.register 7) (.register 12))
      (.ret [.register 13])) [.pointer h1.length] (h1 ++ [.pair on h.length]) 11 := by
    apply Within.allocate (budget := 3) (c := .pair on h.length)
    · simp [CellExpr.eval, Atom.eval, r4, r3, r2, bindResults, Value.asPointer]
    · simpa [values, Atom.eval] using
        Within.ret code (h1 ++ [.pair on h.length]) (Function.update r4 13 (.pointer h1.length))
          [.register 13]
  clear last
  have al := Within.allocate (h := h) (regs := r3) (dst := 12)
    (expr := .pair (.register 4) (.register 10)) (c := .pair zn tn)
    (by simp [CellExpr.eval, Atom.eval, r3, r2, r1, bindResults, Value.asPointer]) last'
  have c3 := Within.call (procedure := ids.dec.cyc.arcs.read) (regs := r2) (results := [9, 10, 11])
    (arguments := [.register 2]) (by
      have a : values r2 [.register 2] = [.pointer tp] := by
        simp [r2, r1, r0, bindResults, initialRegisters, values, Atom.eval]
      simpa only [a, hread] using rt) al
  have c2 := Within.call (procedure := ids.dec.cyc.arcs.read) (regs := r1) (results := [6, 7, 8])
    (arguments := [.register 1]) (by
      have a : values r1 [.register 1] = [.pointer op] := by
        simp [r1, r0, bindResults, initialRegisters, values, Atom.eval]
      simpa only [a, hread] using ro) c3
  have c1 := Within.call (procedure := ids.dec.cyc.arcs.read) (regs := r0) (results := [3, 4, 5])
    (arguments := [.register 0]) (by
      have a : values r0 [.register 0] = [.pointer zp] := by
        simp [r0, initialRegisters, values, Atom.eval]
      simpa only [a, hread] using rz) c2
  rw [hcode.consts]
  exact c1.mono (by simp [CellExpr.args])

/-- The event bound is an explicit polynomial: degree six in the combined size. -/
theorem budget_le (W N m : ℕ) : budget W N m ≤ 20000 * (W + N + m + 1) ^ 6 := by
  set s := W + N + m + 1 with hs
  have hW : W ≤ s := by omega
  have hN : N + 1 ≤ s := by omega
  have hm : m + 1 ≤ s := by omega
  have h1 : 1 ≤ s := by omega
  have p12 : s ≤ s ^ 2 := by nlinarith
  have p23 : s ^ 2 ≤ s ^ 3 := by nlinarith [pow_two s, pow_succ s 2]
  have p34 : s ^ 3 ≤ s ^ 4 := by nlinarith [pow_succ s 3]
  have p45 : s ^ 4 ≤ s ^ 5 := by nlinarith [pow_succ s 4]
  have p56 : s ^ 5 ≤ s ^ 6 := by nlinarith [pow_succ s 5]
  have hp : predBudget W ≤ 156 * s := by unfold predBudget; omega
  have hsc : RegisterStoredRational.scalarBudget N ≤ 3300 * s ^ 3 := by
    unfold RegisterStoredRational.scalarBudget
    gcongr
  have hss : RegisterRationalProject.scaleSubBudget N m ≤ 6700 * s ^ 4 := by
    unfold RegisterRationalProject.scaleSubBudget
    calc (2 * RegisterStoredRational.scalarBudget N + 50) * m + 23
        ≤ (2 * (3300 * s ^ 3) + 50) * s + 23 := by gcongr; omega
      _ = 6600 * s ^ 4 + 50 * s + 23 := by ring
      _ ≤ 6700 * s ^ 4 := by nlinarith
  have hpairs : pairsBudget N m ≤ 500 * s ^ 2 := by
    unfold pairsBudget arcPairBudget
    calc (60 * N + 300 + 45) * m + 23 ≤ (405 * s) * s + 23 := by gcongr <;> omega
      _ ≤ 500 * s ^ 2 := by nlinarith
  have hstep : RegisterSupportCycle.stepBudget W (2 * m) (2 * m + 1) ≤ 2000 * s ^ 2 := by
    unfold RegisterSupportCycle.stepBudget
    calc (2 * predBudget W + 70) * (2 * m + 1 + 2 * m) + 120
        ≤ (2 * (156 * s) + 70 * s) * (4 * s) + 120 * s ^ 2 := by gcongr <;> nlinarith
      _ ≤ 2000 * s ^ 2 := by nlinarith
  have hcyc : RegisterSupportCycle.cycleBudget W (2 * m) ≤ 4200 * s ^ 3 := by
    unfold RegisterSupportCycle.cycleBudget RegisterSupportCycle.searchBudget
    calc 43 * (2 * m) + ((2 * m + 1) * RegisterSupportCycle.stepBudget W (2 * m) (2 * m + 1) + 13) + 60
        ≤ 86 * s + ((2 * s) * (2000 * s ^ 2) + 13) + 60 := by
          have := Nat.mul_le_mul (show 2 * m + 1 ≤ 2 * s by omega) hstep
          omega
      _ = 4000 * s ^ 3 + 86 * s + 73 := by ring
      _ ≤ 4200 * s ^ 3 := by nlinarith
  have hgen : (genBudget W (2 * m + 1) + 35) * m ≤ 1200 * s ^ 3 := by
    unfold genBudget
    calc ((2 * predBudget W + 60) * (2 * m + 1) + 150 + 35) * m
        ≤ ((2 * (156 * s) + 60 * s) * (2 * s) + 185 * s ^ 2) * s := by gcongr <;> nlinarith
      _ = 929 * s ^ 3 := by ring
      _ ≤ 1200 * s ^ 3 := by omega
  have hpiv : (pivotBudget N + 30) * m ≤ 200 * s ^ 2 := by
    unfold pivotBudget
    calc (60 * N + 100 + 30) * m ≤ (190 * s) * s := by gcongr <;> omega
      _ = 190 * s ^ 2 := by ring
      _ ≤ 200 * s ^ 2 := by omega
  have hround : roundBudget W N m ≤ 17000 * s ^ 4 := by
    unfold roundBudget
    have ha : arcsBudget m ≤ 69 * s := by unfold arcsBudget; omega
    have h46 : 46 * m + 56 * m ≤ 102 * s := by omega
    have h14 : 1 ≤ s ^ 4 := by omega
    linarith
  have hitem : itemBudget W N m ≤ 17100 * s ^ 5 := by
    unfold itemBudget decomposeBudget
    calc m * roundBudget W N m + 13 + 12 ≤ s * (17000 * s ^ 4) + 25 := by
          have := Nat.mul_le_mul (show m ≤ s by omega) hround
          omega
      _ = 17000 * s ^ 5 + 25 := by ring
      _ ≤ 17100 * s ^ 5 := by omega
  unfold budget
  calc 56 * m + 23 + (itemBudget W N m + 27) * m + 50
      ≤ 56 * s + 23 + (17100 * s ^ 5 + 27) * s + 50 := by gcongr <;> omega
    _ = 17100 * s ^ 6 + 83 * s + 73 := by ring
    _ ≤ 20000 * s ^ 6 := by omega

end WeightedMIS.RegisterCandidates
