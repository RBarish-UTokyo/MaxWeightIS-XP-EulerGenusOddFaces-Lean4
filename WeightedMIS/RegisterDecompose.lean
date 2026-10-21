module

public import WeightedMIS.RegisterGeneratorWords

/-!
# Compiled deterministic support decomposition

One round on a stored rational row `xs` builds the arc pairs and arcs of the
signed support graph, finds the support cycle, and maps every edge pair to its
signed generator word (magnitude chosen among the shared words `0`, `1`, `2`
by cycle membership of both orientations, sign taken from the source state).
The generator words are viewed as rationals with the shared denominator `1`
(one `pair` cell per coordinate, `intRow`). The first coordinate whose
generator word is nonzero is the pivot; the residual `xs - (x_e / g_e) g` is
computed with the compiled division and `scaleSub`. The round emits the
generator row and recurses on the residual with one fuel item less.

Integer rows are represented as `SignedWords.ListAt`: lists of signed words
`(negative, magnitude)` of width `N`, each denoting
`RegisterPotentialStep.value`. The compiled procedure computes exactly
`SupportCycleWords.decomposeW`, prepended to an accumulator.
-/

@[expose] public section

namespace WeightedMIS.RegisterDecompose

open PointerMemory RegisterMachine EfficientSearch EfficientSearch.Pointer StoredRational
open SupportCycleWords RegisterSupportArcs RegisterSupportCycle RegisterGeneratorWords
open RegisterRationalRow (RowAt)
open SignedWords (SignedAt)

variable {p W N : ℕ}

/-! ## The decomposition rounds -/

structure Procedures (p : ℕ) where
  cyc : RegisterSupportCycle.Procedures p
  rat : RegisterRationalProject.Procedures p
  genItem : Fin p
  genMap : Fin p
  ratItem : Fin p
  ratMap : Fin p
  pairItem : Fin p
  zipXG : Fin p
  pivotTest : Fin p
  pivotFind : Fin p
  self : Fin p

/-- Pivot found at the pair in register 10: residual and recursion. -/
def decTail (ids : Procedures p) : Command p :=
  .call ids.rat.divide [.register 11, .register 13] [14]
    (.call ids.rat.scaleSub [.register 1, .register 4, .register 14] [6]
      (.call ids.self [.register 5, .register 6, .register 2, .register 3] [7]
        (.allocate 8 (.cons (.register 12) (.register 7)) (.ret [.register 8]))))

def decPivot (ids : Procedures p) : Command p :=
  .load (.register 10) 11 13 15 { CompiledTrie.failCases with pair := decTail ids }

def decAfter (ids : Procedures p) : Command p :=
  .call ids.ratMap [.register 12, .register 13] [4]
    (.call ids.zipXG [.register 1, .register 4, .null] [6]
      (.call ids.pivotFind [.register 6, .null] [9, 10]
        (.branch (.register 9) (decPivot ids) (.ret [.register 3]))))

def decRound (ids : Procedures p) : Command p :=
  RegisterPairReads.readPairs [(2, 6, 7)]
    (.call ids.cyc.arcs.zipArcs [.register 1, .register 6, .null] [8]
      (.call ids.cyc.arcs.flatArcs [.register 8, .null, .null] [9]
        (.call ids.cyc.cycle [.register 9] [10]
          (.allocate 11 (.pair (.register 10) (.register 7))
            (.call ids.genMap [.register 8, .register 11] [12]
              (.load (.register 7) 13 14 15 { CompiledTrie.failCases with
                pair := decAfter ids }))))))

/-- Arguments 0=fuel row, 1=current row, 2=data `.pair edgeTable consts`,
3=accumulator of integer rows. -/
def decomposeBody (ids : Procedures p) : Command p :=
  .load (.register 0) 4 5 15 { CompiledTrie.failCases with
    nil := .ret [.register 3]
    cons := decRound ids }

structure Procedures.Matches (ids : Procedures p) (code : Code p)
    (d : RegisterRationalProducts.Procedures p) : Prop where
  cyc : ids.cyc.Matches code
  rat : ids.rat.Matches code d
  genItem : code ids.genItem = genItemBody ids.cyc.memFind
  genMap : code ids.genMap = RegisterListMap.body ids.genMap ids.genItem
  ratItem : code ids.ratItem = ratItemBody
  ratMap : code ids.ratMap = RegisterListMap.body ids.ratMap ids.ratItem
  pairItem : code ids.pairItem = pairItemBody
  zipXG : code ids.zipXG = RegisterListZip.body ids.zipXG ids.pairItem
  pivotTest : code ids.pivotTest = pivotTestBody ids.cyc.arcs.zeroTest
  pivotFind : code ids.pivotFind = RegisterListFind.body ids.pivotFind ids.pivotTest
  self : code ids.self = decomposeBody ids

def roundBudget (W N m : ℕ) : ℕ :=
  pairsBudget N m + arcsBudget m + cycleBudget W (2 * m) + (genBudget W (2 * m + 1) + 35) * m +
    46 * m + 56 * m + (pivotBudget N + 30) * m + RegisterStoredRational.scalarBudget N +
    RegisterRationalProject.scaleSubBudget N m + 400

def decomposeBudget (W N m F : ℕ) : ℕ := F * roundBudget W N m + 13

theorem genBudget_mono (W : ℕ) {a b : ℕ} (h : a ≤ b) : genBudget W a ≤ genBudget W b := by
  unfold genBudget
  have := Nat.mul_le_mul_left (2 * predBudget W + 60) h
  omega

theorem budget_none (m P1 P2 P3 P4 P5 P6 P7 F : ℕ) :
    10 + (10 * 1 + (1 + 2 * 3 + P1 + (1 + 2 * 3 + P2 + (1 + 2 * 1 + P3 + (4 + 2 * 2 +
      (1 + 2 * 2 + (P4 + 13) + (10 + (1 + 2 * 2 + (46 * m + 13) + (1 + 2 * 3 + ((11 + 45) * m + 23) +
      (1 + 2 * 2 + (P5 + 15) + (3 + 3))))))))))) ≤
    (F + 1) * (P1 + P2 + P3 + P4 + 46 * m + 56 * m + P5 + P6 + P7 + 400) + 13 := by
  have h : (F + 1) * (P1 + P2 + P3 + P4 + 46 * m + 56 * m + P5 + P6 + P7 + 400) =
      F * (P1 + P2 + P3 + P4 + 46 * m + 56 * m + P5 + P6 + P7 + 400) +
        (P1 + P2 + P3 + P4 + 46 * m + 56 * m + P5 + P6 + P7 + 400) := Nat.add_one_mul _ _
  rw [h]
  omega

theorem budget_pivot (m P1 P2 P3 P4 P5 P6 P7 F : ℕ) :
    10 + (10 * 1 + (1 + 2 * 3 + P1 + (1 + 2 * 3 + P2 + (1 + 2 * 1 + P3 + (4 + 2 * 2 +
      (1 + 2 * 2 + (P4 + 13) + (10 + (1 + 2 * 2 + (46 * m + 13) + (1 + 2 * 3 + ((11 + 45) * m + 23) +
      (1 + 2 * 2 + (P5 + 15) + (3 + (10 + (1 + 2 * (0 + 1 + 1) + P6 + (1 + 2 * (0 + 1 + 1 + 1) + P7 +
      (1 + 2 * (0 + 1 + 1 + 1 + 1) +
        (F * (P1 + P2 + P3 + P4 + 46 * m + 56 * m + P5 + P6 + P7 + 400) + 13) + 11))))))))))))))) ≤
    (F + 1) * (P1 + P2 + P3 + P4 + 46 * m + 56 * m + P5 + P6 + P7 + 400) + 13 := by
  have h : (F + 1) * (P1 + P2 + P3 + P4 + 46 * m + 56 * m + P5 + P6 + P7 + 400) =
      F * (P1 + P2 + P3 + P4 + 46 * m + 56 * m + P5 + P6 + P7 + 400) +
        (P1 + P2 + P3 + P4 + 46 * m + 56 * m + P5 + P6 + P7 + 400) := Nat.add_one_mul _ _
  rw [h]
  omega

theorem decompose_compiled (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d) {m : ℕ}
    {k : Bits N × Bits N × Bits N} {table : List (EdgeW W)} (htl : table.length = m) :
    ∀ (fuel : List (BinaryRational.Word N)) {h : Heap}, Valid h → ∀ {fp xp dp ap : Ptr}
      {xs : List (BinaryRational.Word N)} {acc : List (List (RegisterPotentialStep.Word N))},
      RowAt h fp fuel → RowAt h xp xs → xs.length = m → DataAt h dp (table, k) →
      IntRowsAt h ap acc →
      ∃ out q, Extends h out ∧ Valid out ∧ IntRowsAt out q (decomposeW k table fuel xs ++ acc) ∧
        Within code h (initialRegisters [.pointer fp, .pointer xp, .pointer dp, .pointer ap])
          (code ids.self) [.pointer q] out (decomposeBudget W N m fuel.length)
  | [], h, hh, fp, xp, dp, ap, xs, acc, hf, _, _, _, ha => by
    obtain ⟨ps, hlist, hrel⟩ := hf
    cases hrel
    cases hlist with
    | nil cell =>
      refine ⟨h, ap, .refl h, hh, by simpa [decomposeW] using ha, ?_⟩
      rw [hcode.self]
      apply Within.mono (a := 13) _ (by simp [decomposeBudget])
      apply Within.load (budget := 3) (pointer := fp) (c := .nil)
      · simp [Atom.eval, initialRegisters]
      · exact cell
      · simpa [values, Atom.eval, Cases.select, initialRegisters, loadRegisters, decoded] using
          Within.ret code h (loadRegisters (initialRegisters [.pointer fp, .pointer xp,
            .pointer dp, .pointer ap]) 4 5 15 .nil) [.register 3]
  | f :: fuel, h, hh, fp, xp, dp, ap, xs, acc, hf, hx, hxl, hd, ha => by
    obtain ⟨ps, hlist, hrel⟩ := hf
    cases hrel with
    | @cons fh _ ps _ _ hft =>
    cases hlist with
    | @cons _ _ ft _ fcell frest =>
    obtain ⟨tp, kp, dcell, htab, hk⟩ := id hd
    obtain ⟨op, r, zp, twp, kc1, kc2, hz, ho, htw⟩ := id hk
    let pairs := pairsW xs table
    let C := cycleW (arcsW pairs)
    let gs := pairs.map (genW k C)
    let gq := gs.map (ratW k.2.1)
    have hpl : pairs.length = m := by simp [pairs, pairsW_length, hxl, htl]
    have hal : (arcsW pairs).length = 2 * m := by rw [arcsW_length, hpl]
    have hCl : C.length ≤ 2 * m + 1 := by
      have := cycleW_length (arcsW pairs)
      show (cycleW (arcsW pairs)).length ≤ 2 * m + 1
      omega
    have hgsl : gs.length = m := by simp [gs, hpl]
    have hgql : gq.length = m := by simp [gq, hgsl]
    -- arc pairs, arcs and cycle
    obtain ⟨m1, q1, e1, v1, hpairs, run1⟩ :=
      pairs_compiled code ids.cyc.arcs hcode.cyc.arcs hh hx htab
    obtain ⟨m2, q2, e2, v2, harcs, run2⟩ :=
      arcs_compiled code ids.cyc.arcs hcode.cyc.arcs v1 hpairs
    obtain ⟨m3, q3, e3, v3, hC, run3⟩ := cycle_compiled code ids.cyc hcode.cyc v2 harcs
    have e13 := e1.trans (e2.trans e3)
    obtain ⟨e4, v4, l4⟩ := alloc v3 (.pair q3 kp) (by
      intro q hq
      simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hC.allocated
      · exact (hk.mono e13).allocated)
    let m4 := m3 ++ [.pair q3 kp]
    have hgd : GenDataAt m4 m3.length (C, k) :=
      ⟨q3, kp, l4, hC.mono e4 (fun _ _ hx => hx.mono e4), (hk.mono e13).mono e4⟩
    -- generator words
    have e24 := e2.trans (e3.trans e4)
    obtain ⟨m5, q5, e5, v5, hgs, run5⟩ := RegisterListMap.compiled_const code ids.genMap
      ids.genItem hcode.genMap PairAt GenDataAt SignedAt (fun ext _ _ hx => hx.mono ext)
      (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext)
      (fun _ hx => hx.allocated) (fun d pr => genW d.2 d.1 pr) (genBudget W (2 * m + 1)) v4
      (hpairs.mono e24 (fun _ _ hx => hx.mono e24)) hgd
      (fun hv _ _ _ hp hd' => by
        obtain ⟨o, q, e, v, hq, w⟩ := genItem_compiled code ids.cyc hcode.cyc ids.genItem
          hcode.genItem hv hp hd'
        exact ⟨o, q, e, v, hq, w.mono (genBudget_mono W hCl)⟩)
    have e15 := e13.trans (e4.trans e5)
    -- rational view of the generator
    obtain ⟨m6, q6, e6, v6, hgq, run6⟩ := intRow_compiled code ids.ratMap ids.ratItem
      hcode.ratMap hcode.ratItem v5 hgs (ho.mono e15)
    have e16 := e15.trans e6
    -- coordinate pairs and pivot search
    obtain ⟨m7, q7, e7, v7, hxg, run7⟩ := RegisterListZip.compiled_const code ids.zipXG
      ids.pairItem hcode.zipXG (fun heap ptr (x : BinaryRational.Word N) => At heap ptr x)
      (fun heap ptr (x : BinaryRational.Word N) => At heap ptr x) (fun _ _ (_ : Unit) => True)
      PairWAt (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext)
      (fun _ _ _ _ => trivial) (fun ext _ _ hx => hx.mono ext)
      (fun _ hx => by obtain ⟨_, _, c, _⟩ := hx; exact List.getElem?_eq_some_iff.mp c |>.1)
      (fun _ x g => (x, g)) 11 v6 (hx.mono e16) hgq
      (data := ()) (dataPtr := 0) trivial
      (fun hv _ _ _ _ _ hxa hga _ => pairItem_compiled code ids.pairItem hcode.pairItem hv hxa hga)
    obtain ⟨m8, q8, e8, v8, hfound, -, run8⟩ := RegisterListFind.compiled_const code
      ids.pivotFind ids.pivotTest hcode.pivotFind PairWAt (fun _ _ (_ : Unit) => True)
      (fun ext _ _ hx => hx.mono ext) (fun _ _ _ _ => trivial) (fun _ pr => pivotPred pr)
      (pivotBudget N) v7 hxg (data := ()) (dataPtr := 0) trivial
      (fun hv _ _ _ hp _ => pivotTest_compiled code ids.cyc.arcs hcode.cyc.arcs ids.pivotTest
        hcode.pivotTest hv hp)
    have e18 := e16.trans (e7.trans e8)
    let xg := List.zipWith Prod.mk xs gq
    have hxgl : xg.length = m := by simp [xg, hxl, hgql]
    let found := (xg.find? pivotPred).isSome
    -- register files of the common prefix
    let r0 := initialRegisters [Value.pointer fp, .pointer xp, .pointer dp, .pointer ap]
    let r1 := loadRegisters r0 4 5 15 (.cons fh ft)
    let r2 := loadRegisters r1 6 7 15 (.pair tp kp)
    let r3 := bindResults r2 [8] [Value.pointer q1]
    let r4 := bindResults r3 [9] [Value.pointer q2]
    let r5 := bindResults r4 [10] [Value.pointer q3]
    let r6 := Function.update r5 11 (Value.pointer m3.length)
    let r7 := bindResults r6 [12] [Value.pointer q5]
    let r8 := loadRegisters r7 13 14 15 (.pair op r)
    let r9 := bindResults r8 [4] [Value.pointer q6]
    let r10 := bindResults r9 [6] [Value.pointer q7]
    let r11 := bindResults r10 [9, 10] [Value.flag found, .pointer q8]
    have hpre : ∀ {o : List Value} {outH : Heap} {B : ℕ},
        Within code m8 r11 (.branch (.register 9) (decPivot ids) (.ret [.register 3])) o outH B →
        Within code h r0 (code ids.self) o outH
          (10 + (10 * 1 + (1 + 2 * 3 + pairsBudget N (min xs.length table.length) +
            (1 + 2 * 3 + arcsBudget pairs.length + (1 + 2 * 1 + cycleBudget W (arcsW pairs).length +
            (4 + 2 * 2 + (1 + 2 * 2 + ((genBudget W (2 * m + 1) + 35) * pairs.length + 13) +
            (10 + (1 + 2 * 2 + (46 * gs.length + 13) +
            (1 + 2 * 3 + ((11 + 45) * min xs.length gq.length + 23) +
            (1 + 2 * 2 + ((pivotBudget N + 30) * xg.length + 15) + B))))))))))) := by
      intro o outH B rest
      have c8 := Within.call (procedure := ids.pivotFind) (regs := r10) (results := [9, 10])
        (arguments := [.register 6, .null]) (by
          have a : values r10 [.register 6, .null] = [.pointer q7, .pointer 0] := by
            simp [r10, bindResults, values, Atom.eval]
          simpa only [a] using run8) rest
      have c7 := Within.call (procedure := ids.zipXG) (regs := r9) (results := [6])
        (arguments := [.register 1, .register 4, .null]) (by
          have a : values r9 [.register 1, .register 4, .null] =
              [.pointer xp, .pointer q6, .pointer 0] := by
            simp [r9, r8, r7, r6, r5, r4, r3, r2, r1, r0, bindResults, loadRegisters, decoded,
              initialRegisters, values, Atom.eval]
          simpa only [a] using run7) c8
      have c6 := Within.call (procedure := ids.ratMap) (regs := r8) (results := [4])
        (arguments := [.register 12, .register 13]) (by
          have a : values r8 [.register 12, .register 13] = [.pointer q5, .pointer op] := by
            simp [r8, r7, bindResults, loadRegisters, decoded, values, Atom.eval]
          simpa only [a] using run6) c7
      have l8 := Within.load (address := .register 7) (first := 13) (second := 14) (bit := 15)
        (branches := { CompiledTrie.failCases with pair := decAfter ids })
        (by simp [Atom.eval, r7, r6, r5, r4, r3, r2, bindResults, loadRegisters, decoded])
        ((e4.trans e5).lookup (e13.lookup kc1)) c6
      have c5 := Within.call (procedure := ids.genMap) (regs := r6) (results := [12])
        (arguments := [.register 8, .register 11]) (by
          have a : values r6 [.register 8, .register 11] = [.pointer q1, .pointer m3.length] := by
            simp [r6, r5, r4, r3, bindResults, values, Atom.eval]
          simpa only [a] using run5) l8
      have a4 := Within.allocate (h := m3) (regs := r5) (dst := 11)
        (expr := .pair (.register 10) (.register 7)) (c := .pair q3 kp)
        (by simp [CellExpr.eval, Atom.eval, r5, r4, r3, r2, bindResults, loadRegisters, decoded,
          Value.asPointer]) c5
      have c3 := Within.call (procedure := ids.cyc.cycle) (regs := r4) (results := [10])
        (arguments := [.register 9]) (by
          have a : values r4 [.register 9] = [.pointer q2] := by
            simp [r4, bindResults, values, Atom.eval]
          simpa only [a] using run3) a4
      have c2 := Within.call (procedure := ids.cyc.arcs.flatArcs) (regs := r3) (results := [9])
        (arguments := [.register 8, .null, .null]) (by
          have a : values r3 [.register 8, .null, .null] =
              [.pointer q1, .pointer 0, .pointer 0] := by
            simp [r3, bindResults, values, Atom.eval]
          simpa only [a] using run2) c3
      have c1 := Within.call (procedure := ids.cyc.arcs.zipArcs) (regs := r2) (results := [8])
        (arguments := [.register 1, .register 6, .null]) (by
          have a : values r2 [.register 1, .register 6, .null] =
              [.pointer xp, .pointer tp, .pointer 0] := by
            simp [r2, r1, r0, loadRegisters, decoded, initialRegisters, values, Atom.eval]
          simpa only [a] using run1) c2
      have reads : RegisterPairReads.Reads h r1 [(2, 6, 7)] r2 :=
        .cons (ptr := dp) (by simp [r1, r0, loadRegisters, decoded, initialRegisters]) dcell
          (.nil _)
      have l0 := Within.load (address := .register 0) (first := 4) (second := 5) (bit := 15)
        (branches := { CompiledTrie.failCases with nil := .ret [.register 3], cons := decRound ids })
        (by simp [Atom.eval, r0, initialRegisters]) fcell (reads.within c1)
      rw [hcode.self]
      exact l0
    have h9 : (Atom.register 9).eval r11 = .flag found := by simp [r11, bindResults, Atom.eval]
    have hdec : decomposeW k table (f :: fuel) xs =
        match xg.find? pivotPred with
        | none => []
        | some pr => gs :: decomposeW k table fuel
            (RationalWordRows.scaleSubW (BinaryRational.divide pr.1 pr.2).1 xs gq) := rfl
    rcases hfp : xg.find? pivotPred with _ | pr
    · -- no pivot: return the accumulator
      have hnf : found = false := by simp [found, hfp]
      refine ⟨m8, ap, e18, v8, by
        rw [hdec, hfp]
        exact ha.mono e18, ?_⟩
      have last : Within code m8 r11 (.ret [.register 3]) [.pointer ap] m8 3 := by
        simpa [r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, r0, bindResults, loadRegisters,
          decoded, initialRegisters, values, Atom.eval] using Within.ret code m8 r11 [.register 3]
      have br := Within.branch (b := false) (test := .register 9) (regs := r11)
        (yes := decPivot ids) (by rw [h9, hnf]) (by simpa using last)
      refine (hpre br).mono ?_
      simp only [decomposeBudget, roundBudget, List.length_cons, hpl, hal, hgsl, hgql, hxgl, hxl,
        htl, min_self]
      generalize pairsBudget N m = P1
      generalize arcsBudget m = P2
      generalize cycleBudget W (2 * m) = P3
      generalize (genBudget W (2 * m + 1) + 35) * m = P4
      generalize (pivotBudget N + 30) * m = P5
      generalize RegisterStoredRational.scalarBudget N = P6
      generalize RegisterRationalProject.scaleSubBudget N m = P7
      generalize fuel.length = F
      exact budget_none m P1 P2 P3 P4 P5 P6 P7 F
    · -- pivot found: residual and recursion
      have hf' : found = true := by simp [found, hfp]
      have hpr : PairWAt m8 q8 pr := hfound pr hfp
      obtain ⟨xe, ge, pcell, hxe, hge⟩ := hpr
      obtain ⟨m9, q9, e9, v9, hcoef, run9⟩ :=
        RegisterRationalProject.divide_compiled code ids.rat d hcode.rat v8 hxe hge
      have e19 := e18.trans e9
      obtain ⟨m10, q10, e10, v10, hres, run10⟩ := RegisterRationalProject.scaleSub_compiled code
        ids.rat d hcode.rat v9 (hx.mono e19) (hgq.mono (e7.trans (e8.trans e9)))
        hcoef
      have e110 := e19.trans e10
      have hresl :
          (RationalWordRows.scaleSubW (BinaryRational.divide pr.1 pr.2).1 xs gq).length = m := by
        rw [RationalWordRows.scaleSubW_length, hxl, hgql, min_self]
      obtain ⟨m11, q11, e11, v11, hrec, run11⟩ := decompose_compiled code ids d hcode htl fuel v10
        ⟨ps, frest.mono e110, hft.imp (fun _ _ hx => hx.mono e110)⟩ hres hresl (hd.mono e110)
        (ha.mono e110)
      have e511 := (e6.trans (e7.trans (e8.trans (e9.trans (e10.trans e11)))))
      obtain ⟨e12, v12, hout⟩ := RegisterListCommon.allocate_consRep
        (R := SignedWords.ListAt) (fun ext _ _ hx => hx.mono ext) v11 (hgs.mono e511
          (fun _ _ hx => hx.mono e511)) (hgs.mono e511 (fun _ _ hx => hx.mono e511)).allocated hrec
      refine ⟨_, _, e110.trans (e11.trans e12), v12, by
        rw [hdec, hfp]
        exact hout, ?_⟩
      let r12 := loadRegisters r11 11 13 15 (.pair xe ge)
      let r13 := bindResults r12 [14] [Value.pointer q9]
      let r14 := bindResults r13 [6] [Value.pointer q10]
      let r15 := bindResults r14 [7] [Value.pointer q11]
      have last := RegisterListCommon.within_consRet code m11 (regs := r15) (dst := 8)
        (head := 12) (tail := 7) (a := q5) (t := q11)
        (by simp [r15, r14, r13, r12, r11, r10, r9, r8, r7, bindResults, loadRegisters, decoded])
        (by simp [r15, bindResults])
      have c11 := Within.call (procedure := ids.self) (regs := r14) (results := [7])
        (arguments := [.register 5, .register 6, .register 2, .register 3]) (by
          have a : values r14 [.register 5, .register 6, .register 2, .register 3] =
              [.pointer ft, .pointer q10, .pointer dp, .pointer ap] := by
            simp [r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, r0, bindResults,
              loadRegisters, decoded, initialRegisters, values, Atom.eval]
          simpa only [a] using run11) last
      have c10 := Within.call (procedure := ids.rat.scaleSub) (regs := r13) (results := [6])
        (arguments := [.register 1, .register 4, .register 14]) (by
          have a : values r13 [.register 1, .register 4, .register 14] =
              [.pointer xp, .pointer q6, .pointer q9] := by
            simp [r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, r0, bindResults,
              loadRegisters, decoded, initialRegisters, values, Atom.eval]
          simpa only [a, hcode.rat.scaleSub] using run10) c11
      have c9 := Within.call (procedure := ids.rat.divide) (regs := r12) (results := [14])
        (arguments := [.register 11, .register 13]) (by
          have a : values r12 [.register 11, .register 13] = [.pointer xe, .pointer ge] := by
            simp [r12, loadRegisters, decoded, values, Atom.eval]
          simpa only [a] using run9) c10
      have l9 := Within.load (address := .register 10) (first := 11) (second := 13) (bit := 15)
        (branches := { CompiledTrie.failCases with pair := decTail ids })
        (by simp [Atom.eval, r11, bindResults]) pcell c9
      have br := Within.branch (b := true) (test := .register 9) (regs := r11)
        (no := .ret [.register 3]) (by rw [h9, hf']) l9
      refine (hpre br).mono ?_
      simp only [decomposeBudget, roundBudget, List.length_cons, hpl, hal, hgsl, hgql, hxgl, hxl,
        htl, min_self, List.length_nil]
      generalize pairsBudget N m = P1
      generalize arcsBudget m = P2
      generalize cycleBudget W (2 * m) = P3
      generalize (genBudget W (2 * m + 1) + 35) * m = P4
      generalize (pivotBudget N + 30) * m = P5
      generalize RegisterStoredRational.scalarBudget N = P6
      generalize RegisterRationalProject.scaleSubBudget N m = P7
      generalize fuel.length = F
      exact budget_pivot m P1 P2 P3 P4 P5 P6 P7 F

end WeightedMIS.RegisterDecompose
