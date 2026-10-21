module

public import WeightedMIS.RegisterSupportArcs
public import WeightedMIS.RegisterListFind

/-!
# Compiled support-cycle search

`search` consumes one fuel item per step. It first searches the reversed list
of visited arcs for the current arc (comparator equality of keys). On a hit it
returns the current arc followed by the visited arcs before its first
occurrence (`takeUntil`). Otherwise it reads the target state of the current
arc, searches the arc list for the first active arc starting at that state
(falling back to the current arc), prepends the current arc to the visited
list and recurses. `cycle` starts at the first active arc with fuel
`a :: arcs`. Both procedures compute exactly `SupportCycleWords.searchW` and
`SupportCycleWords.cycleW`.
-/

@[expose] public section

namespace WeightedMIS.RegisterSupportCycle

open PointerMemory RegisterMachine EfficientSearch EfficientSearch.Pointer
open SupportCycleWords RegisterSupportArcs

variable {p W : ℕ}

/-! ## Visited prefix before a repeated arc -/

/-- Arguments 0=arc list, 1=arc `a`; the result is the prefix of arcs different from `a`. -/
def takeUntilBody (self same : Fin p) : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := .call same [.register 2, .register 1] [4]
      (.branch (.register 4) (.ret [.null])
        (.call self [.register 3, .register 1] [5]
          (.allocate 6 (.cons (.register 2) (.register 5)) (.ret [.register 6])))) }

def takeUntilBudget (W k : ℕ) : ℕ := (predBudget W + 40) * k + 13

theorem takeUntil_compiled (code : Code p) (compare same self : Fin p)
    (hcompare : code compare = RegisterComparator.comparatorBody compare)
    (hsame : code same = sameBody compare) (hself : code self = takeUntilBody self same)
    {a : ArcW W} :
    ∀ (rs : List (ArcW W)) {h : Heap}, Valid h → ∀ {lp ap : Ptr}, ListRep ArcWAt h lp rs →
      ArcWAt h ap a →
      ∃ out q, Extends h out ∧ Valid out ∧
        ListRep ArcWAt out q (rs.takeWhile (fun b => !samePred a b)) ∧
        Within code h (initialRegisters [.pointer lp, .pointer ap]) (code self) [.pointer q] out
          (takeUntilBudget W rs.length)
  | [], h, hh, lp, ap, hl, _ => by
    obtain ⟨ps, hlist, hrel⟩ := hl
    cases hrel
    cases hlist with
    | nil cell =>
      refine ⟨h, 0, .refl h, hh, RegisterListCommon.listRep_null hh, ?_⟩
      rw [hself]
      apply Within.mono (a := 13) _ (by simp [takeUntilBudget])
      apply Within.load (budget := 3) (pointer := lp) (c := .nil)
      · simp [Atom.eval, initialRegisters]
      · exact cell
      · simpa [values, Atom.eval, Cases.select] using
          Within.ret code h (loadRegisters (initialRegisters [.pointer lp, .pointer ap]) 2 3 15 .nil)
            [.null]
  | b :: rs, h, hh, lp, ap, hl, ha => by
    obtain ⟨ps, hlist, hrel⟩ := hl
    cases hrel with
    | @cons bp _ ps _ hb hbs =>
    cases hlist with
    | @cons _ _ rest _ cell hrest =>
    let r0 := initialRegisters [Value.pointer lp, .pointer ap]
    let r1 := loadRegisters r0 2 3 15 (.cons bp rest)
    have tested := same_compiled code compare same hcompare hsame hb ha
    have targs : values r1 [.register 2, .register 1] = [.pointer bp, .pointer ap] := by
      simp [r1, r0, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    let branches : Cases (Command p) := { CompiledTrie.failCases with
      nil := .ret [.null]
      cons := .call same [.register 2, .register 1] [4]
        (.branch (.register 4) (.ret [.null])
          (.call self [.register 3, .register 1] [5]
            (.allocate 6 (.cons (.register 2) (.register 5)) (.ret [.register 6])))) }
    by_cases hp : samePred a b = true
    · refine ⟨h, 0, .refl h, hh, by simpa [hp] using RegisterListCommon.listRep_null hh, ?_⟩
      let r2 := bindResults r1 [4] [Value.flag true]
      have ret : Within code h r2 (.ret [.null]) [.pointer 0] h 3 := by
        simpa [values, Atom.eval] using Within.ret code h r2 [.null]
      have br := Within.branch (b := true) (test := .register 4) (regs := r2)
        (no := .call self [.register 3, .register 1] [5]
          (.allocate 6 (.cons (.register 2) (.register 5)) (.ret [.register 6])))
        (by simp [Atom.eval, r2, bindResults]) (by simpa using ret)
      have tc := Within.call (procedure := same) (regs := r1) (results := [4])
        (arguments := [.register 2, .register 1]) (by simpa only [targs, hp] using tested) br
      have loaded := Within.load (address := .register 0) (first := 2) (second := 3) (bit := 15)
        (branches := branches) (by simp [Atom.eval, r0, initialRegisters]) cell tc
      rw [hself]
      refine loaded.mono ?_
      simp only [takeUntilBudget, List.length_cons, List.length_nil]
      generalize predBudget W = B
      nlinarith
    · have hpf : samePred a b = false := by simpa using hp
      obtain ⟨out, q, e, v, hq, rec⟩ := takeUntil_compiled code compare same self hcompare hsame
        hself rs hh ⟨ps, hrest, hbs⟩ ha
      obtain ⟨e2, v2, hout⟩ := RegisterListCommon.allocate_consRep
        (R := ArcWAt) (fun ext _ _ hx => hx.mono ext) v (hb.mono e) (hb.mono e).allocated hq
      refine ⟨out ++ [.cons bp q], out.length, e.trans e2, v2, by simpa [hpf] using hout, ?_⟩
      let r2 := bindResults r1 [4] [Value.flag false]
      let r3 := bindResults r2 [5] [Value.pointer q]
      have last := RegisterListCommon.within_consRet code out (regs := r3) (dst := 6) (head := 2)
        (tail := 5) (a := bp) (t := q) (by simp [r3, r2, r1, bindResults, loadRegisters, decoded])
        (by simp [r3, bindResults])
      have rargs : values r2 [.register 3, .register 1] = [.pointer rest, .pointer ap] := by
        simp [r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
      have rc := Within.call (procedure := self) (regs := r2) (results := [5])
        (arguments := [.register 3, .register 1]) (by simpa only [rargs] using rec) last
      have br := Within.branch (b := false) (test := .register 4) (regs := r2)
        (yes := .ret [.null]) (by simp [Atom.eval, r2, bindResults]) (by simpa using rc)
      have tc := Within.call (procedure := same) (regs := r1) (results := [4])
        (arguments := [.register 2, .register 1]) (by simpa only [targs, hpf] using tested) br
      have loaded := Within.load (address := .register 0) (first := 2) (second := 3) (bit := 15)
        (branches := branches) (by simp [Atom.eval, r0, initialRegisters]) cell tc
      rw [hself]
      refine loaded.mono ?_
      simp only [takeUntilBudget, List.length_cons, List.length_nil]
      generalize predBudget W = B
      nlinarith

/-! ## Successor search -/

def searchNext (self : Fin p) : Command p :=
  .allocate 12 (.cons (.register 1) (.register 2))
    (.call self [.register 5, .register 11, .register 12, .register 3] [13] (.ret [.register 13]))

def searchSelect (self : Fin p) : Command p :=
  .branch (.register 13) (.copy 11 (.register 14) (searchNext self))
    (.copy 11 (.register 1) (searchNext self))

def searchMiss (self succFind : Fin p) : Command p :=
  .load (.register 1) 8 9 10 { CompiledTrie.failCases with
    bit := .load (.register 8) 9 10 15 { CompiledTrie.failCases with
      pair := .load (.register 10) 11 12 15 { CompiledTrie.failCases with
        pair := .call succFind [.register 3, .register 12] [13, 14] (searchSelect self) } } }

def searchHit (take : Fin p) : Command p :=
  .call take [.register 2, .register 1] [8]
    (.allocate 9 (.cons (.register 1) (.register 8)) (.ret [.register 9]))

def searchCases (self memFind take succFind : Fin p) : Cases (Command p) :=
  { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := .call memFind [.register 2, .register 1] [6, 7]
      (.branch (.register 6) (searchHit take) (searchMiss self succFind)) }

/-- Arguments 0=fuel list, 1=current arc, 2=reversed visited arcs, 3=arc list. -/
def searchBody (self memFind take succFind : Fin p) : Command p :=
  .load (.register 0) 4 5 15 (searchCases self memFind take succFind)

structure Procedures (p : ℕ) where
  arcs : RegisterSupportArcs.Procedures p
  memFind : Fin p
  takeUntil : Fin p
  succFind : Fin p
  activeFind : Fin p
  search : Fin p
  cycle : Fin p

/-- Arguments 0=arc list; the result is the support cycle (up to order). -/
def cycleBody (activeFind search : Fin p) : Command p :=
  .call activeFind [.register 0, .null] [1, 2]
    (.branch (.register 1)
      (.allocate 3 (.cons (.register 2) (.register 0))
        (.call search [.register 3, .register 2, .null, .register 0] [4] (.ret [.register 4])))
      (.ret [.null]))

structure Procedures.Matches (ids : Procedures p) (code : Code p) : Prop where
  arcs : ids.arcs.Matches code
  memFind : code ids.memFind = RegisterListFind.body ids.memFind ids.arcs.same
  takeUntil : code ids.takeUntil = takeUntilBody ids.takeUntil ids.arcs.same
  succFind : code ids.succFind = RegisterListFind.body ids.succFind ids.arcs.succ
  activeFind : code ids.activeFind = RegisterListFind.body ids.activeFind ids.arcs.active
  search : code ids.search = searchBody ids.search ids.memFind ids.takeUntil ids.succFind
  cycle : code ids.cycle = cycleBody ids.activeFind ids.search

def stepBudget (W A L : ℕ) : ℕ := (2 * predBudget W + 70) * (L + A) + 120

def searchBudget (W A L F : ℕ) : ℕ := F * stepBudget W A L + 13

theorem memFind_compiled (code : Code p) (ids : Procedures p) (hcode : ids.Matches code)
    {h : Heap} (hh : Valid h) {rp ap : Ptr} {rs : List (ArcW W)} {a : ArcW W}
    (hr : ListRep ArcWAt h rp rs) (ha : ArcWAt h ap a) :
    ∃ out q, Extends h out ∧ Valid out ∧
      (∀ x, rs.find? (samePred a) = some x → ArcWAt out q x) ∧
      (rs.find? (samePred a) = none → q = 0) ∧
      Within code h (initialRegisters [.pointer rp, .pointer ap]) (code ids.memFind)
        [.flag (rs.find? (samePred a)).isSome, .pointer q] out
        ((predBudget W + 30) * rs.length + 15) :=
  RegisterListFind.compiled_const code ids.memFind ids.arcs.same hcode.memFind ArcWAt ArcWAt
    (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext) samePred (predBudget W) hh
    hr ha (fun hv _ _ _ hx hd => ⟨_, .refl _, hv,
      same_compiled code ids.arcs.compare ids.arcs.same hcode.arcs.compare hcode.arcs.same hx hd⟩)

theorem search_compiled (code : Code p) (ids : Procedures p) (hcode : ids.Matches code)
    (arcs : List (ArcW W)) :
    ∀ (fuel : List (ArcW W)) {h : Heap}, Valid h → ∀ {fp ap rp sp : Ptr} {a : ArcW W}
      {rs : List (ArcW W)}, ListRep ArcWAt h fp fuel → ArcWAt h ap a → ListRep ArcWAt h rp rs →
      ListRep ArcWAt h sp arcs →
      ∃ out q, Extends h out ∧ Valid out ∧ ListRep ArcWAt out q (searchW arcs fuel a rs) ∧
        Within code h (initialRegisters [.pointer fp, .pointer ap, .pointer rp, .pointer sp])
          (code ids.search) [.pointer q] out
          (searchBudget W arcs.length (rs.length + fuel.length) fuel.length)
  | [], h, hh, fp, ap, rp, sp, a, rs, hf, _, _, _ => by
    obtain ⟨ps, hlist, hrel⟩ := hf
    cases hrel
    cases hlist with
    | nil cell =>
      refine ⟨h, 0, .refl h, hh, by simpa [searchW] using RegisterListCommon.listRep_null hh, ?_⟩
      rw [hcode.search]
      apply Within.mono (a := 13) _ (by simp [searchBudget])
      apply Within.load (budget := 3) (pointer := fp) (c := .nil)
      · simp [Atom.eval, initialRegisters]
      · exact cell
      · simpa [values, Atom.eval, Cases.select, searchCases] using
          Within.ret code h (loadRegisters (initialRegisters [.pointer fp, .pointer ap, .pointer rp,
            .pointer sp]) 4 5 15 .nil) [.null]
  | f :: fuel, h, hh, fp, ap, rp, sp, a, rs, hf, ha, hr, hs => by
    obtain ⟨ps, hlist, hrel⟩ := hf
    cases hrel with
    | @cons fh _ ps _ _ hft =>
    cases hlist with
    | @cons _ _ ft _ fcell frest =>
    have mono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr (x : ArcW W), ArcWAt h ptr x →
        ArcWAt h' ptr x := fun e _ _ hx => hx.mono e
    obtain ⟨m1, q1, e1, v1, -, -, memRun⟩ := memFind_compiled code ids hcode hh hr ha
    let r0 := initialRegisters [Value.pointer fp, .pointer ap, .pointer rp, .pointer sp]
    let r1 := loadRegisters r0 4 5 15 (.cons fh ft)
    let found := (rs.find? (samePred a)).isSome
    let r2 := bindResults r1 [6, 7] [Value.flag found, .pointer q1]
    have margs : values r1 [.register 2, .register 1] = [.pointer rp, .pointer ap] := by
      simp [r1, r0, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    have hmem : ∀ {rest : Command p} {o : List Value} {outH : Heap} {B : ℕ},
        Within code m1 r2 rest o outH B →
        Within code h r0 (.load (.register 0) 4 5 15 { CompiledTrie.failCases with
            nil := .ret [.null]
            cons := .call ids.memFind [.register 2, .register 1] [6, 7] rest }) o outH
          (10 + (1 + 2 * 2 + ((predBudget W + 30) * rs.length + 15) + B)) := by
      intro rest o outH B hrest
      have mc := Within.call (procedure := ids.memFind) (regs := r1) (results := [6, 7])
        (arguments := [.register 2, .register 1]) (by simpa only [margs] using memRun) hrest
      exact Within.load (address := .register 0) (first := 4) (second := 5) (bit := 15)
        (branches := { CompiledTrie.failCases with
          nil := .ret [.null]
          cons := .call ids.memFind [.register 2, .register 1] [6, 7] rest })
        (by simp [Atom.eval, r0, initialRegisters]) fcell mc
    have h6 : (Atom.register 6).eval r2 = .flag found := by simp [r2, bindResults, Atom.eval]
    have hlen : rs.length ≤ rs.length + (f :: fuel).length := by simp
    by_cases hit : found = true
    · -- the current arc was already visited
      obtain ⟨m2, q2, e2, v2, hq2, takeRun⟩ := takeUntil_compiled code ids.arcs.compare
        ids.arcs.same ids.takeUntil hcode.arcs.compare hcode.arcs.same hcode.takeUntil rs v1
        (hr.mono e1 (fun _ _ hx => hx.mono e1)) (ha.mono e1)
      obtain ⟨e3, v3, hout⟩ := RegisterListCommon.allocate_consRep (R := ArcWAt) mono v2
        ((ha.mono e1).mono e2) ((ha.mono e1).mono e2).allocated hq2
      have hsearch : searchW arcs (f :: fuel) a rs =
          a :: rs.takeWhile (fun b => !samePred a b) := by
        have hc : (rs.find? (samePred a)).isSome = true := hit
        simp only [searchW, hc, ↓reduceIte]
      refine ⟨m2 ++ [.cons ap q2], m2.length, e1.trans (e2.trans e3), v3,
        by rw [hsearch]; exact hout, ?_⟩
      let r3 := bindResults r2 [8] [Value.pointer q2]
      have last := RegisterListCommon.within_consRet code m2 (regs := r3) (dst := 9) (head := 1)
        (tail := 8) (a := ap) (t := q2)
        (by simp [r3, r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters])
        (by simp [r3, bindResults])
      have targs : values r2 [.register 2, .register 1] = [.pointer rp, .pointer ap] := by
        simp [r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters, values,
          Atom.eval]
      have tc := Within.call (procedure := ids.takeUntil) (regs := r2) (results := [8])
        (arguments := [.register 2, .register 1]) (by simpa only [targs] using takeRun) last
      have br := Within.branch (b := true) (test := .register 6) (regs := r2)
        (yes := searchHit ids.takeUntil) (no := searchMiss ids.search ids.succFind)
        (by rw [h6, hit]) (by simpa [searchHit] using tc)
      have whole := hmem br
      rw [hcode.search]
      refine whole.mono ?_
      simp only [searchBudget, stepBudget, takeUntilBudget, List.length_cons]
      generalize predBudget W = B at *
      have hS : (2 * B + 70) * (rs.length + (fuel.length + 1) + arcs.length) + 120 ≤
          (fuel.length + 1) * ((2 * B + 70) * (rs.length + (fuel.length + 1) + arcs.length) + 120) :=
        Nat.le_mul_of_pos_left _ (by omega)
      have hR : (2 * B + 70) * rs.length ≤
          (2 * B + 70) * (rs.length + (fuel.length + 1) + arcs.length) :=
        Nat.mul_le_mul_left _ (by omega)
      have hsum : (B + 30) * rs.length + (B + 40) * rs.length = (2 * B + 70) * rs.length := by
        ring
      generalize (B + 30) * rs.length = X1 at *
      generalize (B + 40) * rs.length = X2 at *
      generalize (2 * B + 70) * rs.length = X3 at *
      generalize (2 * B + 70) * (rs.length + (fuel.length + 1) + arcs.length) = S at *
      generalize (fuel.length + 1) * (S + 120) = T at *
      omega
    · -- follow the first supported successor
      have hpf : found = false := by simpa using hit
      obtain ⟨body, kp, sp', srcp, tgtp, c1, c2, -, c3, -, ht⟩ := id ha
      obtain ⟨m2, q2, e2, v2, hfound, hnone, succRun⟩ := RegisterListFind.compiled_const code
        ids.succFind ids.arcs.succ hcode.succFind ArcWAt
        (fun heap ptr (t : StateW W) => BitsAt heap ptr t) (fun ext _ _ hx => hx.mono ext)
        (fun ext _ _ hx => hx.mono ext) succPred (predBudget W) v1
        (hs.mono e1 (fun _ _ hx => hx.mono e1)) (ht.mono e1)
        (fun hv _ _ _ hx hd => ⟨_, .refl _, hv, succ_compiled code ids.arcs.compare ids.arcs.succ
          hcode.arcs.compare hcode.arcs.succ hx hd⟩)
      have e12 := e1.trans e2
      have ha2 : ArcWAt m2 ap a := ha.mono e12
      let r3 := loadRegisters r2 8 9 10 (.bit a.active body)
      let r4 := loadRegisters r3 9 10 15 (.pair kp sp')
      let r5 := loadRegisters r4 11 12 15 (.pair srcp tgtp)
      let sfound := (arcs.find? (succPred a.target)).isSome
      let r6 := bindResults r5 [13, 14] [Value.flag sfound, .pointer q2]
      have h1 : r6 1 = .pointer ap := by
        simp [r6, r5, r4, r3, r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters]
      have h2 : r6 2 = .pointer rp := by
        simp [r6, r5, r4, r3, r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters]
      have h3 : r6 3 = .pointer sp := by
        simp [r6, r5, r4, r3, r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters]
      have h5 : r6 5 = .pointer ft := by
        simp [r6, r5, r4, r3, r2, r1, bindResults, loadRegisters, decoded]
      -- the selected successor pointer
      obtain ⟨np, hnp, hsel⟩ : ∃ np, ArcWAt m2 np (succW arcs a) ∧
          ∀ {o : List Value} {outH : Heap} {B : ℕ},
            Within code m2 (Function.update r6 11 (.pointer np)) (searchNext ids.search) o outH B →
            Within code m2 r6 (searchSelect ids.search) o outH (3 + (3 + B)) := by
        have h13 : (Atom.register 13).eval r6 = .flag sfound := by
          simp [r6, bindResults, Atom.eval]
        rcases hfs : arcs.find? (succPred a.target) with _ | b
        · refine ⟨ap, by simpa [succW, hfs] using ha2, fun {o outH B} hw => ?_⟩
          have hsf : sfound = false := by simp [sfound, hfs]
          refine Within.branch (b := false) (by rw [h13, hsf]) ?_
          exact Within.copy (by simpa [Atom.eval, h1] using hw)
        · refine ⟨q2, by simpa [succW, hfs] using hfound b hfs, fun {o outH B} hw => ?_⟩
          have hsf : sfound = true := by simp [sfound, hfs]
          refine Within.branch (b := true) (by rw [h13, hsf]) ?_
          have h14 : r6 14 = .pointer q2 := by simp [r6, bindResults]
          exact Within.copy (by simpa [Atom.eval, h14] using hw)
      obtain ⟨e3, v3, hrs⟩ := RegisterListCommon.allocate_consRep (R := ArcWAt) mono v2 ha2
        ha2.allocated (hr.mono e12 (fun _ _ hx => hx.mono e12))
      let m3 := m2 ++ [.cons ap rp]
      have e13 := e12.trans e3
      obtain ⟨out, q, e4, v4, hq, rec⟩ := search_compiled code ids hcode arcs fuel v3
        ⟨ps, frest.mono e13, hft.imp (fun _ _ hx => hx.mono e13)⟩ (hnp.mono e3) hrs
        (hs.mono e13 (fun _ _ hx => hx.mono e13))
      have hsearch : searchW arcs (f :: fuel) a rs = searchW arcs fuel (succW arcs a) (a :: rs) := by
        simp only [searchW]
        have hn : ¬ ((rs.find? (samePred a)).isSome = true) := by
          rw [show (rs.find? (samePred a)).isSome = found from rfl, hpf]
          simp
        simp only [hn, Bool.false_eq_true, ↓reduceIte]
      refine ⟨out, q, e13.trans e4, v4, by rw [hsearch]; exact hq, ?_⟩
      let r7 := Function.update r6 11 (Value.pointer np)
      let r8 := Function.update r7 12 (Value.pointer m2.length)
      let r9 := bindResults r8 [13] [Value.pointer q]
      have last : Within code out r9 (.ret [.register 13]) [.pointer q] out 3 := by
        simpa [r9, bindResults, values, Atom.eval] using Within.ret code out r9 [.register 13]
      have cargs : values r8 [.register 5, .register 11, .register 12, .register 3] =
          [.pointer ft, .pointer np, .pointer m2.length, .pointer sp] := by
        simp [r8, r7, values, Atom.eval, h5, h3]
      have hL : (a :: rs).length + fuel.length = rs.length + (f :: fuel).length := by
        simp only [List.length_cons]; omega
      rw [hL] at rec
      have rc := Within.call (procedure := ids.search) (regs := r8) (results := [13])
        (arguments := [.register 5, .register 11, .register 12, .register 3])
        (by simpa only [cargs] using rec) last
      have al := Within.allocate (h := m2) (regs := r7) (dst := 12)
        (expr := .cons (.register 1) (.register 2)) (c := .cons ap rp)
        (by simp [CellExpr.eval, Atom.eval, r7, h1, h2, Value.asPointer]) rc
      have sel := hsel al
      have sargs : values r5 [.register 3, .register 12] = [.pointer sp, .pointer tgtp] := by
        simp [r5, r4, r3, r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters,
          values, Atom.eval]
      have sc := Within.call (procedure := ids.succFind) (regs := r5) (results := [13, 14])
        (arguments := [.register 3, .register 12]) (by simpa only [sargs] using succRun) sel
      have l3 := Within.load (address := .register 10) (first := 11) (second := 12) (bit := 15)
        (branches := { CompiledTrie.failCases with
          pair := .call ids.succFind [.register 3, .register 12] [13, 14]
            (searchSelect ids.search) })
        (by simp [Atom.eval, r4, loadRegisters, decoded]) (e1.lookup c3) sc
      have l2 := Within.load (address := .register 8) (first := 9) (second := 10) (bit := 15)
        (branches := { CompiledTrie.failCases with
          pair := .load (.register 10) 11 12 15 { CompiledTrie.failCases with
            pair := .call ids.succFind [.register 3, .register 12] [13, 14]
              (searchSelect ids.search) } })
        (by simp [Atom.eval, r3, loadRegisters, decoded]) (e1.lookup c2) l3
      have l1 := Within.load (address := .register 1) (first := 8) (second := 9) (bit := 10)
        (branches := { CompiledTrie.failCases with
          bit := .load (.register 8) 9 10 15 { CompiledTrie.failCases with
            pair := .load (.register 10) 11 12 15 { CompiledTrie.failCases with
              pair := .call ids.succFind [.register 3, .register 12] [13, 14]
                (searchSelect ids.search) } } })
        (by simp [Atom.eval, r2, r1, r0, bindResults, loadRegisters, decoded, initialRegisters])
        (e1.lookup c1) l2
      have br := Within.branch (b := false) (test := .register 6) (regs := r2)
        (yes := searchHit ids.takeUntil) (no := searchMiss ids.search ids.succFind)
        (by rw [h6, hpf]) (by simpa [searchMiss] using l1)
      have whole := hmem br
      rw [hcode.search]
      refine whole.mono ?_
      simp only [searchBudget, stepBudget, List.length_cons, CellExpr.args, List.length_nil]
      generalize predBudget W = B at *
      nlinarith

def cycleBudget (W A : ℕ) : ℕ := 43 * A + searchBudget W A (A + 1) (A + 1) + 60

/-- Argument 0=arc list; the result is `cycleW arcs`. -/
theorem cycle_compiled (code : Code p) (ids : Procedures p) (hcode : ids.Matches code)
    {h : Heap} (hh : Valid h) {sp : Ptr} {arcs : List (ArcW W)}
    (hs : ListRep ArcWAt h sp arcs) :
    ∃ out q, Extends h out ∧ Valid out ∧ ListRep ArcWAt out q (cycleW arcs) ∧
      Within code h (initialRegisters [.pointer sp]) (code ids.cycle) [.pointer q] out
        (cycleBudget W arcs.length) := by
  obtain ⟨m1, q1, e1, v1, hfound, -, findRun⟩ := RegisterListFind.compiled_const code
    ids.activeFind ids.arcs.active hcode.activeFind ArcWAt (fun _ _ (_ : Unit) => True)
    (fun ext _ _ hx => hx.mono ext) (fun _ _ _ _ => trivial) (fun _ a => a.active) 13 hh hs
    (data := ()) (dataPtr := 0) trivial
    (fun hv _ _ _ hx _ => ⟨_, .refl _, hv, active_compiled code ids.arcs.active
      hcode.arcs.active hx⟩)
  let r0 := initialRegisters [Value.pointer sp]
  let found := (arcs.find? (fun a => a.active)).isSome
  let r1 := bindResults r0 [1, 2] [Value.flag found, .pointer q1]
  have fargs : values r0 [.register 0, .null] = [.pointer sp, .pointer 0] := by
    simp [r0, initialRegisters, values, Atom.eval]
  have h1 : (Atom.register 1).eval r1 = .flag found := by simp [r1, bindResults, Atom.eval]
  rcases hf : arcs.find? (fun a => a.active) with _ | a
  · have hc : cycleW arcs = [] := by simp [cycleW, hf]
    refine ⟨m1, 0, e1, v1, by rw [hc]; exact RegisterListCommon.listRep_null v1, ?_⟩
    have last : Within code m1 r1 (.ret [.null]) [.pointer 0] m1 3 := by
      simpa [values, Atom.eval] using Within.ret code m1 r1 [.null]
    have br := Within.branch (b := false) (test := .register 1) (regs := r1)
      (yes := .allocate 3 (.cons (.register 2) (.register 0))
        (.call ids.search [.register 3, .register 2, .null, .register 0] [4] (.ret [.register 4])))
      (by rw [h1]; simp [found, hf]) (by simpa using last)
    have fc := Within.call (procedure := ids.activeFind) (regs := r0) (results := [1, 2])
      (arguments := [.register 0, .null]) (by simpa only [fargs] using findRun) br
    rw [hcode.cycle]
    refine fc.mono ?_
    simp only [cycleBudget, List.length_cons, List.length_nil]
    omega
  · have ha : ArcWAt m1 q1 a := hfound a hf
    have hc : cycleW arcs = searchW arcs (a :: arcs) a [] := by simp [cycleW, hf]
    obtain ⟨e2, v2, hfuel⟩ := RegisterListCommon.allocate_consRep (R := ArcWAt)
      (fun ext _ _ hx => hx.mono ext) v1 ha ha.allocated (hs.mono e1 (fun _ _ hx => hx.mono e1))
    let m2 := m1 ++ [.cons q1 sp]
    obtain ⟨out, q, e3, v3, hq, run⟩ := search_compiled code ids hcode arcs (a :: arcs) v2 hfuel
      (ha.mono e2) (RegisterListCommon.listRep_null v2)
      (hs.mono (e1.trans e2) (fun _ _ hx => hx.mono (e1.trans e2)))
    refine ⟨out, q, e1.trans (e2.trans e3), v3, by rw [hc]; exact hq, ?_⟩
    let r2 := Function.update r1 3 (Value.pointer m1.length)
    let r3 := bindResults r2 [4] [Value.pointer q]
    have last : Within code out r3 (.ret [.register 4]) [.pointer q] out 3 := by
      simpa [r3, bindResults, values, Atom.eval] using Within.ret code out r3 [.register 4]
    have sargs : values r2 [.register 3, .register 2, .null, .register 0] =
        [.pointer m1.length, .pointer q1, .pointer 0, .pointer sp] := by
      simp [r2, r1, r0, bindResults, initialRegisters, values, Atom.eval]
    have sc := Within.call (procedure := ids.search) (regs := r2) (results := [4])
      (arguments := [.register 3, .register 2, .null, .register 0])
      (by simpa only [sargs] using run) last
    have al := Within.allocate (h := m1) (regs := r1) (dst := 3)
      (expr := .cons (.register 2) (.register 0)) (c := .cons q1 sp)
      (by simp [CellExpr.eval, Atom.eval, r1, r0, bindResults, initialRegisters,
        Value.asPointer]) sc
    have br := Within.branch (b := true) (test := .register 1) (regs := r1)
      (no := .ret [.null]) (by rw [h1]; simp [found, hf]) (by simpa using al)
    have fc := Within.call (procedure := ids.activeFind) (regs := r0) (results := [1, 2])
      (arguments := [.register 0, .null]) (by simpa only [fargs] using findRun) br
    rw [hcode.cycle]
    refine fc.mono ?_
    simp only [cycleBudget, List.length_cons, List.length_nil, CellExpr.args]
    omega

end WeightedMIS.RegisterSupportCycle
