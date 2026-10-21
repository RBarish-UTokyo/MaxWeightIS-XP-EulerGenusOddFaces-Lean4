module

public import WeightedMIS.RegisterCoordinate

/-! # Closed register traversal updating every box coordinate -/

@[expose] public section

namespace WeightedMIS.RegisterCoordinates

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords

variable {p : ℕ}

def consResult : Command p :=
  .allocate 11 (.cons (.register 8) (.register 10)) (.ret [.flag true, .register 11])

def afterDigit (self : Fin p) : Command p :=
  .branch (.register 7)
    (.call self [.register 0, .register 4, .register 6] [9, 10]
      (.branch (.register 9) consResult RegisterCoordinate.rejected))
    RegisterCoordinate.rejected

def wordsBody (self digit : Fin p) : Command p :=
  .load (.register 1) 3 4 15 { CompiledTrie.failCases with
    nil := .load (.register 2) 5 6 15 { CompiledTrie.failCases with
      nil := .ret [.flag true, .null] }
    cons := .load (.register 2) 5 6 15 { CompiledTrie.failCases with
      cons := .call digit [.register 0, .register 3, .register 5] [7, 8] (afterDigit self) } }

theorem compiled (code : Code p) (self digit add cmp sub complement : Fin p)
    (hself : code self = wordsBody self digit) (hdigit : code digit = RegisterCoordinate.digitBody add cmp sub)
    (hadd : code add = RegisterAdder.adderBody add)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (hsub : code sub = RegisterSubtractor.subtractorBody complement add)
    (hcomp : code complement = RegisterComplement.complementBody complement)
    {n : ℕ} {h : Heap} (hh : Valid h) {base : Bits n} {ws : List (Bits n)} {ds : List (SignedWord n)}
    {bp wp dp : Ptr} (hb : BitsAt h bp base) (hw : WordsAt h wp ws) (hd : DeltasAt h dp ds)
    (hlen : ws.length = ds.length) :
    ∃ out q, Extends h out ∧ Valid out ∧ OptionWordsAt out q (updateWords base ws ds) ∧
      Within code h (initialRegisters [.pointer bp, .pointer wp, .pointer dp]) (code self)
        [.flag (updateWords base ws ds).isSome, .pointer q] out (500 * (n + 1) * ws.length + 25) := by
  induction ws generalizing h wp dp ds with
  | nil =>
    cases ds with
    | cons d ds => simp at hlen
    | nil =>
      have wc := WordsAt.nil_iff.mp hw
      have dc := DeltasAt.nil_iff.mp hd
      refine ⟨h, 0, .refl h, hh, ?_, ?_⟩
      · exact WordsAt.nil hh.1
      · rw [hself]
        unfold wordsBody
        apply Within.load (budget := 15) (pointer := wp) (c := .nil)
        · simp [Atom.eval, initialRegisters]
        · exact wc
        · apply Within.load (budget := 5) (pointer := dp) (c := .nil)
          · simp [Atom.eval, initialRegisters, loadRegisters, decoded]
          · exact dc
          · simpa [values, Atom.eval, Cases.select, updateWords] using
              Within.ret code h (loadRegisters (loadRegisters
                (initialRegisters [.pointer bp, .pointer wp, .pointer dp]) 3 4 15 .nil) 5 6 15 .nil)
                [.flag true, .null]
  | cons w ws ih =>
    cases ds with
    | nil => simp at hlen
    | cons d ds =>
      have hl : ws.length = ds.length := by simpa using hlen
      obtain ⟨xp, xt, wc, hx, hxs⟩ := WordsAt.cons_iff.mp hw
      obtain ⟨sp, st, dc, hs, hss⟩ := DeltasAt.cons_iff.mp hd
      obtain ⟨mid, y, he, hm, hy, digitRun⟩ := RegisterCoordinate.compiled code add cmp sub complement
        hadd hcmp hsub hcomp hh hb hx hs
      let regs := initialRegisters [Value.pointer bp, .pointer wp, .pointer dp]
      let r1 := loadRegisters regs 3 4 15 (.cons xp xt)
      let r2 := loadRegisters r1 5 6 15 (.cons sp st)
      let r3 := bindResults r2 [7, 8] [.flag (updateDigit base w d).isSome, .pointer y]
      have hargs : values r2 [.register 0, .register 3, .register 5] =
          [.pointer bp, .pointer xp, .pointer sp] := by
        simp [values, Atom.eval, r2, r1, regs, loadRegisters, decoded, initialRegisters]
      have hdRun : Within code h (initialRegisters (values r2 [.register 0, .register 3, .register 5]))
          (code digit) [.flag (updateDigit base w d).isSome, .pointer y] mid (400 * (n + 1)) := by
        simpa only [hargs, hdigit] using digitRun
      have h7 : r3 7 = .flag (updateDigit base w d).isSome := by simp [r3, bindResults]
      cases hupdate : updateDigit base w d with
      | none =>
        have hy0 : y = 0 := by simpa [hupdate, OptionWordAt] using hy
        subst y
        refine ⟨mid, 0, he, hm, ?_, ?_⟩
        · simp [updateWords, hupdate, OptionWordsAt]
        · have hr := RegisterCoordinate.rejected_compiled code mid r3
          have hbranch := Within.branch (test := .register 7) (b := false)
            (yes := .call self [.register 0, .register 4, .register 6] [9, 10]
              (.branch (.register 9) consResult RegisterCoordinate.rejected))
            (no := RegisterCoordinate.rejected)
            (by simpa [Atom.eval, hupdate] using h7) hr
          have hc := Within.call (procedure := digit) (arguments := [.register 0, .register 3, .register 5])
            (results := [7, 8]) (regs := r2) hdRun hbranch
          have hld := Within.load (address := .register 2) (first := 5) (second := 6) (bit := 15)
            (branches := {CompiledTrie.failCases with cons := .call digit [.register 0, .register 3, .register 5] [7, 8] (afterDigit self)})
            (by simp [Atom.eval, r1, regs, loadRegisters, decoded, initialRegisters]) dc hc
          have hlw := Within.load (address := .register 1) (first := 3) (second := 4) (bit := 15)
            (branches := {CompiledTrie.failCases with
              nil := .load (.register 2) 5 6 15 {CompiledTrie.failCases with nil := .ret [.flag true, .null]}
              cons := .load (.register 2) 5 6 15 {CompiledTrie.failCases with cons := .call digit [.register 0, .register 3, .register 5] [7, 8] (afterDigit self)}})
            (by simp [Atom.eval, regs, initialRegisters]) wc hld
          simpa [hself, wordsBody, updateWords, hupdate] using
            hlw.mono (b := 500 * (n + 1) * (w :: ws).length + 25) (by simp; nlinarith)
      | some new =>
        have hyrep : BitsAt mid y new := by simpa [hupdate, OptionWordAt] using hy
        obtain ⟨last, tail, hel, hlast, htail, child⟩ := ih hm (hb.mono he) (hxs.mono he) (hss.mono he) hl
        let r4 := bindResults r3 [9, 10] [.flag (updateWords base ws ds).isSome, .pointer tail]
        have hargsChild : values r3 [.register 0, .register 4, .register 6] =
            [.pointer bp, .pointer xt, .pointer st] := by
          simp [values, Atom.eval, r3, r2, r1, regs, bindResults, loadRegisters, decoded, initialRegisters]
        have hcRun : Within code mid
            (initialRegisters (values r3 [.register 0, .register 4, .register 6])) (code self)
            [.flag (updateWords base ws ds).isSome, .pointer tail] last
            (500 * (n + 1) * ws.length + 25) := by simpa only [hargsChild] using child
        have h9 : r4 9 = .flag (updateWords base ws ds).isSome := by simp [r4, bindResults]
        have h8 : r4 8 = .pointer y := by simp [r4, r3, bindResults]
        have h10 : r4 10 = .pointer tail := by simp [r4, bindResults]
        obtain ⟨out, q, heout, ho, hq, cont⟩ :
            ∃ out q, Extends last out ∧ Valid out ∧
              OptionWordsAt out q (updateWords base (w :: ws) (d :: ds)) ∧
              Within code last r4 (.branch (.register 9) consResult RegisterCoordinate.rejected)
                [.flag (updateWords base (w :: ws) (d :: ds)).isSome, .pointer q] out 16 := by
          cases hrest : updateWords base ws ds with
          | none =>
            have ht0 : tail = 0 := by simpa [hrest, OptionWordsAt] using htail
            refine ⟨last, 0, .refl last, hlast, ?_, ?_⟩
            · simp [updateWords, hupdate, hrest, OptionWordsAt]
            · have hr := RegisterCoordinate.rejected_compiled code last r4
              have hbr := Within.branch (test := .register 9) (b := false)
                (yes := consResult) (no := RegisterCoordinate.rejected)
                (by simpa [Atom.eval, hrest] using h9) hr
              simpa [updateWords, hupdate, hrest] using hbr.mono (b := 16) (by omega)
          | some ys =>
            have htRep : WordsAt last tail ys := by simpa [hrest, OptionWordsAt] using htail
            obtain ⟨hal, hlRep⟩ := allocate_word_cons hlast (hyrep.mono hel) htRep
            refine ⟨last ++ [.cons y tail], last.length, hal.1, hal.2.1, ?_, ?_⟩
            · simpa [updateWords, hupdate, hrest, OptionWordsAt] using hlRep
            · have ret := Within.ret code (last ++ [.cons y tail])
                (Function.update r4 11 (.pointer last.length)) [.flag true, .register 11]
              have hret : Within code (last ++ [.cons y tail])
                  (Function.update r4 11 (.pointer last.length)) (.ret [.flag true, .register 11])
                  [.flag true, .pointer last.length] (last ++ [.cons y tail]) 5 := by
                simpa [values, Atom.eval] using ret
              have halc := Within.allocate (dst := 11) (expr := .cons (.register 8) (.register 10))
                (by simp [CellExpr.eval, Atom.eval, h8, h10, Value.asPointer]) hret
              have hbr := Within.branch (test := .register 9) (b := true)
                (yes := consResult) (no := RegisterCoordinate.rejected)
                (by simpa [Atom.eval, hrest] using h9) halc
              simpa [updateWords, hupdate, hrest, consResult, CellExpr.args] using hbr
        refine ⟨out, q, (he.trans hel).trans heout, ho, hq, ?_⟩
        have selfCall := Within.call (procedure := self)
          (arguments := [.register 0, .register 4, .register 6]) (results := [9, 10]) (regs := r3) hcRun cont
        have digitBranch := Within.branch (test := .register 7) (b := true)
          (yes := .call self [.register 0, .register 4, .register 6] [9, 10]
            (.branch (.register 9) consResult RegisterCoordinate.rejected))
          (no := RegisterCoordinate.rejected)
          (by simpa [Atom.eval, hupdate] using h7) selfCall
        have digitCall := Within.call (procedure := digit)
          (arguments := [.register 0, .register 3, .register 5]) (results := [7, 8]) (regs := r2) hdRun digitBranch
        have deltaLoad := Within.load (address := .register 2) (first := 5) (second := 6) (bit := 15)
          (branches := {CompiledTrie.failCases with cons := .call digit [.register 0, .register 3, .register 5] [7, 8] (afterDigit self)})
          (by simp [Atom.eval, r1, regs, loadRegisters, decoded, initialRegisters]) dc digitCall
        have wordLoad := Within.load (address := .register 1) (first := 3) (second := 4) (bit := 15)
          (branches := {CompiledTrie.failCases with
            nil := .load (.register 2) 5 6 15 {CompiledTrie.failCases with nil := .ret [.flag true, .null]}
            cons := .load (.register 2) 5 6 15 {CompiledTrie.failCases with cons := .call digit [.register 0, .register 3, .register 5] [7, 8] (afterDigit self)}})
          (by simp [Atom.eval, regs, initialRegisters]) wc deltaLoad
        simpa only [hself, wordsBody] using
          wordLoad.mono (b := 500 * (n + 1) * (w :: ws).length + 25) (by simp; nlinarith)

end WeightedMIS.RegisterCoordinates
