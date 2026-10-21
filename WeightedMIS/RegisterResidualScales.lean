module

public import WeightedMIS.RegisterResidualPhase
public import WeightedMIS.ResidualListScales

/-! # Finite register code iterating the binary capacity scales -/

@[expose] public section

namespace WeightedMIS.RegisterResidualScales

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ResidualWords WeightedMIS.ExpandedWords

variable {p : ℕ}

def iterBody (self phase halve : Fin p) : Command p :=
  .call phase [.register 0, .register 1, .register 2, .register 3, .register 4, .register 5] [8, 9]
    (.call halve [.register 1] [10]
      (.call self [.register 8, .register 10, .register 2, .register 3, .register 4, .register 5,
          .register 11, .register 9] [12, 13]
        (.ret [.register 12, .register 13])))

/-- Inputs: table, scale, vertices, source, sink, attempt-list, shape, last cut.
Every loaded shape bit triggers one phase and one represented halving. -/
def scalesBody (self phase halve : Fin p) : Command p :=
  .load (.register 6) 11 15 14 (RegisterAdder.nilBitCases
    (.ret [.register 0, .register 7]) (iterBody self phase halve))

def stepBudget (n b nodes entries attempts : ℕ) : ℕ :=
  RegisterResidualPhase.budget n b nodes entries attempts + 28 * b + 80

def budget (n b nodes entries attempts rounds : ℕ) : ℕ :=
  stepBudget n b nodes entries attempts * rounds + 15

theorem compiled (code : Code p) (d : RegisterResidualPhase.Procedures p) (hm : d.Matches code)
    (self phase halve shift : Fin p)
    (hself : code self = scalesBody self phase halve)
    (hphase : code phase = RegisterResidualPhase.phaseBody phase d.search d.reach.member d.reach.lookup d.tableUpdate)
    (hhalve : code halve = RegisterHalve.halveBody shift)
    (hshift : code shift = RegisterHalve.shiftBody shift)
    {n b k : ℕ} {h : Heap} (hh : Valid h) {table : List (Arc n b)} {delta : Bits b}
    {nodes attempts seen : List (Bits n)} {source sink : Bits n} {shape : Bits k}
    {tablep dp np sp tp ap fp cp : Ptr}
    (ht : TableAt h tablep table) (hd : BitsAt h dp delta) (hn : WordsAt h np nodes)
    (hs : BitsAt h sp source) (hterm : BitsAt h tp sink) (ha : WordsAt h ap attempts)
    (hf : BitsAt h fp shape) (hc : WordsAt h cp seen) :
    ∃ out result cutp, Extends h out ∧ Valid out ∧
      TableAt out result (ResidualListScales.scales nodes source sink attempts.length k delta table seen).table ∧
      WordsAt out cutp (ResidualListScales.scales nodes source sink attempts.length k delta table seen).seen ∧
      Within code h (initialRegisters [.pointer tablep, .pointer dp, .pointer np, .pointer sp, .pointer tp,
          .pointer ap, .pointer fp, .pointer cp])
        (code self) [.pointer result, .pointer cutp] out (budget n b nodes.length table.length attempts.length k) := by
  induction shape generalizing h table delta seen tablep dp np sp tp ap fp cp with
  | nil =>
    cases hf with
    | nil cell =>
      let regs := initialRegisters [Value.pointer tablep, .pointer dp, .pointer np, .pointer sp, .pointer tp,
        .pointer ap, .pointer fp, .pointer cp]
      have ret : Within code h (loadRegisters regs 11 15 14 .nil) (.ret [.register 0, .register 7])
          [.pointer tablep, .pointer cp] h 5 := by
        simpa [regs, initialRegisters, loadRegisters, decoded, values, Atom.eval] using
          Within.ret code h (loadRegisters regs 11 15 14 .nil) [.register 0, .register 7]
      have ld := Within.load (address := .register 6) (first := 11) (second := 15) (bit := 14)
        (branches := RegisterAdder.nilBitCases (.ret [.register 0, .register 7]) (iterBody self phase halve))
        (by simp [regs, initialRegisters, Atom.eval]) cell ret
      refine ⟨h, tablep, cp, .refl h, hh, ht, hc, ?_⟩
      simpa [hself, scalesBody, budget] using ld
  | @cons k bit shape ih =>
    cases hf with
    | @cons _ ftail _ _ _ fcell hftail =>
      obtain ⟨mid, resultp, seenp, he1, hv1, htable, hseen, phaseRun⟩ :=
        RegisterResidualPhase.compiled code d hm phase hphase hh ht hd hn hs hterm ha
      obtain ⟨halfHeap, halfp, he2, hv2, hhalf, halveRun⟩ :=
        RegisterHalve.halve_compiled code shift hshift hv1 (hd.mono he1)
      have he12 := he1.trans he2
      let r := ResidualListPhase.phase delta nodes source sink attempts.length table
      have htr : TableAt halfHeap resultp r.table := htable.mono he2
      have hcr : WordsAt halfHeap seenp r.seen := hseen.mono he2
      obtain ⟨out, result, cutp, he3, ho, houtTable, houtCut, child⟩ := ih hv2 htr hhalf
        (hn.mono he12) (hs.mono he12) (hterm.mono he12) (ha.mono he12) (hftail.mono he12) hcr
      let regs := initialRegisters [Value.pointer tablep, .pointer dp, .pointer np, .pointer sp, .pointer tp,
        .pointer ap, .pointer fp, .pointer cp]
      let r1 := loadRegisters regs 11 15 14 (.bit bit ftail)
      let r2 := bindResults r1 [8, 9] [.pointer resultp, .pointer seenp]
      let r3 := bindResults r2 [10] [.pointer halfp]
      let r4 := bindResults r3 [12, 13] [.pointer result, .pointer cutp]
      have ret : Within code out r4 (.ret [.register 12, .register 13]) [.pointer result, .pointer cutp] out 5 := by
        simpa [r4, bindResults, values, Atom.eval] using Within.ret code out r4 [.register 12, .register 13]
      have argsR : values r3 [.register 8, .register 10, .register 2, .register 3, .register 4, .register 5,
          .register 11, .register 9] = [.pointer resultp, .pointer halfp, .pointer np, .pointer sp, .pointer tp,
            .pointer ap, .pointer ftail, .pointer seenp] := by
        simp [r3, r2, r1, regs, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
      have hlen : r.table.length = table.length := ResidualListPhase.phase_table_length _ _ _ _ _ _
      have recurse := Within.call (procedure := self) (regs := r3)
        (arguments := [.register 8, .register 10, .register 2, .register 3, .register 4, .register 5,
          .register 11, .register 9]) (results := [12, 13])
        (by simpa only [argsR, hlen] using child) ret
      have argsH : values r2 [.register 1] = [.pointer dp] := by
        simp [r2, r1, regs, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
      have hcall := Within.call (procedure := halve) (regs := r2)
        (arguments := [.register 1]) (results := [10])
        (by simpa only [argsH, hhalve] using halveRun) recurse
      have argsP : values r1 [.register 0, .register 1, .register 2, .register 3, .register 4, .register 5] =
          [.pointer tablep, .pointer dp, .pointer np, .pointer sp, .pointer tp, .pointer ap] := by
        simp [r1, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
      have pcall := Within.call (procedure := phase) (regs := r1)
        (arguments := [.register 0, .register 1, .register 2, .register 3, .register 4, .register 5]) (results := [8, 9])
        (by simpa only [argsP] using phaseRun) hcall
      have ld := Within.load (address := .register 6) (first := 11) (second := 15) (bit := 14)
        (branches := RegisterAdder.nilBitCases (.ret [.register 0, .register 7]) (iterBody self phase halve))
        (by simp [regs, initialRegisters, Atom.eval]) fcell pcall
      refine ⟨out, result, cutp, he12.trans he3, ho, houtTable, houtCut, ?_⟩
      simpa only [hself, scalesBody, iterBody] using ld.mono
        (b := budget n b nodes.length table.length attempts.length (k + 1))
        (by simp only [budget, stepBudget, List.length_cons, List.length_nil, Nat.mul_add, Nat.mul_one]; omega)

end WeightedMIS.RegisterResidualScales
