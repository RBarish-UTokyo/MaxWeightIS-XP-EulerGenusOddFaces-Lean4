module

public import WeightedMIS.RegisterResidualScales
public import WeightedMIS.RegisterPhaseAttempts
public import WeightedMIS.ResidualScalesRefinement

/-!
# Finite register maximum-flow solver on a stored residual table

The solver procedure has inputs `[table, nodes, source, sink, shape]`, where
`shape` is any word of the capacity width `b`. It

1. builds the leading scale `RegisterHalve.powerTop b` from the shape word,
2. builds the attempt list `List.replicate (2 * N^2 + 1) source`, `N` the number
   of vertex words,
3. runs the scale loop for `b` rounds (one per shape bit), starting with the
   empty carried cut (the null pointer, cell `0`),

and returns `[table', cut]`. The output is exactly `ResidualListScales.solve`
with `2 * N^2 + 1` attempts. Combined with
`ResidualScalesRefinement.solve_matches_length`, the stored output represents
the flow and cut of `MaxFlowScaling.solve`.
-/

@[expose] public section

namespace WeightedMIS.RegisterMaxFlowSolve

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ResidualWords WeightedMIS.ExpandedWords

structure Procedures (p : ℕ) where
  phase : RegisterResidualPhase.Procedures p
  attempts : RegisterPhaseAttempts.Procedures p
  phaseLoop : Fin p
  scales : Fin p
  halve : Fin p
  shift : Fin p
  power : Fin p
  zero : Fin p
  self : Fin p

variable {p : ℕ}

/-- Inputs: table, vertex words, source, sink, capacity-shape word.
Outputs: final residual table and last reached cut. -/
def solveBody (power attempts scales : Fin p) : Command p :=
  .call power [.register 4] [5]
    (.call attempts [.register 1, .register 2] [6]
      (.call scales [.register 0, .register 5, .register 1, .register 2, .register 3,
          .register 6, .register 4, .null] [7, 8]
        (.ret [.register 7, .register 8])))

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  d.phase.Matches code ∧
  d.attempts.Matches code ∧
  code d.phaseLoop = RegisterResidualPhase.phaseBody d.phaseLoop d.phase.search
    d.phase.reach.member d.phase.reach.lookup d.phase.tableUpdate ∧
  code d.scales = RegisterResidualScales.scalesBody d.scales d.phaseLoop d.halve ∧
  code d.halve = RegisterHalve.halveBody d.shift ∧
  code d.shift = RegisterHalve.shiftBody d.shift ∧
  code d.power = RegisterHalve.powerBody d.zero ∧
  code d.zero = RegisterZero.zeroBody d.zero ∧
  code d.self = solveBody d.power d.attempts.entry d.scales

/-- Event budget: `n` vertex-word width, `b` capacity width, `N` vertex words,
`E` table entries. -/
def solveBudget (n b N E : ℕ) : ℕ :=
  RegisterResidualScales.budget n b N E (2 * N ^ 2 + 1) b + (24 * b + 30) +
    RegisterPhaseAttempts.budget N + 30

theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {n b : ℕ} {h : Heap} (hh : Valid h) {table : List (Arc n b)}
    {nodes : List (Bits n)} {source sink : Bits n} {shape : Bits b}
    {tablep np sp tp fp : Ptr}
    (ht : TableAt h tablep table) (hn : WordsAt h np nodes)
    (hs : BitsAt h sp source) (hterm : BitsAt h tp sink) (hf : BitsAt h fp shape) :
    ∃ out result cutp, Extends h out ∧ Valid out ∧
      TableAt out result
        (ResidualListScales.solve nodes source sink (2 * nodes.length ^ 2 + 1) table).table ∧
      WordsAt out cutp
        (ResidualListScales.solve nodes source sink (2 * nodes.length ^ 2 + 1) table).seen ∧
      Within code h (initialRegisters [.pointer tablep, .pointer np, .pointer sp, .pointer tp,
          .pointer fp])
        (code d.self) [.pointer result, .pointer cutp] out
        (solveBudget n b nodes.length table.length) := by
  obtain ⟨hphase, hattempts, hloop, hscales, hhalve, hshift, hpower, hzero, hself⟩ := hm
  -- leading scale
  obtain ⟨h1, dp, e1, v1, hd, powerRun⟩ :=
    RegisterHalve.power_compiled code d.zero hzero hh hf
  -- attempt list
  obtain ⟨h2, ap, e2, v2, ha, attemptsRun⟩ :=
    RegisterPhaseAttempts.compiled code d.attempts hattempts v1 (hn.mono e1) (hs.mono e1)
  have e12 := e1.trans e2
  -- scale loop, carried cut starts empty
  have hc : WordsAt h2 0 ([] : List (Bits n)) := WordsAt.nil v2.1
  obtain ⟨out, result, cutp, e3, v3, htable, hcut, scalesRun⟩ :=
    RegisterResidualScales.compiled code d.phase hphase d.scales d.phaseLoop d.halve d.shift
      hscales hloop hhalve hshift v2 (ht.mono e12) (hd.mono e2) (hn.mono e12) (hs.mono e12)
      (hterm.mono e12) ha (hf.mono e12) hc
  have hlen : (List.replicate (2 * nodes.length ^ 2 + 1) source).length =
      2 * nodes.length ^ 2 + 1 := List.length_replicate
  rw [hlen] at htable hcut scalesRun
  refine ⟨out, result, cutp, e12.trans e3, v3, htable, hcut, ?_⟩
  let regs := initialRegisters [Value.pointer tablep, .pointer np, .pointer sp, .pointer tp,
    .pointer fp]
  let r1 := bindResults regs [5] [.pointer dp]
  let r2 := bindResults r1 [6] [.pointer ap]
  let r3 := bindResults r2 [7, 8] [.pointer result, .pointer cutp]
  have ret : Within code out r3 (.ret [.register 7, .register 8])
      [.pointer result, .pointer cutp] out 5 := by
    simpa [r3, bindResults, values, Atom.eval] using
      Within.ret code out r3 [.register 7, .register 8]
  have argsS : values r2 [.register 0, .register 5, .register 1, .register 2, .register 3,
      .register 6, .register 4, .null] =
      [.pointer tablep, .pointer dp, .pointer np, .pointer sp, .pointer tp, .pointer ap,
        .pointer fp, .pointer 0] := by
    simp [r2, r1, regs, bindResults, initialRegisters, values, Atom.eval]
  have scall := Within.call (procedure := d.scales) (regs := r2)
    (arguments := [.register 0, .register 5, .register 1, .register 2, .register 3,
      .register 6, .register 4, .null]) (results := [7, 8])
    (by simpa only [argsS] using scalesRun) ret
  have argsA : values r1 [.register 1, .register 2] = [.pointer np, .pointer sp] := by
    simp [r1, regs, bindResults, initialRegisters, values, Atom.eval]
  have acall := Within.call (procedure := d.attempts.entry) (regs := r1)
    (arguments := [.register 1, .register 2]) (results := [6])
    (by simpa only [argsA] using attemptsRun) scall
  have argsP : values regs [.register 4] = [.pointer fp] := by
    simp [regs, initialRegisters, values, Atom.eval]
  have pcall := Within.call (procedure := d.power) (regs := regs)
    (arguments := [.register 4]) (results := [5])
    (by simpa only [argsP, hpower] using powerRun) acall
  rw [hself]
  exact pcall.mono (by simp only [solveBudget, List.length_cons, List.length_nil]; omega)

/-- The solver budget is a polynomial of degree two in the word widths, four in
the number of vertex words and one in the number of table entries. -/
theorem solveBudget_le (n b N E : ℕ) :
    solveBudget n b N E ≤ 1000 * (n + b + 1) ^ 2 * (N + 1) ^ 4 * (E + 1) := by
  have key : 1000 * (n + b + 1) ^ 2 * (N + 1) ^ 4 * (E + 1) = solveBudget n b N E + (
      845 + 1000 * E + 3840 * N + 4000 * N * E + 5920 * N ^ 2 + 6000 * N ^ 2 * E +
      4000 * N ^ 3 + 4000 * N ^ 3 * E + 1000 * N ^ 4 + 1000 * N ^ 4 * E + 1228 * b +
      1478 * b * E + 7280 * b * N + 6996 * b * N * E + 11192 * b * N ^ 2 +
      11238 * b * N ^ 2 * E + 7280 * b * N ^ 3 + 6996 * b * N ^ 3 * E + 1860 * b * N ^ 4 +
      1760 * b * N ^ 4 * E + 972 * b ^ 2 + 506 * b ^ 2 * E + 4000 * b ^ 2 * N +
      3928 * b ^ 2 * N * E + 6000 * b ^ 2 * N ^ 2 + 5506 * b ^ 2 * N ^ 2 * E +
      4000 * b ^ 2 * N ^ 3 + 3928 * b ^ 2 * N ^ 3 * E + 1000 * b ^ 2 * N ^ 4 +
      1000 * b ^ 2 * N ^ 4 * E + 2000 * n + 2000 * n * E + 8000 * n * N + 8000 * n * N * E +
      12000 * n * N ^ 2 + 12000 * n * N ^ 2 * E + 8000 * n * N ^ 3 + 8000 * n * N ^ 3 * E +
      2000 * n * N ^ 4 + 2000 * n * N ^ 4 * E + 1856 * n * b + 2000 * n * b * E +
      7784 * n * b * N + 7568 * n * b * N * E + 11784 * n * b * N ^ 2 +
      11856 * n * b * N ^ 2 * E + 7784 * n * b * N ^ 3 + 7568 * n * b * N ^ 3 * E +
      1928 * n * b * N ^ 4 + 1856 * n * b * N ^ 4 * E + 1000 * n ^ 2 + 1000 * n ^ 2 * E +
      4000 * n ^ 2 * N + 4000 * n ^ 2 * N * E + 6000 * n ^ 2 * N ^ 2 +
      6000 * n ^ 2 * N ^ 2 * E + 4000 * n ^ 2 * N ^ 3 + 4000 * n ^ 2 * N ^ 3 * E +
      1000 * n ^ 2 * N ^ 4 + 1000 * n ^ 2 * N ^ 4 * E) := by
    simp only [solveBudget, RegisterResidualScales.budget, RegisterResidualScales.stepBudget,
      RegisterResidualPhase.budget, RegisterResidualPhase.stepBudget,
      RegisterResidualSearch.budget, RegisterResidualReach.budget,
      RegisterResidualReach.stepBudget, RegisterResidualCrossing.budget,
      RegisterResidualPredicate.budget, RegisterMembership.budget, RegisterRouteLookup.budget,
      RegisterResidualTableUpdate.budget, RegisterResidualUpdate.budget,
      RegisterArcMembership.budget, RegisterPhaseAttempts.budget]
    ring
  rw [key]
  exact Nat.le_add_right _ _

/-- For a complete table of `N^2` entries the budget is `O((n + b)^2 N^6)`. -/
theorem solveBudget_square_le (n b N : ℕ) :
    solveBudget n b N (N ^ 2) ≤ 1000 * (n + b + 1) ^ 2 * (N + 1) ^ 6 := by
  have hE : N ^ 2 + 1 ≤ (N + 1) ^ 2 := by
    have hs : (N + 1) ^ 2 = N ^ 2 + 2 * N + 1 := by ring
    omega
  calc solveBudget n b N (N ^ 2) ≤ 1000 * (n + b + 1) ^ 2 * (N + 1) ^ 4 * (N ^ 2 + 1) :=
        solveBudget_le n b N (N ^ 2)
    _ ≤ 1000 * (n + b + 1) ^ 2 * (N + 1) ^ 4 * (N + 1) ^ 2 := Nat.mul_le_mul_left _ hE
    _ = 1000 * (n + b + 1) ^ 2 * (N + 1) ^ 6 := by ring

/-- On the stored complete capacity table of a network with distinct terminals,
the solver returns words representing the flow and cut of `MaxFlowScaling.solve`. -/
theorem compiled_solve (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {V : Type*} [Fintype V] [DecidableEq V] {n b : ℕ} (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (c : V → V → ℕ) (s t : V) (hst : s ≠ t) (nodes : List V) (complete : ∀ v, v ∈ nodes)
    (hlen : nodes.length = Fintype.card V) (hb : 0 < b)
    (hwidth : ∀ u v, c u v + c v u < 2 ^ b)
    (caps : V → V → Bits b) (hcap : ∀ u v, (caps u v).value = c u v)
    {h : Heap} (hh : Valid h) {shape : Bits b} {tablep np sp tp fp : Ptr}
    (ht : TableAt h tablep
      ((nodes.product nodes).map (ResidualCrossingRefinement.encodeArc enc caps)))
    (hn : WordsAt h np (nodes.map enc)) (hs : BitsAt h sp (enc s))
    (hterm : BitsAt h tp (enc t)) (hf : BitsAt h fp shape) :
    ∃ out result cutp, ∃ words : ResidualListPhase.Result n b, Extends h out ∧ Valid out ∧
      TableAt out result words.table ∧ WordsAt out cutp words.seen ∧
      ResidualPhaseRefinement.Represents enc nodes c s t words
        (MaxFlowScaling.solve c nodes s t) ∧
      Within code h (initialRegisters [.pointer tablep, .pointer np, .pointer sp, .pointer tp,
          .pointer fp])
        (code d.self) [.pointer result, .pointer cutp] out
        (solveBudget n b nodes.length (nodes.length ^ 2)) := by
  obtain ⟨out, result, cutp, he, hv, htable, hcut, run⟩ := compiled code d hm hh ht hn hs hterm hf
  have hrep := ResidualScalesRefinement.solve_matches_length enc hinj c s t hst nodes complete
    hlen hb hwidth caps hcap
  have hentries : ((nodes.product nodes).map
      (ResidualCrossingRefinement.encodeArc enc caps)).length = (nodes.map enc).length ^ 2 := by
    rw [List.length_map, List.length_map]
    exact (List.length_product nodes nodes).trans (by ring)
  rw [hentries, List.length_map] at run
  exact ⟨out, result, cutp, _, he, hv, htable, hcut, hrep, run⟩

end WeightedMIS.RegisterMaxFlowSolve
