module

public import WeightedMIS.RegisterNetworkTable
public import WeightedMIS.RegisterMaxFlowSolve

/-!
# Solving the stored double-cover network

From the vertex words, the edge list, the scaled weight words, the large
capacity word and the zero capacity word, the procedure builds the node records,
the node word list and the complete capacity table, and runs the register
maximum-flow solver with the zero word as capacity-shape word. The returned
final residual table and reached cut represent the flow and cut of
`MaxFlowScaling.solve` on `MaxFlowPreprocessing.matrix adj μ`; for the scaled
weights of a rational weight vector this is `MaxFlowPreprocessing.networkResult`.
-/

@[expose] public section

namespace WeightedMIS.RegisterNetworkSolve

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords WeightedMIS.ResidualWords
open WeightedMIS.DoubleCoverNetwork WeightedMIS.MaxFlowPreprocessing
open WeightedMIS.GraphReachEncoded WeightedMIS.NetworkWords
open WeightedMIS.RegisterNetworkNodes WeightedMIS.RegisterAdjacencyScan WeightedMIS.RegisterNetworkTable
open scoped BigOperators

structure Procedures (p : ℕ) where
  nodes : RegisterNetworkNodes.Procedures p
  table : RegisterNetworkTable.Procedures p
  solve : RegisterMaxFlowSolve.Procedures p
  self : Fin p

variable {p : ℕ}

/-- Arguments: vertex words, edges, scaled weights, large capacity, zero.
Results: final residual table, reached cut. -/
def solveNetBody (nodes words table solve : Fin p) : Command p :=
  .call nodes [.register 0, .register 2, .register 4] [5, 6, 7]
    (.call words [.register 5, .null] [8]
      (.call table [.register 5, .register 1, .register 3, .register 4] [9]
        (.call solve [.register 9, .register 8, .register 6, .register 7, .register 4] [10, 11]
          (.ret [.register 10, .register 11]))))

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  d.nodes.Matches code ∧ d.table.Matches code ∧ d.solve.Matches code ∧
  code d.self = solveNetBody d.nodes.self d.nodes.words d.table.self d.solve.self

def budget (W B m n : ℕ) : ℕ :=
  RegisterNetworkNodes.budget W n + (48 * (2 * n + 2) + 13) + RegisterNetworkTable.budget W m n +
    RegisterMaxFlowSolve.solveBudget (W + 2) B (2 * n + 2) ((2 * n + 2) ^ 2) + 60

theorem nodes_length' (n : ℕ) : (nodes n).length = 2 * n + 2 := by
  rw [nodes_eq]; simp; ring

theorem scales_seen_length {k b : ℕ} (nodes : List (Bits k)) (source sink : Bits k)
    (attempts rounds : ℕ) (delta : Bits b) (table : List (Arc k b)) (seen : List (Bits k))
    (hs : seen.length ≤ nodes.length + 1) :
    (ResidualListScales.scales nodes source sink attempts rounds delta table seen).seen.length ≤
      nodes.length + 1 := by
  induction rounds generalizing delta table seen with
  | zero => exact hs
  | succ rounds ih =>
    exact ih _ _ _ (ResidualListPhase.phase_seen_length _ _ _ _ _ _)

theorem solve_seen_length {k b : ℕ} (nodes : List (Bits k)) (source sink : Bits k)
    (attempts : ℕ) (table : List (Arc k b)) :
    (ResidualListScales.solve nodes source sink attempts table).seen.length ≤ nodes.length + 1 :=
  scales_seen_length _ _ _ _ _ _ _ _ (by simp)

theorem solve_table_length {k b : ℕ} (nodes : List (Bits k)) (source sink : Bits k)
    (attempts : ℕ) (table : List (Arc k b)) :
    (ResidualListScales.solve nodes source sink attempts table).table.length = table.length :=
  ResidualListScales.scales_table_length _ _ _ _ _ _ _ _

/-- The stored network represents the capacity-scaling result on the network
matrix of the scaled weights `μ`. The final residual table is exported. -/
theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {W B n m : ℕ} (hn : n < 2 ^ W) (hn0 : 0 < n) (hB : 0 < B)
    (left right : Fin m → Fin n) [DecidableRel (EdgeTransport.Adj left right)]
    (μ : Fin n → ℕ) (hbig : 1 + ∑ x, μ x < 2 ^ B)
    {h : Heap} (hh : Valid h) {vp ep mp bp zp : Ptr}
    (hv : WordsAt h vp (rangeWords W n)) (he : EdgeWordsAt h ep (edgeWords W left right))
    (hmu : WordsAt h mp ((List.finRange n).map (muWordOf B μ)))
    (hb : BitsAt h bp (word B (1 + ∑ x, μ x))) (hz : BitsAt h zp (word B 0)) :
    ∃ out tablep cutp, ∃ words : ResidualListPhase.Result (W + 2) B, Extends h out ∧ Valid out ∧
      TableAt out tablep words.table ∧ WordsAt out cutp words.seen ∧
      ResidualPhaseRefinement.Represents (nodeWord W) (nodes n)
        (matrix (EdgeTransport.Adj left right) μ) sourceNode sinkNode words
        (MaxFlowScaling.solve (matrix (EdgeTransport.Adj left right) μ) (nodes n)
          sourceNode sinkNode) ∧
      words.seen.length ≤ 2 * n + 3 ∧ words.table.length = (2 * n + 2) ^ 2 ∧
      Within code h (initialRegisters [.pointer vp, .pointer ep, .pointer mp, .pointer bp,
          .pointer zp]) (code d.self) [.pointer tablep, .pointer cutp] out (budget W B m n) := by
  obtain ⟨hnodes, htable, hsolve, hself⟩ := hm
  obtain ⟨h1, rp, sp, tp, e1, v1, hr, hs, ht, nodesRun⟩ :=
    RegisterNetworkNodes.compiled code d.nodes hnodes hn0 (muWordOf B μ) (word B 0) hh hv hmu hz
  obtain ⟨h2, np, e2, v2, hnp, wordsRun⟩ := words_compiled code d.nodes hnodes v1 hr
  obtain ⟨h3, tabp, e3, v3, htab, tableRun⟩ := RegisterNetworkTable.compiled code d.table htable
    hn left right μ v2 (hr.mono e2) (he.mono (e1.trans e2)) (hb.mono (e1.trans e2))
    (hz.mono (e1.trans e2))
  have e23 := e2.trans e3
  obtain ⟨out, result, cutp, e4, v4, hres, hcut, solveRun⟩ :=
    RegisterMaxFlowSolve.compiled code d.solve hsolve v3 htab (hnp.mono e3) (hs.mono e23)
      (ht.mono e23) (hz.mono (e1.trans e23))
  have hrep := ResidualScalesRefinement.solve_matches_length (nodeWord W)
    (nodeWord_value_injective hn) (matrix (EdgeTransport.Adj left right) μ)
    sourceNode sinkNode (by simp [sourceNode, sinkNode]) (nodes n) (nodes_complete n)
    (nodes_length n) hB (fun u v => lt_of_le_of_lt (matrix_pair_le _ μ u v) hbig)
    (capWord B (EdgeTransport.Adj left right) μ) (capWord_value _ μ hbig)
  have htlen : (((nodes n).product (nodes n)).map
      (arc W B (EdgeTransport.Adj left right) μ)).length = (2 * n + 2) ^ 2 := by
    rw [List.length_map]
    exact (List.length_product (nodes n) (nodes n)).trans (by rw [nodes_length']; ring)
  have hseen := solve_seen_length ((nodes n).map (nodeWord W)) (nodeWord W (sourceNode : Node (Fin n)))
    (nodeWord W (sinkNode : Node (Fin n))) (2 * ((nodes n).map (nodeWord W)).length ^ 2 + 1)
    (((nodes n).product (nodes n)).map (arc W B (EdgeTransport.Adj left right) μ))
  have htab' := solve_table_length ((nodes n).map (nodeWord W)) (nodeWord W (sourceNode : Node (Fin n)))
    (nodeWord W (sinkNode : Node (Fin n))) (2 * ((nodes n).map (nodeWord W)).length ^ 2 + 1)
    (((nodes n).product (nodes n)).map (arc W B (EdgeTransport.Adj left right) μ))
  rw [htlen, List.length_map, nodes_length'] at solveRun
  refine ⟨out, result, cutp, _, e1.trans (e23.trans e4), v4, hres, hcut, hrep,
    by simpa [nodes_length'] using hseen, by simpa [nodes_length', htlen] using htab', ?_⟩
  rw [nodes_length'] at wordsRun
  let r0 := initialRegisters [Value.pointer vp, .pointer ep, .pointer mp, .pointer bp, .pointer zp]
  let r1 := bindResults r0 [5, 6, 7] [.pointer rp, .pointer sp, .pointer tp]
  let r2 := bindResults r1 [8] [.pointer np]
  let r3 := bindResults r2 [9] [.pointer tabp]
  let r4 := bindResults r3 [10, 11] [.pointer result, .pointer cutp]
  have last : Within code out r4 (.ret [.register 10, .register 11])
      [.pointer result, .pointer cutp] out 5 := by
    simpa [values, Atom.eval, r4, bindResults] using
      Within.ret code out r4 [.register 10, .register 11]
  have aS : values r3 [.register 9, .register 8, .register 6, .register 7, .register 4] =
      [.pointer tabp, .pointer np, .pointer sp, .pointer tp, .pointer zp] := by
    simp [values, Atom.eval, r3, r2, r1, r0, bindResults, initialRegisters]
  have cS := Within.call (procedure := d.solve.self) (regs := r3)
    (arguments := [.register 9, .register 8, .register 6, .register 7, .register 4])
    (results := [10, 11]) (by simpa only [aS] using solveRun) last
  have aT : values r2 [.register 5, .register 1, .register 3, .register 4] =
      [.pointer rp, .pointer ep, .pointer bp, .pointer zp] := by
    simp [values, Atom.eval, r2, r1, r0, bindResults, initialRegisters]
  have cT := Within.call (procedure := d.table.self) (regs := r2)
    (arguments := [.register 5, .register 1, .register 3, .register 4]) (results := [9])
    (by simpa only [aT] using tableRun) cS
  have aW : values r1 [.register 5, .null] = [.pointer rp, .pointer 0] := by
    simp [values, Atom.eval, r1, bindResults]
  have cW := Within.call (procedure := d.nodes.words) (regs := r1)
    (arguments := [.register 5, .null]) (results := [8]) (by simpa only [aW] using wordsRun) cT
  have aN : values r0 [.register 0, .register 2, .register 4] =
      [.pointer vp, .pointer mp, .pointer zp] := by
    simp [values, Atom.eval, r0, initialRegisters]
  have cN := Within.call (procedure := d.nodes.self) (regs := r0)
    (arguments := [.register 0, .register 2, .register 4]) (results := [5, 6, 7])
    (by simpa only [aN] using nodesRun) cW
  rw [hself]
  exact cN.mono (by simp [budget]; omega)

/-- For the scaled weights of a rational weight vector the represented result is
`MaxFlowPreprocessing.networkResult`. -/
theorem solve_eq_networkResult {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (w : Fin n → ℚ) :
    MaxFlowScaling.solve (matrix adj (scaledWeight w)) (nodes n) sourceNode sinkNode =
      networkResult adj (List.finRange n) w := rfl

theorem budget_le (W B m n : ℕ) :
    budget W B m n ≤ 2000 * (W + B + 3) ^ 2 * (m + 1) * (2 * n + 3) ^ 6 := by
  have hs := RegisterMaxFlowSolve.solveBudget_square_le (W + 2) B (2 * n + 2)
  have h1 : W + 2 + B + 1 = W + B + 3 := by ring
  have h2 : 2 * n + 2 + 1 = 2 * n + 3 := by ring
  rw [h1, h2] at hs
  simp only [budget, RegisterNetworkNodes.budget, RegisterNetworkTable.budget,
    RegisterNetworkTable.outerItemBudget, RegisterNetworkTable.innerBudget,
    RegisterNetworkTable.innerItemBudget, RegisterNetworkTable.capBudget,
    RegisterAdjacencyScan.budget, RegisterAdjacencyScan.itemBudget]
  generalize RegisterMaxFlowSolve.solveBudget (W + 2) B (2 * n + 2) ((2 * n + 2) ^ 2) = S at hs ⊢
  generalize hK : W + B + 3 = K at hs ⊢
  generalize hN : 2 * n + 3 = N at hs ⊢
  have hWK : W ≤ K := by omega
  have hx : 2 * n + 2 ≤ N := by omega
  have hN3 : 3 ≤ N := by omega
  have hK3 : 3 ≤ K := by omega
  -- the table part
  have ht : (((144 * W + 160 + 30) * m + 40 + 100 + 130 + 27) * (2 * n + 2) + 13 + 40 + 27) *
      (2 * n + 2) ≤ (500 * K * (m + 1)) * N * N := by
    have a : (144 * W + 160 + 30) * m + 40 + 100 + 130 + 27 ≤ 400 * K * (m + 1) := by nlinarith
    have b1 : ((144 * W + 160 + 30) * m + 40 + 100 + 130 + 27) * (2 * n + 2) ≤
        400 * K * (m + 1) * N := Nat.mul_le_mul a hx
    have b2 : 1 ≤ K * (m + 1) * N := by
      have : 0 < K * (m + 1) * N := by positivity
      omega
    have b : ((144 * W + 160 + 30) * m + 40 + 100 + 130 + 27) * (2 * n + 2) + 13 + 40 + 27 ≤
        500 * K * (m + 1) * N := by
      have e : 500 * K * (m + 1) * N = 400 * K * (m + 1) * N + 100 * (K * (m + 1) * N) := by ring
      rw [e]
      linarith
    exact Nat.mul_le_mul b hx
  have hK2 : K ≤ K ^ 2 := by nlinarith
  have hN6 : N * N ≤ N ^ 6 := by
    calc N * N = N ^ 2 := (sq N).symm
      _ ≤ N ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hKm : 500 * K * (m + 1) * N * N ≤ 500 * K ^ 2 * (m + 1) * N ^ 6 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left (500 * (m + 1)) hK2) hN6
    calc 500 * K * (m + 1) * N * N = 500 * (m + 1) * K * (N * N) := by ring
      _ ≤ 500 * (m + 1) * K ^ 2 * N ^ 6 := this
      _ = 500 * K ^ 2 * (m + 1) * N ^ 6 := by ring
  have hbase : 1 ≤ K ^ 2 * (m + 1) * N ^ 6 := by
    have : 0 < K ^ 2 * (m + 1) * N ^ 6 := by positivity
    omega
  have hsmall : 24 * W + 200 * n + 300 + (48 * (2 * n + 2) + 13) + 60 + 60 ≤
      500 * K ^ 2 * (m + 1) * N ^ 6 := by
    have hK6 : K * N ≤ K ^ 2 * (m + 1) * N ^ 6 := by
      have a : K ≤ K ^ 2 * (m + 1) := by nlinarith
      have b : N ≤ N ^ 6 := by
        calc N = N ^ 1 := (pow_one N).symm
          _ ≤ N ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
      exact Nat.mul_le_mul a b
    have hl : 24 * W + 200 * n + 300 + (48 * (2 * n + 2) + 13) + 60 + 60 ≤ 500 * (K * N) := by
      nlinarith
    have e : 500 * K ^ 2 * (m + 1) * N ^ 6 = 500 * (K ^ 2 * (m + 1) * N ^ 6) := by ring
    rw [e]
    linarith
  have hS : S ≤ 1000 * K ^ 2 * (m + 1) * N ^ 6 := by
    calc S ≤ 1000 * K ^ 2 * N ^ 6 := hs
      _ ≤ 1000 * K ^ 2 * N ^ 6 * (m + 1) := Nat.le_mul_of_pos_right _ (by omega)
      _ = 1000 * K ^ 2 * (m + 1) * N ^ 6 := by ring
  nlinarith

end WeightedMIS.RegisterNetworkSolve
