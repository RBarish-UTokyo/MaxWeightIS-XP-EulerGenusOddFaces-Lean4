module

public import WeightedMIS.RegisterEdgeCosts

/-!
# Compiled integer edge costs of a graph

The procedure runs the compiled maximum-flow preprocessing
(`RegisterPreprocessing`) on the vertex words, edge records and weight row of
a graph, and then computes the cost word of every edge from the exported
final residual table and large capacity word (`RegisterEdgeCosts`). With no
vertices there are no edges and the empty list is returned.

For nonnegative weights the output words are the canonical words of
`IntegerEdgeCosts.integerCost left right (List.finRange m) (List.finRange n)
weights e`, in edge order, at the capacity width `NetworkWeights.width w n`
(every cost is below `2 ^ width w n`). No optimality hypothesis is used. The
class words of the preprocessing point are returned as well.
-/

@[expose] public section

namespace WeightedMIS.RegisterEdgeCostProgram

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.ResidualWords
open WeightedMIS.GraphReachEncoded WeightedMIS.NetworkWords WeightedMIS.NetworkWeights
open WeightedMIS.RegisterAdjacencyScan WeightedMIS.RegisterCutReadback
open WeightedMIS.RegisterNetworkWeights (allocate_fits)

structure Procedures (p : ℕ) where
  prep : RegisterPreprocessing.Procedures p
  costs : RegisterEdgeCosts.Procedures p
  self : Fin p

variable {p : ℕ}

def afterBody (costs : Fin p) : Command p :=
  .load (.register 0) 8 9 15 { CompiledTrie.failCases with
    nil := .allocate 7 .nil (.ret [.register 7, .register 3])
    cons := .call costs [.register 1, .register 4, .register 6] [7]
      (.ret [.register 7, .register 3]) }

/-- Arguments: vertex words, edge records, weight row. Results: cost words,
class words. -/
def programBody (prep costs : Fin p) : Command p :=
  .call prep [.register 0, .register 1, .register 2] [3, 4, 5, 6] (afterBody costs)

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  d.prep.Matches code ∧ d.costs.Matches code ∧
  code d.self = programBody d.prep.self d.costs.self

def costsBudget (W w n m : ℕ) : ℕ :=
  RegisterEdgeCosts.budget W (width w n) m ((2 * n + 2) ^ 2)

def budget (W w n m : ℕ) : ℕ :=
  RegisterPreprocessing.budget W w n m + costsBudget W w n m + 40

/-- Main theorem: for nonnegative weights the stored cost words are the
canonical words of the integer edge costs. -/
theorem edgeCosts_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {W w n m : ℕ} (hn : n < 2 ^ W) (left right : Fin m → Fin n)
    (weights : Fin n → ℚ) (hw : ∀ v, 0 ≤ weights v) (q : Fin n → BinaryRational.Word w)
    (hq : ∀ v, BinaryRational.Canonical (q v)) (hval : ∀ v, (q v).value = weights v)
    {h : Heap} (hh : Valid h) {vp ep wp : Ptr}
    (hv : WordsAt h vp (rangeWords W n)) (he : EdgeWordsAt h ep (edgeWords W left right))
    (hwp : RegisterRationalRow.RowAt h wp ((List.finRange n).map q)) :
    ∃ out cp zp, Extends h out ∧ Valid out ∧
      WordsAt out cp ((List.finRange m).map fun e => word (width w n)
        (IntegerEdgeCosts.integerCost left right (List.finRange m) (List.finRange n)
          weights e)) ∧
      (∀ e, IntegerEdgeCosts.integerCost left right (List.finRange m) (List.finRange n)
          weights e < 2 ^ width w n) ∧
      WordsAt out zp ((List.finRange n).map fun v =>
        classWord (OriginalReduction.preprocessingPoint (left := left) (right := right)
          weights (List.finRange n) v)) ∧
      Within code h (initialRegisters [.pointer vp, .pointer ep, .pointer wp]) (code d.self)
        [.pointer cp, .pointer zp] out (budget W w n m) := by
  obtain ⟨hprep, hcosts, hself⟩ := hm
  obtain ⟨H1, zp, tablep, cutp, bigp, e1, v1, hz, hpos, prepRun⟩ :=
    RegisterPreprocessing.preprocessing_compiled code d.prep hprep hn left right weights q hq
      hval hh hv he hwp
  let r0 := initialRegisters [Value.pointer vp, .pointer ep, .pointer wp]
  let r1 := bindResults r0 [3, 4, 5, 6] [.pointer zp, .pointer tablep, .pointer cutp,
    .pointer bigp]
  have aP : values r0 [.register 0, .register 1, .register 2] =
      [.pointer vp, .pointer ep, .pointer wp] := by
    simp [values, Atom.eval, r0, initialRegisters]
  have g3 : r1 3 = .pointer zp := by simp [r1, bindResults]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- no vertices, hence no edges
    obtain rfl : m = 0 := by
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · exact hm0
      · exact (left ⟨0, hm0⟩).elim0
    have cell : H1[vp]? = some .nil := by
      have : rangeWords W 0 = [] := rfl
      rw [this] at hv
      exact e1.lookup (WordsAt.nil_iff.mp hv)
    obtain ⟨e2, v2, c2⟩ := allocate_fits v1 (c := .nil)
      (by intro x hx; simp [Cell.references] at hx)
    refine ⟨H1 ++ [.nil], H1.length, zp, e1.trans e2, v2, by simpa using WordsAt.nil c2,
      fun e => e.elim0, hz.mono e2, ?_⟩
    let s1 := loadRegisters r1 8 9 15 .nil
    have last : Within code (H1 ++ [.nil]) (Function.update s1 7 (.pointer H1.length))
        (.ret [.register 7, .register 3]) [.pointer H1.length, .pointer zp] (H1 ++ [.nil]) 5 := by
      simpa [values, Atom.eval, s1, loadRegisters, decoded, g3] using
        Within.ret code (H1 ++ [.nil]) (Function.update s1 7 (.pointer H1.length))
          [.register 7, .register 3]
    have a := Within.allocate (regs := s1) (dst := 7) (h := H1) (expr := .nil) (c := .nil)
      (by simp [CellExpr.eval]) last
    have l := Within.load (regs := r1) (address := .register 0) (first := 8) (second := 9)
      (bit := 15) (branches := { CompiledTrie.failCases with
        nil := .allocate 7 .nil (.ret [.register 7, .register 3])
        cons := .call d.costs.self [.register 1, .register 4, .register 6] [7]
          (.ret [.register 7, .register 3]) })
      (by simp [Atom.eval, r1, r0, bindResults, initialRegisters]) cell a
    have c := Within.call (procedure := d.prep.self) (regs := r0)
      (arguments := [.register 0, .register 1, .register 2]) (results := [3, 4, 5, 6])
      (by simpa only [aP] using prepRun) l
    rw [hself]
    exact c.mono (by simp [budget, CellExpr.args]; omega)
  · obtain ⟨words, htab, -, hbig, hrep, -, htabLen⟩ := hpos hn0
    have hwpos : 0 < w := width_pos_of_canonical (q ⟨0, hn0⟩) (hq ⟨0, hn0⟩)
    have hB := width_bound q hq hwpos
    obtain ⟨caps, htable, hcaps⟩ :=
      EdgeCostWords.transport_eq_sub left right weights hw q hrep
    obtain ⟨H2, cp, e2, v2, hcp, costRun⟩ := RegisterEdgeCosts.compiled code d.costs hcosts v1
      (he.mono e1) htab hbig
    have hzero : (Bits.subtract (word (width w n) (big q)) (word (width w n) (big q))).1 =
        word (width w n) 0 := by
      apply eq_word_of_value
      rw [(Bits.subtract_value_of_le _ _ le_rfl).2, Nat.sub_self]
    rw [hzero, htable, EdgeCostWords.costWords_eq hn left right weights q hB caps hcaps] at hcp
    have hT := EdgeCostWords.T_le left right weights q caps hcaps
    refine ⟨H2, cp, zp, e1.trans e2, v2, hcp, fun e => ?_, hz.mono e2, ?_⟩
    · have := EdgeCostWords.integerCost_le left right weights q e hT
      omega
    · obtain ⟨x0, rest, cell0⟩ : ∃ x0 rest, H1[vp]? = some (.cons x0 rest) := by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        obtain ⟨ptrs, hl, hr⟩ := hv
        rw [rangeWords, List.finRange_succ, List.map_cons] at hr
        cases hr with
        | cons _ _ =>
          cases hl with
          | cons cell _ => exact ⟨_, _, e1.lookup cell⟩
      have hlen : (edgeWords W left right).length = m := by simp [edgeWords]
      rw [hlen, htabLen] at costRun
      let s1 := loadRegisters r1 8 9 15 (.cons x0 rest)
      let s2 := bindResults s1 [7] [.pointer cp]
      have last : Within code H2 s2 (.ret [.register 7, .register 3])
          [.pointer cp, .pointer zp] H2 5 := by
        simpa [values, Atom.eval, s2, s1, bindResults, loadRegisters, decoded, g3] using
          Within.ret code H2 s2 [.register 7, .register 3]
      have aC : values s1 [.register 1, .register 4, .register 6] =
          [.pointer ep, .pointer tablep, .pointer bigp] := by
        simp [values, Atom.eval, s1, r1, r0, bindResults, loadRegisters, decoded,
          initialRegisters]
      have cC := Within.call (procedure := d.costs.self) (regs := s1)
        (arguments := [.register 1, .register 4, .register 6]) (results := [7])
        (by simpa only [aC] using costRun) last
      have l := Within.load (regs := r1) (address := .register 0) (first := 8) (second := 9)
        (bit := 15) (branches := { CompiledTrie.failCases with
          nil := .allocate 7 .nil (.ret [.register 7, .register 3])
          cons := .call d.costs.self [.register 1, .register 4, .register 6] [7]
            (.ret [.register 7, .register 3]) })
        (by simp [Atom.eval, r1, r0, bindResults, initialRegisters]) cell0 cC
      have c := Within.call (procedure := d.prep.self) (regs := r0)
        (arguments := [.register 0, .register 1, .register 2]) (results := [3, 4, 5, 6])
        (by simpa only [aP] using prepRun) l
      rw [hself]
      exact c.mono (by simp [budget, costsBudget]; omega)

/-! ## Polynomial event bound -/

theorem costsBudget_le (W w n m : ℕ) :
    costsBudget W w n m ≤ 4600 * ((W + 3) * (w + 2) * (n + m + 2) ^ 3) := by
  have hws := RegisterNetworkWeights.width_succ_le w n
  unfold costsBudget RegisterEdgeCosts.budget RegisterEdgeCosts.loopBudget
    RegisterEdgeCosts.itemBudget RegisterEdgeCosts.termBudget RegisterArcLookup.budget
    RegisterAdjacencyScan.budget RegisterAdjacencyScan.itemBudget
  generalize width w n = B at hws ⊢
  have hT : m ≤ n + m + 2 := by omega
  have hT1 : 1 ≤ n + m + 2 := by omega
  have ha1 : 1 ≤ w + 2 := by omega
  have hB : B ≤ (w + 2) * (n + m + 2) := by
    have : (w + 2) * (n + 2) ≤ (w + 2) * (n + m + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  set K := (W + 3) * (w + 2) * (n + m + 2) ^ 2 with hK
  have hcT : (W + 3) * (n + m + 2) ≤ K := by
    rw [hK]
    calc (W + 3) * (n + m + 2) = (W + 3) * 1 * (n + m + 2) * 1 := by ring
      _ ≤ (W + 3) * (w + 2) * (n + m + 2) * (n + m + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ ha1) le_rfl) hT1
      _ = _ := by ring
  have hct : (W + 3) * (2 * n + 2) ^ 2 ≤ 4 * K := by
    rw [hK]
    have : (2 * n + 2) ^ 2 ≤ 4 * (n + m + 2) ^ 2 := by
      calc (2 * n + 2) ^ 2 ≤ (2 * (n + m + 2)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 4 * (n + m + 2) ^ 2 := by ring
    calc (W + 3) * (2 * n + 2) ^ 2 ≤ (W + 3) * (4 * (n + m + 2) ^ 2) := Nat.mul_le_mul_left _ this
      _ = 4 * ((W + 3) * 1 * (n + m + 2) ^ 2) := by ring
      _ ≤ 4 * ((W + 3) * (w + 2) * (n + m + 2) ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ha1))
  have haT : (w + 2) * (n + m + 2) ≤ K := by
    rw [hK]
    calc (w + 2) * (n + m + 2) = 1 * (w + 2) * (n + m + 2) * 1 := by ring
      _ ≤ (W + 3) * (w + 2) * (n + m + 2) * (n + m + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))) hT1
      _ = _ := by ring
  have hWm : W * m ≤ K := le_trans (Nat.mul_le_mul (by omega) hT) hcT
  have hm : m ≤ K := le_trans (le_trans hT (by nlinarith)) hcT
  have hWt : W * (2 * n + 2) ^ 2 ≤ 4 * K := le_trans (Nat.mul_le_mul_right _ (by omega)) hct
  have ht : (2 * n + 2) ^ 2 ≤ 4 * K := le_trans (by nlinarith) hct
  have hW : W ≤ K := le_trans (by nlinarith) hcT
  have hBK : B ≤ K := le_trans hB haT
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (by positivity)
  generalize hX : (144 * W + 160 + 30) * m + 40 +
      2 * ((72 * (W + 2) + 150) * (2 * n + 2) ^ 2 + 15 + 137 * B + 120) + 36 * W +
        110 * B + 200 + 60 = X
  have hXK : X ≤ 4300 * K := by
    rw [← hX]
    have e1 : (144 * W + 160 + 30) * m = 144 * (W * m) + 190 * m := by ring
    have e2 : (72 * (W + 2) + 150) * (2 * n + 2) ^ 2 =
        72 * (W * (2 * n + 2) ^ 2) + 294 * (2 * n + 2) ^ 2 := by ring
    rw [e1, e2]
    omega
  have hXm : X * m ≤ 4300 * K * (n + m + 2) := Nat.mul_le_mul hXK hT
  have hfin : K * (n + m + 2) = (W + 3) * (w + 2) * (n + m + 2) ^ 3 := by rw [hK]; ring
  have hKT : K ≤ K * (n + m + 2) := Nat.le_mul_of_pos_right _ (by omega)
  have : 4300 * K * (n + m + 2) = 4300 * (K * (n + m + 2)) := by ring
  rw [← hfin]
  omega

/-- A clean polynomial bound on the event budget. -/
theorem budget_le (W w n m : ℕ) :
    budget W w n m ≤ 610000 * (w + 2) ^ 2 * (W + 3) ^ 2 * (n + m + 2) ^ 9 := by
  have hP := RegisterPreprocessing.budget_le W w n m
  have hC := costsBudget_le W w n m
  unfold budget
  have hle : (W + 3) * (w + 2) * (n + m + 2) ^ 3 ≤ (w + 2) ^ 2 * (W + 3) ^ 2 * (n + m + 2) ^ 9 := by
    have h1 : W + 3 ≤ (W + 3) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h2 : w + 2 ≤ (w + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h3 : (n + m + 2) ^ 3 ≤ (n + m + 2) ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
    calc (W + 3) * (w + 2) * (n + m + 2) ^ 3 ≤ (W + 3) ^ 2 * (w + 2) ^ 2 * (n + m + 2) ^ 9 :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      _ = _ := by ring
  have hone : 1 ≤ (w + 2) ^ 2 * (W + 3) ^ 2 * (n + m + 2) ^ 9 :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  have e : 610000 * (w + 2) ^ 2 * (W + 3) ^ 2 * (n + m + 2) ^ 9 =
      610000 * ((w + 2) ^ 2 * (W + 3) ^ 2 * (n + m + 2) ^ 9) := by ring
  have e' : 600000 * (w + 2) ^ 2 * (W + 3) ^ 2 * (n + m + 2) ^ 9 =
      600000 * ((w + 2) ^ 2 * (W + 3) ^ 2 * (n + m + 2) ^ 9) := by ring
  rw [e]
  rw [e'] at hP
  omega

end WeightedMIS.RegisterEdgeCostProgram
