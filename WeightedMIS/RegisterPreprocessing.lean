module

public import WeightedMIS.RegisterNetworkSolve
public import WeightedMIS.RegisterCutReadback
public import WeightedMIS.OriginalReduction

/-!
# The compiled maximum-flow preprocessing

Input: the vertex words `GraphReachEncoded.rangeWords W n`, the endpoint words of
the edges (`pair` cells, `GraphReachEncoded.edgeWords W left right`) and the
stored row of canonical rational weight words. The procedure

1. returns the empty class list at once when there are no vertices,
2. computes the scaled integral weights and the large capacity
   (`RegisterNetworkWeights`),
3. builds and solves the double-cover network (`RegisterNetworkSolve`),
4. reads the class of every vertex from the reached cut (`RegisterCutReadback`).

It returns the class words of `OriginalReduction.preprocessingPoint`, the final
residual table, the reached cut and the large capacity word. For at least one
vertex, the final residual table and cut represent
`MaxFlowPreprocessing.networkResult` of the truncated weights, for the endpoint
adjacency decided by `Incidence.endpointAdjDecidable`, as used by the actual
preprocessing.
-/

@[expose] public section

namespace WeightedMIS.RegisterPreprocessing

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.ResidualWords
open WeightedMIS.DoubleCoverNetwork WeightedMIS.MaxFlowPreprocessing
open WeightedMIS.GraphReachEncoded WeightedMIS.NetworkWords WeightedMIS.NetworkWeights
open WeightedMIS.RegisterAdjacencyScan WeightedMIS.RegisterCutReadback
open scoped BigOperators

structure Procedures (p : ℕ) where
  weights : RegisterNetworkWeights.Procedures p
  network : RegisterNetworkSolve.Procedures p
  readback : RegisterCutReadback.Procedures p
  self : Fin p

variable {p : ℕ}

/-- Arguments: vertex words, edges, weight row. Results: class words, final
residual table, reached cut, large capacity word. -/
def preprocessingBody (weights network readback : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.null, .null, .null, .null]
    cons := .call weights [.register 2] [5, 6, 7]
      (.call network [.register 0, .register 1, .register 5, .register 6, .register 7] [8, 9]
        (.call readback [.register 0, .register 9] [10]
          (.ret [.register 10, .register 8, .register 9, .register 6]))) }

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  d.weights.Matches code ∧ d.network.Matches code ∧ d.readback.Matches code ∧
  code d.self = preprocessingBody d.weights.self d.network.self d.readback.self

def budget (W w n m : ℕ) : ℕ :=
  RegisterNetworkWeights.budget w n + RegisterNetworkSolve.budget W (width w n) m n +
    RegisterCutReadback.budget W n (2 * n + 3) + 60

/-- The endpoint adjacency decision used by `OriginalReduction.preprocessingPoint`. -/
abbrev endpointAdj {n m : ℕ} (left right : Fin m → Fin n) :
    DecidableRel (EdgeTransport.Adj left right) :=
  Incidence.endpointAdjDecidable (leftV := left) (rightV := right)

theorem readback_budget_mono (W n a b : ℕ) (hab : a ≤ b) :
    RegisterCutReadback.budget W n a ≤ RegisterCutReadback.budget W n b := by
  unfold RegisterCutReadback.budget RegisterCutReadback.itemBudget RegisterMembership.budget
  have : (36 * (W + 2) + 60) * a ≤ (36 * (W + 2) + 60) * b := Nat.mul_le_mul_left _ hab
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_right
  omega

/-- Main theorem: the stored classes of all vertices agree with the actual
maximum-flow preprocessing point, and the final residual network is exported. -/
theorem preprocessing_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {W w n m : ℕ} (hn : n < 2 ^ W) (left right : Fin m → Fin n)
    (weights : Fin n → ℚ) (q : Fin n → BinaryRational.Word w)
    (hq : ∀ v, BinaryRational.Canonical (q v)) (hval : ∀ v, (q v).value = weights v)
    {h : Heap} (hh : Valid h) {vp ep wp : Ptr}
    (hv : WordsAt h vp (rangeWords W n)) (he : EdgeWordsAt h ep (edgeWords W left right))
    (hw : RegisterRationalRow.RowAt h wp ((List.finRange n).map q)) :
    ∃ out zp tablep cutp bigp, Extends h out ∧ Valid out ∧
      WordsAt out zp ((List.finRange n).map fun v =>
        classWord (OriginalReduction.preprocessingPoint (left := left) (right := right)
          weights (List.finRange n) v)) ∧
      (0 < n → ∃ words : ResidualListPhase.Result (W + 2) (width w n),
        TableAt out tablep words.table ∧ WordsAt out cutp words.seen ∧
        BitsAt out bigp (word (width w n) (big q)) ∧
        (letI := endpointAdj left right;
          ResidualPhaseRefinement.Represents (nodeWord W) (nodes n)
            (matrix (EdgeTransport.Adj left right) (mu q)) sourceNode sinkNode words
            (networkResult (EdgeTransport.Adj left right) (List.finRange n)
              (NegativeWeights.nonnegative weights))) ∧
        words.seen.length ≤ 2 * n + 3 ∧ words.table.length = (2 * n + 2) ^ 2) ∧
      Within code h (initialRegisters [.pointer vp, .pointer ep, .pointer wp]) (code d.self)
        [.pointer zp, .pointer tablep, .pointer cutp, .pointer bigp] out (budget W w n m) := by
  obtain ⟨hweights, hnetwork, hreadback, hself⟩ := hm
  have hwts : weightsOf q = weights := funext hval
  have htrunc : truncated q = NegativeWeights.nonnegative weights := by
    rw [truncated, hwts]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- no vertices
    have cell : h[vp]? = some .nil := by
      have : rangeWords W 0 = [] := rfl
      rw [this] at hv
      exact WordsAt.nil_iff.mp hv
    refine ⟨h, 0, 0, 0, 0, .refl h, hh, by simpa using (WordsAt.nil hh.1 : WordsAt h 0 ([] : List (Bits 2))),
      fun h0 => absurd h0 (by omega), ?_⟩
    let r0 := initialRegisters [Value.pointer vp, .pointer ep, .pointer wp]
    have last := Within.ret code h (loadRegisters r0 3 4 15 .nil) [.null, .null, .null, .null]
    have l := Within.load (regs := r0) (address := .register 0) (first := 3) (second := 4)
      (bit := 15) (branches := { CompiledTrie.failCases with
        nil := .ret [.null, .null, .null, .null]
        cons := .call d.weights.self [.register 2] [5, 6, 7]
          (.call d.network.self [.register 0, .register 1, .register 5, .register 6,
              .register 7] [8, 9]
            (.call d.readback.self [.register 0, .register 9] [10]
              (.ret [.register 10, .register 8, .register 9, .register 6]))) })
      (by simp [Atom.eval, r0, initialRegisters]) cell
      (by simpa [values, Atom.eval, Cases.select] using last)
    rw [hself]
    exact l.mono (by simp [budget])
  · -- at least one vertex
    have hwpos : 0 < w := width_pos_of_canonical (q ⟨0, hn0⟩) (hq ⟨0, hn0⟩)
    obtain ⟨x0, rest, cell0⟩ : ∃ x0 rest, h[vp]? = some (.cons x0 rest) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨ptrs, hl, hr⟩ := hv
      rw [rangeWords, List.finRange_succ, List.map_cons] at hr
      cases hr with
      | cons _ _ =>
        cases hl with
        | cons cell _ => exact ⟨_, _, cell⟩
    obtain ⟨h1, musp, bigp, zerop, e1, v1, hmus, hbig, hzero, weightsRun⟩ :=
      RegisterNetworkWeights.compiled code d.weights hweights q hq hn0 hh hw
    let _inst := endpointAdj left right
    have hB : 0 < width w n := by unfold width; positivity
    obtain ⟨h2, tablep, cutp, words, e2, v2, htab, hcut, hrep, hseenLen, htabLen, netRun⟩ :=
      RegisterNetworkSolve.compiled code d.network hnetwork hn hn0 hB left right (mu q)
        (big_lt q hq hwpos) v1 (hv.mono e1) (he.mono e1) hmus hbig hzero
    obtain ⟨-, caps, -, -, hseen⟩ := id hrep
    obtain ⟨h3, zp, e3, v3, hz, readRun⟩ := RegisterCutReadback.compiled code d.readback
      hreadback hn v2 _ hseen (hv.mono (e1.trans e2)) hcut
    have hpoint : ((List.finRange n).map fun v =>
        classWord (DoubleCover.rounded
          (leftCover (membership (MaxFlowScaling.solve (matrix (EdgeTransport.Adj left right)
            (mu q)) (nodes n) sourceNode sinkNode).cut))
          (rightCover (membership (MaxFlowScaling.solve (matrix (EdgeTransport.Adj left right)
            (mu q)) (nodes n) sourceNode sinkNode).cut)) v)) =
        (List.finRange n).map fun v =>
          classWord (OriginalReduction.preprocessingPoint (left := left) (right := right)
            weights (List.finRange n) v) := by
      unfold OriginalReduction.preprocessingPoint lpPoint networkResult mu
      rw [htrunc]
    rw [hpoint] at hz
    refine ⟨h3, zp, tablep, cutp, bigp, e1.trans (e2.trans e3), v3, hz, fun _ => ⟨words,
      htab.mono e3, hcut.mono e3, hbig.mono (e2.trans e3), ?_, hseenLen, htabLen⟩, ?_⟩
    · have hres : networkResult (EdgeTransport.Adj left right) (List.finRange n)
          (NegativeWeights.nonnegative weights) = MaxFlowScaling.solve
            (matrix (EdgeTransport.Adj left right) (mu q)) (nodes n) sourceNode sinkNode := by
        unfold networkResult mu
        rw [htrunc]
      rw [hres]
      exact hrep
    · have hread := readRun.mono (readback_budget_mono W n _ _ (by simpa using hseenLen))
      let r0 := initialRegisters [Value.pointer vp, .pointer ep, .pointer wp]
      let r1 := loadRegisters r0 3 4 15 (.cons x0 rest)
      let r2 := bindResults r1 [5, 6, 7] [.pointer musp, .pointer bigp, .pointer zerop]
      let r3 := bindResults r2 [8, 9] [.pointer tablep, .pointer cutp]
      let r4 := bindResults r3 [10] [.pointer zp]
      have last : Within code h3 r4 (.ret [.register 10, .register 8, .register 9, .register 6])
          [.pointer zp, .pointer tablep, .pointer cutp, .pointer bigp] h3 9 := by
        simpa [values, Atom.eval, r4, r3, r2, bindResults] using
          Within.ret code h3 r4 [.register 10, .register 8, .register 9, .register 6]
      have aR : values r3 [.register 0, .register 9] = [.pointer vp, .pointer cutp] := by
        simp [values, Atom.eval, r3, r2, r1, r0, bindResults, loadRegisters, decoded,
          initialRegisters]
      have cR := Within.call (procedure := d.readback.self) (regs := r3)
        (arguments := [.register 0, .register 9]) (results := [10])
        (by simpa only [aR] using hread) last
      have aN : values r2 [.register 0, .register 1, .register 5, .register 6, .register 7] =
          [.pointer vp, .pointer ep, .pointer musp, .pointer bigp, .pointer zerop] := by
        simp [values, Atom.eval, r2, r1, r0, bindResults, loadRegisters, decoded,
          initialRegisters]
      have cN := Within.call (procedure := d.network.self) (regs := r2)
        (arguments := [.register 0, .register 1, .register 5, .register 6, .register 7])
        (results := [8, 9]) (by simpa only [aN] using netRun) cR
      have aW : values r1 [.register 2] = [.pointer wp] := by
        simp [values, Atom.eval, r1, r0, loadRegisters, decoded, initialRegisters]
      have cW := Within.call (procedure := d.weights.self) (regs := r1)
        (arguments := [.register 2]) (results := [5, 6, 7])
        (by simpa only [aW] using weightsRun) cN
      have l := Within.load (regs := r0) (address := .register 0) (first := 3) (second := 4)
        (bit := 15) (branches := { CompiledTrie.failCases with
          nil := .ret [.null, .null, .null, .null]
          cons := .call d.weights.self [.register 2] [5, 6, 7]
            (.call d.network.self [.register 0, .register 1, .register 5, .register 6,
                .register 7] [8, 9]
              (.call d.readback.self [.register 0, .register 9] [10]
                (.ret [.register 10, .register 8, .register 9, .register 6]))) })
        (by simp [Atom.eval, r0, initialRegisters]) cell0 cW
      rw [hself]
      exact l.mono (by simp [budget]; omega)

/-- A clean polynomial bound on the event budget. -/
theorem budget_le (W w n m : ℕ) :
    budget W w n m ≤ 600000 * (w + 2) ^ 2 * (W + 3) ^ 2 * (n + m + 2) ^ 9 := by
  have hWb := RegisterNetworkWeights.budget_le w n
  have hSb := RegisterNetworkSolve.budget_le W (width w n) m n
  have hws := RegisterNetworkWeights.width_succ_le w n
  unfold budget
  generalize width w n = B at hWb hSb hws
  generalize hR : RegisterCutReadback.budget W n (2 * n + 3) = R
  have hRle : R ≤ 330 * (W + 3) * (n + m + 2) ^ 2 := by
    rw [← hR]
    unfold RegisterCutReadback.budget RegisterCutReadback.itemBudget RegisterMembership.budget
    nlinarith [Nat.zero_le (W * n * n), Nat.zero_le (W * n * m), Nat.zero_le (W * m * m),
      Nat.zero_le (n * m), Nat.zero_le (W * n), Nat.zero_le (W * m)]
  generalize ha : w + 2 = a at hws ⊢
  generalize hc : W + 3 = c at hRle ⊢
  generalize hT : n + m + 2 = T at hRle ⊢
  have ha1 : 1 ≤ a := by omega
  have hc1 : 1 ≤ c := by omega
  have hT1 : 1 ≤ T := by omega
  have haT : 1 ≤ a * T := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hcaT : 1 ≤ c * a * T := Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- the solver part
  have h1 : W + B + 3 ≤ 2 * (c * a * T) := by
    have hB : B + 1 ≤ a * T := le_trans hws (Nat.mul_le_mul_left a (by omega))
    have hBc : a * T ≤ c * a * T := by
      rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
    have hWc : W + 2 ≤ c * a * T := le_trans (by omega) (le_trans (Nat.le_mul_of_pos_right c
      (by omega : 0 < a * T)) (by rw [Nat.mul_assoc]))
    omega
  have h2 : (W + B + 3) ^ 2 ≤ 4 * (c * a * T) ^ 2 := by
    calc (W + B + 3) ^ 2 ≤ (2 * (c * a * T)) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 4 * (c * a * T) ^ 2 := by ring
  have h3 : (2 * n + 3) ^ 6 ≤ 64 * T ^ 6 := by
    calc (2 * n + 3) ^ 6 ≤ (2 * T) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      _ = 64 * T ^ 6 := by ring
  have h4 : m + 1 ≤ T := by omega
  have hS : 2000 * (W + B + 3) ^ 2 * (m + 1) * (2 * n + 3) ^ 6 ≤
      512000 * (c ^ 2 * a ^ 2 * T ^ 9) := by
    calc 2000 * (W + B + 3) ^ 2 * (m + 1) * (2 * n + 3) ^ 6
        ≤ 2000 * (4 * (c * a * T) ^ 2) * T * (64 * T ^ 6) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h4) h3
      _ = 512000 * (c ^ 2 * a ^ 2 * T ^ 9) := by ring
  -- the weights part
  have hT9 : T ^ 3 ≤ T ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hc2 : 1 ≤ c ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hW' : 1200 * (B + 1) ^ 2 * (n + 1) ≤ 1200 * (c ^ 2 * a ^ 2 * T ^ 9) := by
    have hB : B + 1 ≤ a * T := le_trans hws (Nat.mul_le_mul_left a (by omega))
    calc 1200 * (B + 1) ^ 2 * (n + 1) ≤ 1200 * (a * T) ^ 2 * T :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB 2)) (by omega)
      _ = 1200 * (1 * a ^ 2 * T ^ 3) := by ring
      _ ≤ 1200 * (c ^ 2 * a ^ 2 * T ^ 9) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_right _ hc2) hT9)
  -- the readback part
  have hR' : R ≤ 330 * (c ^ 2 * a ^ 2 * T ^ 9) := by
    have hcT : c * T ^ 2 ≤ c ^ 2 * a ^ 2 * T ^ 9 := by
      have e1 : c ≤ c ^ 2 := by nlinarith
      have e2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
      have e3 : T ^ 2 ≤ T ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
      calc c * T ^ 2 = c * 1 * T ^ 2 := by ring
        _ ≤ c ^ 2 * a ^ 2 * T ^ 9 := Nat.mul_le_mul (Nat.mul_le_mul e1 e2) e3
    calc R ≤ 330 * c * T ^ 2 := hRle
      _ = 330 * (c * T ^ 2) := by ring
      _ ≤ 330 * (c ^ 2 * a ^ 2 * T ^ 9) := Nat.mul_le_mul_left _ hcT
  have h60 : 60 ≤ 60 * (c ^ 2 * a ^ 2 * T ^ 9) := by
    have : 1 ≤ c ^ 2 * a ^ 2 * T ^ 9 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have e : 600000 * a ^ 2 * c ^ 2 * T ^ 9 = 600000 * (c ^ 2 * a ^ 2 * T ^ 9) := by ring
  rw [e]
  omega

end WeightedMIS.RegisterPreprocessing
