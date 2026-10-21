module

public import WeightedMIS.RegisterTopLevel
public import WeightedMIS.SpecMachine
public import WeightedMIS.SpecBridge

/-!
# Runs of the entry procedure on the encoded input

From the event bound of the entry procedure (`RegisterTopLevel.top_compiled`)
the operational statement follows: on the encoded input there is a framed
run, every framed run is that run (with the same call tree), its output
denotes `ExecutableMIS.solve R w`, and its stack bit cost is bounded by the
event budget through `FramedExec.bitCost_le_of_length_le`. For a drawing in
a closed-surface map, the bridge `Drawing.solve_spec` turns the output into a
maximum-weight independent set. The polynomial part of the event budget is
at most `2 ^ 36 · N ^ 11 · (L + 1) ^ 2` with `N = D.size` and `L` the weight
encoding length.
-/

@[expose] public section

namespace WeightedMIS.RegisterTopLevel

open WeightedMIS.Spec WeightedMIS.SpecEncoding
open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.RegisterComponentSolve (HardBudget HardSpec)
open WeightedMIS.RegisterWeightMask (CanonAt)
open WeightedMIS.RegisterFinalAssembly (residualHardSum)

variable {p : ℕ}

/-! ## Runs -/

/-- **Runs of the entry procedure.** There is exactly one framed run on the
encoded input; it outputs `ExecutableMIS.solve R w` and its stack bit cost is
at most `B · (102 + 35 · size (|heap| + B))` for the event budget `B`. -/
theorem top_runs (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    (hb : HardBudget) (D : Drawing) (w : Fin D.vertices → ℚ)
    (hard : HardSpec code ids.hard (indexWidth D) (CanonAt (weightWidth w)) hb)
    {R : EmbeddingFaces.Ribbon D.left D.right}
    (hR : ∀ y, R.corner y = Spec.Flag.equiv _ (D.corner ((Spec.Flag.equiv _).symm y))) :
    ∃ r₀ t₀, Runs code ids.top D w r₀ t₀ ∧
      ∀ r t, Runs code ids.top D w r t →
        r = r₀ ∧ t = t₀ ∧ Outputs D r (ExecutableMIS.solve R w) ∧
        stackBitCost t.compile ≤ (inputBudget D w + residualHardSum hb R w) *
          (102 + 35 * ((encode D w).1.length + (inputBudget D w + residualHardSum hb R w)).size) := by
  obtain ⟨out, q, -, -, hq, events, hex, hlen⟩ := top_compiled ids code hm hb D w hard hR
  obtain ⟨tree, ht⟩ := hex.framed
  refine ⟨_, tree, ht, fun r t hr => ?_⟩
  obtain ⟨rfl, rfl⟩ := FramedExec.deterministic hr ht
  exact ⟨rfl, rfl, outputs_of_setWords D rfl hq,
    ht.bitCost_le_of_length_le (encode_valid D w) (encode_registers_bounded D w) hlen⟩

/-- The binary size of the bit-cost bound, in closed form. -/
theorem cost_factor_le (D : Drawing) (w : Fin D.vertices → ℚ) (B : ℕ) :
    B * (102 + 35 * ((encode D w).1.length + B).size) ≤
      B * (102 + 35 * (100 * D.size ^ 2 * (weightLength w + 1) + B)) := by
  apply Nat.mul_le_mul_left
  have h1 : ((encode D w).1.length + B).size ≤ (encode D w).1.length + B :=
    Nat.size_le.mpr (Nat.lt_two_pow_self)
  have h2 := encode_length_le D w
  omega

/-- **The entry procedure in statement terms.** For a drawing in a
closed-surface map, with the internal ribbon `Drawing.ribbon hA W`: there is a
run on the encoded input, and every run returns a maximum-weight independent
set within the stated stack bit cost. -/
theorem top_correct (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    (hb : HardBudget) (A : Map) (hA : A.IsClosedSurface) (D : Drawing) (W : D.In A)
    (w : Fin D.vertices → ℚ)
    (hard : HardSpec code ids.hard (indexWidth D) (CanonAt (weightWidth w)) hb) :
    (∃ r t, Runs code ids.top D w r t) ∧
      ∀ r t, Runs code ids.top D w r t →
        (∃ I, Outputs D r I ∧ D.IsMaximum w I) ∧
        stackBitCost t.compile ≤
          (inputBudget D w + residualHardSum hb (Drawing.ribbon hA W) w) *
            (102 + 35 * (100 * D.size ^ 2 * (weightLength w + 1) +
              (inputBudget D w + residualHardSum hb (Drawing.ribbon hA W) w))) := by
  have hR : ∀ y, (Drawing.ribbon hA W).corner y =
      Spec.Flag.equiv _ (D.corner ((Spec.Flag.equiv _).symm y)) := by
    intro y
    have := Drawing.ribbon_corner hA W ((Spec.Flag.equiv _).symm y)
    rwa [Equiv.apply_symm_apply] at this
  obtain ⟨r₀, t₀, h0, hall⟩ := top_runs ids code hm hb D w hard hR
  refine ⟨⟨r₀, t₀, h0⟩, fun r t hr => ?_⟩
  obtain ⟨-, -, hout, hcost⟩ := hall r t hr
  exact ⟨⟨_, hout, (Drawing.solve_spec A hA D W w).1⟩, hcost.trans (cost_factor_le D w _)⟩

/-! ## The polynomial part of the budget -/

/-- A closed polynomial bound on the entry budget. -/
theorem topBudget_le {W w0 n m L : ℕ} (hW : W ≤ n + m) (hw : w0 ≤ L) :
    topBudget W w0 n m ≤ 2 ^ 36 * (n + m + 1) ^ 11 * (L + 1) ^ 2 := by
  have hp := RegisterPreprocessing.budget_le W w0 n m
  have ha := RegisterFinalAssembly.assemblyBudget_le W n m
  generalize hN : n + m + 1 = N at ha
  generalize hM : L + 1 = M
  have hN1 : 1 ≤ N := by omega
  have hM1 : 1 ≤ M := by omega
  have hX1 : N * M ≤ N ^ 11 * M ^ 2 :=
    Nat.mul_le_mul (by simpa using Nat.pow_le_pow_right hN1 (show 1 ≤ 11 by norm_num))
      (by simpa using Nat.pow_le_pow_right hM1 (show 1 ≤ 2 by norm_num))
  have hNM : N ≤ N * M := Nat.le_mul_of_pos_right _ (by omega)
  have hN5 : N ^ 5 ≤ N ^ 11 * M ^ 2 :=
    le_trans (Nat.pow_le_pow_right hN1 (by norm_num))
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
  -- preprocessing
  have hp' : RegisterPreprocessing.budget W w0 n m ≤ 11059200000 * (N ^ 11 * M ^ 2) := by
    refine hp.trans ?_
    have a1 : (w0 + 2) ^ 2 ≤ (2 * M) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have a2 : (W + 3) ^ 2 ≤ (3 * N) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have a3 : (n + m + 2) ^ 9 ≤ (2 * N) ^ 9 := Nat.pow_le_pow_left (by omega) 9
    calc 600000 * (w0 + 2) ^ 2 * (W + 3) ^ 2 * (n + m + 2) ^ 9
        ≤ 600000 * (2 * M) ^ 2 * (3 * N) ^ 2 * (2 * N) ^ 9 :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ a1) a2) a3
      _ = 11059200000 * (N ^ 11 * M ^ 2) := by ring
  -- assembly
  have ha' : RegisterFinalAssembly.assemblyBudget W n m ≤ 40000 * (N ^ 11 * M ^ 2) := by
    refine ha.trans ?_
    calc 40000 * (W + 1) * N ^ 4 ≤ 40000 * N * N ^ 4 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ = 40000 * N ^ 5 := by ring
      _ ≤ 40000 * (N ^ 11 * M ^ 2) := Nat.mul_le_mul_left _ hN5
  -- the linear procedures
  have hmask : RegisterWeightMask.maskBudget w0 n ≤ 105 * (N ^ 11 * M ^ 2) := by
    have : (19 * w0 + 73) * n ≤ 92 * (N * M) := by
      calc (19 * w0 + 73) * n ≤ (92 * M) * N := Nat.mul_le_mul (by omega) (by omega)
        _ = 92 * (N * M) := by ring
    simp only [RegisterWeightMask.maskBudget, RegisterWeightMask.testBudget,
      RegisterWeightMask.zeroTestBudget]
    have e : (19 * w0 + 13 + 30 + 30) * n = (19 * w0 + 73) * n := by ring
    omega
  have htrunc : RegisterWeightMask.truncBudget w0 n ≤ 155 * (N ^ 11 * M ^ 2) := by
    have : (40 * w0 + 102) * n ≤ 142 * (N * M) := by
      calc (40 * w0 + 102) * n ≤ (142 * M) * N := Nat.mul_le_mul (by omega) (by omega)
        _ = 142 * (N * M) := by ring
    simp only [RegisterWeightMask.truncBudget, RegisterWeightMask.truncItemBudget,
      RegisterWeightMask.zeroOneBudget]
    have e : (40 * w0 + 17 + 50 + 35) * n = (40 * w0 + 102) * n := by ring
    omega
  have hpairs : RegisterEdgePairs.pairsBudget m ≤ 108 * (N ^ 11 * M ^ 2) := by
    simp only [RegisterEdgePairs.pairsBudget]
    omega
  have e : 2 ^ 36 * N ^ 11 * M ^ 2 = 2 ^ 36 * (N ^ 11 * M ^ 2) := by ring
  simp only [topBudget]
  rw [e]
  omega

/-- The entry budget on the encoded input is at most
`2 ^ 36 · N ^ 11 · (L + 1) ^ 2`. -/
theorem inputBudget_le (D : Drawing) (w : Fin D.vertices → ℚ) :
    inputBudget D w ≤ 2 ^ 36 * D.size ^ 11 * (weightLength w + 1) ^ 2 :=
  topBudget_le (indexWidth_le D) (weightWidth_le w)

end WeightedMIS.RegisterTopLevel
